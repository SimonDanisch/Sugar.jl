"""
Method type, that you can lazily ask for all kind of information,
e.g. AST, lambdainfo, arguments, dependencies etc.
"""
type LazyMethod{T}
    signature
    cache
    decls::OrderedSet
    dependencies::OrderedSet{LazyMethod}
    li
    method
    ast::Expr
    source::String
    funcheader::String
    (::Type{LazyMethod{T}}){T}(signature, cache = Dict()) = new{T}(signature, cache, OrderedSet(), OrderedSet{LazyMethod}())
end

LazyMethod(signature) = LazyMethod{:JL}(signature)
LazyMethod(f::Function, types::Type) = LazyMethod{:JL}((f, types))

LazyMethod{T}(lm::LazyMethod{T}, f::Function, types) = LazyMethod{T}((f, Base.to_tuple_type(types)), lm.cache)


function isfunction(x::LazyMethod)
    isa(x.signature, Tuple) &&
    length(x.signature) == 2 &&
    (isa(x.signature[1], AllFuncs) || isa(x.signature[1], Type))
end
function istype(x::LazyMethod)
    isa(x.signature, DataType)
end
function getfunction(x::LazyMethod)
    isfunction(x) || error("$(x.signature) is not a function")
    x.signature[1]
end


isintrinsic(f::IntrinsicFuncs) = true
isintrinsic(f) = false

function isintrinsic(x::LazyMethod)
    isfunction(x) && isintrinsic(getfunction(x))
end
function Base.push!(decl::LazyMethod, x::LazyMethod)
    push!(decl.dependencies, x)
end
function Base.push!{T}(decl::LazyMethod{T}, signature)
    push!(decl.dependencies, LazyMethod{T}(signature, decl.cache))
end

import Base: ==
Base.hash(x::LazyMethod, h::UInt64) = hash(x.signature, h)
==(x::LazyMethod, y::LazyMethod) = x.signature == y.signature

function Base.show(io::IO, mt::MIME"text/plain", x::LazyMethod)
    show(io, mt, x.signature)
end

function getmethod!(x::LazyMethod)
    if !isdefined(x, :method)
        x.method = Sugar.get_method(x.signature...)
    end
    x.method
end
function getcodeinfo!(x::LazyMethod)
    if !isdefined(x, :li)
        x.li = Sugar.get_lambda(code_typed, x.signature...)
    end
    x.li
end

ssatypes(tp::LazyMethod) = getcodeinfo!(tp).ssavaluetypes
slottypes(tp::LazyMethod) = getcodeinfo!(tp).slottypes
slottype(tp::LazyMethod, s::Slot) = slottypes(tp)[s.id]
slottype(tp::LazyMethod, s::SSAValue) = ssatypes(tp)[s.id + 1]
function slotnames(tp::LazyMethod)
    map(enumerate(getcodeinfo!(tp).slotnames)) do iname
        i, name = iname
        if name == Symbol("#temp#")
            return Symbol(string("xxtempx", i)) # must be made unique
        end
        name
    end
end
function slotname(tp::LazyMethod, s::Slot)
    slotnames(tp)[s.id]
end
slotname(tp::LazyMethod, s::SSAValue) = Sugar.ssavalue_name(s)

if isdefined(Base, :LambdaInfo)
    returntype(x::LazyMethod) = getcodeinfo!(x).rettype
    function method_nargs(f::LazyMethod)
        li = getcodeinfo!(f)
        li.nargs
    end
    function type_ast(T)
        fields = Expr(:block)
        expr = Expr(:type, T.mutable, T, fields)
        for name in fieldnames(T)
            FT = fieldtype(T, name)
            push!(fields.args, :($name::$FT))
        end
        expr
    end
else
    returntype(x::LazyMethod) = Base.Core.Inference.return_type(x.signature...)
    function method_nargs(f::LazyMethod)
        m = getmethod!(f)
        m.nargs
    end
    function type_ast(T)
        fields = Expr(:block)
        mutable = T <: Tuple ? false : T.mutable
        expr = Expr(:struct, mutable, T, fields)
        for name in fieldnames(T)
            FT = fieldtype(T, name)
            push!(fields.args, :($name::$FT))
        end
        expr
    end
end


function getfuncargs(x::LazyMethod)
    sn, st = slotnames(x), Sugar.to_tuple(x.signature[2])
    n = method_nargs(x)
    map(2:n) do i
        expr = :($(sn[i])::$(st[i-1]))
        expr.typ = st[i-1]
        expr
    end
end

function getast!(x::LazyMethod)
    if !isdefined(x, :ast)
        ast = if isfunction(x)
            if isintrinsic(x)
                Expr(:block)
            else
                getcodeinfo!(x) # make sure codeinfo is present
                nargs = method_nargs(x)
                expr = Sugar.sugared(x.signature..., code_typed)
                st = slottypes(x)
                for (i, T) in enumerate(st)
                    slot = SlotNumber(i)
                    push!(x.decls, slot)
                    if i > nargs # if not defined in arguments, define in body
                        name = slotname(x, slot)
                        tmp = :($name::$T)
                        tmp.typ = T
                        unshift!(expr.args, tmp)
                    end
                end
                expr.typ = returntype(x)
                expr
            end
        else
            type_ast(x.signature)
        end
        x.ast = rewrite_ast(x, ast)
    end
    x.ast
end

function rewrite_function(li, f, types, expr)
    expr.args[1] = f
    expr
end
type_type{T}(x::Type{Type{T}}) = T
if isdefined(Base, :LambdaInfo)
    function get_static_parameters(lm::LazyMethod)
        to_tuple(getcodeinfo!(lm).sparam_vals)
    end
else
    function get_static_parameters(lm::LazyMethod)
        # TODO is this the correct way to get static parameters?! It seems to work at least
        world = typemax(UInt)
        x = first(Base._methods(lm.signature..., -1, world))
        to_tuple(x[2])
    end
end
function rewrite_ast(li, expr)
    sparams = get_static_parameters(li)
    if !isempty(sparams)
        expr = first(replace_expr(expr) do expr
            if isa(expr, Expr) && expr.head == :static_parameter
                true, sparams[expr.args[1]]
            else
                false, expr
            end
        end)
    end
    list = replace_expr(expr) do expr
        if isa(expr, NewvarNode)
            # slot = expr.slot
            # T = slottype(li, slot)
            # res = Expr(:(::), slotname(li, slot), T)
            # res.typ = T
            # seems like newvarnodes are redundant with the way we pre define
            # slots, so we can drop them here! # TODO is this true?
            return true, ()
        elseif isa(expr, QuoteNode)
            return true, expr.value
        elseif isa(expr, Expr)
            args, head = expr.args, expr.head
            if head == :(=)
                lhs = args[1]
                rhs = map(x-> rewrite_ast(li, x), args[2:end])
                res = similar_expr(expr, [lhs, rhs...])
                if !(lhs in li.decls)
                    push!(li.decls, lhs)
                    T = expr_type(li, lhs)
                    decl = Expr(:(::), lhs, T)
                    decl.typ = T
                    return true, (decl, res) # splice in declaration
                end
                return true, res
            elseif head == :call
                func = args[1]
                if func == GlobalRef(Core, :apply_type)
                    # TODO do something!!
                end
                types = (map(x-> expr_type(li, x), args[2:end])...)
                f = resolve_func(li, func)
                result = rewrite_function(li, f, types, similar_expr(expr, args))
                if isa(result, Expr)
                    map!(result.args, result.args) do x
                        rewrite_ast(li, x)
                    end
                end
                return true, result
            end
        end
        false, expr
    end
    first(list)
end

function ast_dependencies!(x, ast)
    MacroTools.prewalk(ast) do expr
        if isa(expr, Expr) && expr.head != :block && expr.head != :(=)
            if expr.head == :call
                f = expr.args[1]
                types = Tuple{map(arg-> Sugar.expr_type(x, arg), expr.args[2:end])...}
                push!(x, (f, types))
            else
                t = Sugar.expr_type(x, expr)
                # TODO this could hide problems, but there are some expr untyped which don't matter
                # but filtering would need more work!
                if isleaftype(t)
                    push!(x, t)
                else
                    warn("Found abstract type: $t in expr $expr")
                end
            end
        end
        expr
    end
end
function dependencies!{T}(x::LazyMethod{T}, recursive = false)
    # skip types with no dependencies (shouldn't actually even be in here)
    x.signature in (Module, DataType, Type) && return []
    if isfunction(x)
        ast_dependencies!(x, getast!(x))
        ast_dependencies!(x, Expr(:block, getfuncargs(x)...))
    else
        t = x.signature
        set = OrderedSet()
        for i in 1:nfields(t) # add all fields
            FT = fieldtype(t, i)
            dep = LazyMethod{T}(FT, x.cache)
            push!(set, dep)
        end
        union!(x.dependencies, set)
    end
    if recursive # we don't add them to x!!
        deps = x.dependencies
        return union(deps, _dependencies!(copy(deps), LazyMethod{T}(Void, x.cache)))
    end
    x.dependencies
end

function _dependencies!{T}(dep::LazyMethod{T}, visited = LazyMethod{T}(Void))
    if dep in visited.dependencies
        # when already in deps we need to move it up!
        delete!(visited.dependencies, dep)
        push!(visited.dependencies, dep)
    else
        push!(visited, dep)
        if !isintrinsic(dep)
            _dependencies!(dependencies!(dep), visited)
        end
    end
    visited.dependencies
end
function _dependencies!(deps, visited)
    for dep in copy(deps)
        if !Sugar.isintrinsic(dep)
            _dependencies!(dep, visited)
        end
    end
    visited.dependencies
end

function getfuncheader!(x::LazyMethod)
    if !isdefined(x, :funcheader)
        x.funcheader = if isfunction(x)
            sprint() do io
                args = getfuncargs(x)
                show_function(io, x.signature...)
                Base.show_enclosed_list(io, '(', args, ", ", ')', 0, 0)
                print(io, "::", returntype(x))
            end
        else
            ""
        end
    end
    x.funcheader
end

function getfuncsource(x::LazyMethod)
    try
        ast, str = get_source(getmethod!(x))
        str
    catch e
        sprint() do io
            Base.show_unquoted(io, getast!(x), 0, 0)
        end
    end
end

function gettypesource(x::LazyMethod)
    sprint() do io
        dump(io, x.signature)
    end
end

function getbodysource!(x::LazyMethod)
    if istype(x)
        gettypesource(x)
    else
        getfuncsource(x)
    end
end

function getsource!(x::LazyMethod)
    if !isdefined(x, :source)
        str = getbodysource!(x)
        if isfunction(x)
            str = getfuncheader!(x) * "\n" * str
        end
        x.source = str
    end
    x.source
end

"""
Type of an expression in the context of a LazyMethod
"""
function expr_type(lm::LazyMethod, x)
    _expr_type(lm, x)
end
_expr_type(lm, x::Expr) = x.typ
_expr_type(lm, x::TypedSlot) = x.typ
_expr_type(lm, x::GlobalRef) = typeof(eval(x))
_expr_type{T}(lm, x::Type{T}) = Type{T}
_expr_type{T}(lm, x::T) = T
_expr_type(lm, slot::Union{Slot, SSAValue}) = slottype(lm, slot)

instance(x) = x.instance
extract_type{T}(x::Type{T}) = T

"""
Takes any value found in the context of a LazyMethod and returns
A concrete function!
"""
resolve_func(li, f::AllFuncs) = f
resolve_func{T}(li, ::Type{T}) = T
resolve_func(li, f::Union{GlobalRef, Symbol}) = eval(f)
function resolve_func(li, slot::Slot)
    try
        instance(expr_type(li, slot))
    catch e
        println(slot)
        println(slotname(li, slot))
        rethrow(e)
    end
end
function resolve_func(li, f::Expr)
    if f.typ <: Type
        return extract_type(f.typ)
    end
    if f.typ <: AllFuncs
        return instance(f.typ)
    end
    try
        # TODO figure out what can go wrong here, since this seems rather fragile
        return eval(f)
    catch e
        println("Couldn't resolve $f")
        rethrow(e)
    end
    error("$f not a callable")
end
"""
Like @code_typed, but will create a lazymethod!
"""
macro lazymethod(ex0)
    :($(Base.gen_call_with_extracted_types(:LazyMethod, ex0)))
end

# interface for transpilers
function typename end
function _typename end
function functionname end
function show_name end
function show_type end
function show_function end

function supports_overloading end
function vecname end

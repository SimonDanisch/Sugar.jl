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
    LazyMethod(signature, cache = Dict()) = new{T}(signature, cache, OrderedSet(), OrderedSet{LazyMethod}())
end

LazyMethod(signature) = LazyMethod{:JL}(signature)
LazyMethod(f::Function, types::Type) = LazyMethod{:JL}((f, types))

const AllFuncs = Union{Function, Core.Builtin, Core.IntrinsicFunction}
const IntrinsicFuncs = Union{Core.Builtin, Core.IntrinsicFunction}

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
function getmethod(x::LazyMethod)
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

function returntype(x::LazyMethod)
    getcodeinfo!(x).rettype
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
if VERSION < v"0.6.0-dev"
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
    function method_nargs(f::LazyMethod)
        m = getmethod(f)
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
    sn, st = slotnames(x), slottypes(x)
    n = method_nargs(x)
    map(2:n) do i
        :($(sn[i])::$(st[i]))
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
                expr
            end
        else
            type_ast(x.signature)
        end
        x.ast = rewrite_ast(x, ast)
    end
    x.ast
end

rewrite_function(li, f, types, expr) = expr

function rewrite_ast(li, expr)
    if VERSION < v"0.6.0-dev"
        sparams = (Sugar.getcodeinfo!(li).sparam_vals...,)
        if !isempty(sparams)
            expr = first(Sugar.replace_expr(expr) do expr
                if isa(expr, Expr) && expr.head == :static_parameter
                    true, sparams[expr.args[1]]
                else
                    false, expr
                end
            end)
        end
    end
    list = Sugar.replace_expr(expr) do expr
        if isa(expr, QuoteNode)
            true, expr.value
        elseif isa(expr, Expr)
            args, head = expr.args, expr.head
            if head == :(=)
                lhs = args[1]
                rhs = map(x-> rewrite_ast(li, x), args[2:end])
                res = similar_expr(expr, [lhs, rhs...])
                if !(lhs in li.decls)
                    push!(li.decls, lhs)
                    decl = Expr(:(::), lhs, expr_type(li, lhs))
                    return true, (decl, res) # splice in declaration
                end
                return true, res
            elseif head == :call
                func = args[1]
                if func == GlobalRef(Core, :apply_type)
                    # TODO do something!!
                end
                types = Tuple{map(x-> expr_type(li, x), args[2:end])...}
                f = resolve_func(li, func)
                result = rewrite_function(li, f, types, similar_expr(expr, args))
                map!(result.args, result.args) do x
                    rewrite_ast(li, x)
                end
                return true, result
            end
        end
        false, expr
    end
    first(list)
end


function dependencies!{T}(x::LazyMethod{T}, recursive = false)
    if x.signature in (Module, DataType, Type)
        return []
    end
    if isfunction(x)
        MacroTools.prewalk(getast!(x)) do expr
            if isa(expr, Expr) && expr.head != :block && expr.head != :(=)
                if expr.head == :call
                    f = expr.args[1]
                    types = Tuple{map(arg-> Sugar.expr_type(x, arg), expr.args[2:end])...}
                    push!(x, (f, types))
                else
                    t = Sugar.expr_type(x, expr)
                    # TODO this could hide problems, but there are some expr untyped which don't matter
                    # but filtering would need more work!
                    if t != Any
                        push!(x, t)
                    end
                end
            end
            expr
        end
    else
        t = x.signature
        for i in 1:nfields(t)
            FT = fieldtype(t, i)
            dep = LazyMethod{T}(FT)
            if !(dep in x.dependencies)
                push!(x, dep)
                union!(x.dependencies, dependencies!(dep))
            end
        end
    end
    if recursive # we don't add them to x!!
        deps = x.dependencies
        return union(deps, _dependencies!(copy(deps), LazyMethod{T}(Void)))
    end
    x.dependencies
end

function _dependencies!{T}(dep::LazyMethod{T}, visited = LazyMethod{T}(Void), stack = [])
    if dep in visited.dependencies
        # when already in deps we need to move it up!
        delete!(visited.dependencies, dep)
        push!(visited.dependencies, dep)
    else
        push!(visited, dep)
        try
            push!(stack, dep.signature)
            _dependencies!(dependencies!(dep), visited)
        catch e
            for elem in stack
                println("  ", elem)
            end
        finally
            pop!(stack)
        end
    end
    visited.dependencies
end
function _dependencies!(deps, visited, stack = [])
    for dep in copy(deps)
        if !Sugar.isintrinsic(dep)
            push!(stack, dep.signature)
            _dependencies!(dep, visited)
            pop!(stack)
        end
    end
    visited.dependencies
end



function getfuncheader!(x::LazyMethod)
    if !isdefined(x, :funcheader)
        x.funcheader = if isfunction(x)
            sprint() do io
                args = getfuncargs(x)
                print(io, x.signature[1])
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
_expr_type(lm, x::TypedSlot) = x.type
_expr_type(lm, x::GlobalRef) = typeof(eval(x))
_expr_type{T}(lm, x::T) = T
_expr_type(lm, slot::Union{Slot, SSAValue}) = slottype(lm, slot)


"""
Takes any value found in the context of a LazyMethod and returns
A concrete function!
"""
resolve_func(li, f::AllFuncs) = f
resolve_func{T}(li, ::Type{T}) = T
resolve_func(li, f::Union{GlobalRef, Symbol}) = eval(f)
instance(x) = x.instance
function resolve_func(li, slot::Slot)
    instance(expr_type(li, slot))
end
extract_type{T}(x::Type{T}) = T
function resolve_func(li, f::Expr)
    if f.typ <: Type
        return extract_type(f.typ)
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

macro lazymethod(ex0)
    :($(Base.gen_call_with_extracted_types(:LazyMethod, ex0)))
end

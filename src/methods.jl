"""
Method type, that you can lazily ask for all kind of information,
e.g. AST, lambdainfo, arguments, dependencies etc.
"""
type LazyMethod
    signature
    cache
    decls::OrderedSet
    dependencies::OrderedSet{LazyMethod}
    li
    method
    ast::Expr
    source::String
    funcheader::String
    LazyMethod(signature, cache = Dict()) = new(signature, cache, OrderedSet(), OrderedSet{LazyMethod}())
end
LazyMethod(f::Function, types::Type) = LazyMethod((f, types))
const Funzies = Union{Function, Core.Builtin, Core.IntrinsicFunction}
function isfunction(x::LazyMethod)
    isa(x.signature, Tuple) && length(x.signature) == 2 && isa(x.signature[1], Funzies)
end
function istype(x::LazyMethod)
    isa(x.signature, DataType)
end
function getfunction(x::LazyMethod)
    isfunction(x) || error("$(x.signature) is not a function")
    x.signature[1]
end


isintrinsic(f::Union{Core.Builtin, Core.IntrinsicFunction}) = true
isintrinsic(f) = false
function isintrinsic(x::LazyMethod)
    isfunction(x) && isintrinsic(getfunction(x))
end
function Base.push!(decl::LazyMethod, x::LazyMethod)
    push!(decl.dependencies, x)
end
function Base.push!(decl::LazyMethod, signature)
    push!(decl.dependencies, LazyMethod(signature, decl.cache))
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
if v"0.6" < VERSION
    function method_nargs(f::LazyMethod)
        m = getmethod(f)
        m.nargs
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
        li = getcodeinfo!(f)
        li.nargs
    end
    function type_ast(T)
        fields = Expr(:block)
        expr = Expr(:struct, T.mutable, T, fields)
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
                        unshift!(expr.args, :($name::$T))
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
    if VERSION < v"0.6.0"
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
        if isa(expr, Slot)
            expr_type(li, expr) # add as dependency
            return true, expr
        elseif isa(expr, QuoteNode)
            true, expr.value
        elseif isa(expr, Expr)
            args, head = expr.args, expr.head
            if head == :(=)
                lhs = args[1]
                name = slotname(li, lhs)
                rhs = map(x-> rewrite_ast(li, x), args[2:end])
                res = similar_expr(expr, [lhs, rhs...])
                if !(lhs in li.decls)
                    push!(li.decls, lhs)
                    decl = Expr(:(::), name, expr_type(li, lhs))
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
                push!(li, (f, types))
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


function dependencies!(x::LazyMethod)
    if x.signature == Module
        return []
    end
    if isfunction(x)
        ast = getast!(x) # make sure it walks the ast, which adds the dependencies
    else
        T = x.signature
        for i in 1:nfields(T)
            FT = fieldtype(T, i)
            dep = LazyMethod(FT)
            if !(dep in x.dependencies)
                push!(x, dep)
                union!(x.dependencies, dependencies!(dep))
            end
        end
    end
    x.dependencies
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

function getbodysource!(x::LazyMethod)
    try
        ast, str = get_source(getmethod!(x))
        str
    catch e
        sprint() do io
            Base.show_unquoted(io, getast!(x), 0, 0)
        end
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
    t = _expr_type(lm, x)
    # TODO adding dependencies here seems like a bad mix of abstractions!
    if !isa(t, Module)
        push!(lm, t) # add as dependency
    end
    t
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
resolve_func{T}(li, ::Type{T}) = T
resolve_func(li, f::Union{GlobalRef, Symbol}) = eval(f)
instance(x) = x.instance
function resolve_func(li, slot::Slot)
    instance(expr_type(li, slot))
end
function resolve_func(li, f::Expr)
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

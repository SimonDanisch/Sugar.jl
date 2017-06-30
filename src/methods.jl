"""
Method type, that you can lazily ask for all kind of information,
e.g. AST, lambdainfo, arguments, dependencies etc.
"""
type LazyMethod{T}
    signature
    cache
    decls::OrderedSet
    dependencies::OrderedSet{LazyMethod}
    parent
    codeinfo
    method
    ast::Expr
    source::String
    funcheader::String
    slots::Vector{Tuple{DataType, Symbol}}
    function (::Type{LazyMethod{T}}){T}(
            signature, parent = nothing,
            cache = Dict()
        )
        if parent == nothing
            new{T}(signature, cache, OrderedSet(), OrderedSet{LazyMethod}())
        else
            obj = new{T}(signature, cache, OrderedSet(), OrderedSet{LazyMethod}(), parent)
            push!(parent.dependencies, obj)
            obj
        end
    end
end

LazyMethod{T}(lm::LazyMethod{T}, f::Function, types) = LazyMethod{T}((f, Base.to_tuple_type(types)), lm, lm.cache)
LazyMethod{T}(lm::LazyMethod{T}, t::DataType) = LazyMethod{T}(t, lm, lm.cache)


LazyMethod(signature::DataType) = LazyMethod{:JL}(signature)
LazyMethod(f::AllFuncs, types) = LazyMethod{:JL}((f, Base.to_tuple_type(types)))


function isfunction(x::LazyMethod)
    isa(x.signature, Tuple) &&
    length(x.signature) == 2 &&
    (isa(x.signature[1], AllFuncs) || isa(x.signature[1], Type))
end

istype(x::LazyMethod) = isa(x.signature, DataType)

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
    push!(decl.dependencies, LazyMethod{T}(decl, signature))
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
    if !isdefined(x, :codeinfo)
        x.codeinfo = Sugar.get_lambda(code_typed, x.signature...)
    end
    x.codeinfo
end

function newslot!(m, T, name = gensym())
    push!(m.slots, (T, name))
    TypedSlot(length(m.slots), T)
end

ssatypes(m::LazyMethod) = getcodeinfo!(m).ssavaluetypes

function getslots!(m::LazyMethod)
    if !isdefined(m, :slots)
        ci = getcodeinfo!(m)
        slots = Tuple{DataType, Symbol}[]
        for (i, (T, name)) in enumerate(zip(ci.slottypes, ci.slotnames))
            # tmp must be made unique
            # TODO check if this is just because I mess up scope!
            if name == Symbol("#temp#")
                name = Symbol("xxtempx", i)
            end
            push!(slots, (T, name))
        end
        m.slots = slots
    end
    m.slots
end

slottypes(m::LazyMethod) = map(first, getslots!(m))
slotnames(m::LazyMethod) = map(last, getslots!(m))

slottype(m::LazyMethod, s::TypedSlot) = s.typ
slottype(m::LazyMethod, s::Slot) = first(getslots!(m)[s.id])

slottype(m::LazyMethod, s::SSAValue) = ssatypes(m)[s.id + 1]

slotname(tp::LazyMethod, s::SSAValue) = Sugar.ssavalue_name(s)
function slotname(m::LazyMethod, s::Slot)
    slots = getslots!(m)
    if s.id <= length(slots)
        last(slots[s.id])
    else
        # TODO check in what situation this turns up, and if it should be fixed earlier in the pipeline
        Symbol("slot_$(s.id)")
    end
end

if isdefined(Base, :LambdaInfo)
    returntype(x::LazyMethod) = getcodeinfo!(x).rettype
    function method_nargs(f::LazyMethod)
        codeinfo = getcodeinfo!(f)
        codeinfo.nargs
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
        method = getmethod!(f)
        method.nargs
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


function has_varargs(x::LazyMethod)
    n = method_nargs(x)
    calltypes, real_signature = to_tuple(x.signature[2]), slottypes(x)[2:end]
    if calltypes == real_signature
        return false, n - 1
    else
        l1, l2 = last(calltypes), last(real_signature)
        return l1 != l2 && l2 <: Tuple, n - 1
    end
end

function getfuncargs(x::LazyMethod)
    calltypes, slots = to_tuple(x.signature[2]), getslots!(x)
    n = method_nargs(x)
    map(2:n) do i
        name, T = slots[i]
        calltype = calltypes[i]
        # Slot types might be less specific, e.g. when the variable is unused it might end up as Any.
        # but generally the slot type is the correct one, especially in the context of varargs.
        argtype = isleaftype(T) ? T : calltype
        expr = :($(name)::$(argtype))
        expr.typ = argtype
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

function rewrite_function(m, f, types, expr)
    expr.args[1] = f
    expr
end

"""
A node to inline expressions into the AST
"""
immutable InlineNode
    deps::Vector
    expression::Expr
end


"""
Unrole `Core._apply`
"""
function rewrite_apply(m, types, expr)
    orig_expr = expr
    apply_args = expr.args[2:end]
    if types[1] <: AllFuncs && all(x-> x <: Tuple, types[2:end])
        to_apply = instance(types[1])
        argtuple = apply_args[2:end]
        tuple_len = length(argtuple)
        # assign to tmp, in case it's  not a variable and instead a constructor expression
        tmp_exprs = []; args = []
        for i = 1:tuple_len
            arg_expr = argtuple[i]
            T = types[i + 1]
            # Unrole tuple expressions directly without first creating it!
            if isa(arg_expr, Expr) && arg_expr.head == :call && arg_expr.args[1] == GlobalRef(Core, :tuple)
                tupelems = map(x-> rewrite_ast(m, x), arg_expr.args[2:end])
                append!(args, tupelems)
                continue
            end
            arg = rewrite_ast(m, arg_expr)
            sym = newslot!(m, T, gensym("_apply_tmp"))
            push!(tmp_exprs, Expr(:(::), sym, T))
            push!(tmp_exprs, :($sym = $arg))
            ttup = to_tuple(T)
            tuplen = length(ttup)
            for j = 1:tuplen
                expr = Expr(:call, getindex, sym, j)
                expr.typ = ttup[j]
                expr = rewrite_function(m, getindex, (T, Int), copy(expr))
                push!(args, expr)
            end
        end
        expr = typed_expr(orig_expr.typ, :call, to_apply, args...)
        types = map(x-> expr_type(m, x), args)
        expr = rewrite_function(m, to_apply, types, copy(expr))
        InlineNode(tmp_exprs, expr)
    else
        error("Unknown _apply construct. Found: $expr")
    end
end

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

function rewrite_quotenode(m::LazyMethod, node)
    node.value
end

function rewrite_ast(m, expr)
    sparams = get_static_parameters(m)
    if !isempty(sparams)
        # needs to be done in a first pass for now, since the next step relies on
        # all static params being resolved!s
        expr = first(replace_expr(expr) do expr
            if isa(expr, Expr) && expr.head == :static_parameter
                true, sparams[expr.args[1]]
            else
                false, expr
            end
        end)
    end
    list = replace_expr(expr) do expr
        if isa(expr, SlotNumber)
            # lets make things simple and always use typed slots
            return true, TypedSlot(expr.id, expr_type(m, expr))
        elseif isa(expr, NewvarNode)
            # seems like newvarnodes are redundant with the way we pre define
            # slots, so we can drop them here! # TODO is this true?
            return true, ()
        elseif isa(expr, QuoteNode)
            return true, rewrite_quotenode(m, expr)
        elseif isa(expr, Expr)
            args, head = expr.args, expr.head
            if head == :(=)
                lhs = args[1]
                rhs = map(x-> rewrite_ast(m, x), args[2:end])
                res = similar_expr(expr, [lhs, rhs...])
                if !(lhs in m.decls) # if not already declared
                    # DECLARE IT!
                    push!(m.decls, lhs)
                    T = expr_type(m, lhs)
                    decl = Expr(:(::), lhs, T)
                    decl.typ = T
                    return true, (decl, res) # splice in declaration
                end
                return true, res
            elseif head == :call
                func = args[1]
                types = (map(x-> expr_type(m, x), args[2:end])...)
                f = resolve_func(m, func)
                if f == Core._apply
                    return true, rewrite_apply(m, types, expr)
                end
                lm = LazyMethod(m, f, types)
                has_a_serious_case_of_the_varargs, n = has_varargs(lm)
                if has_a_serious_case_of_the_varargs
                    tup_expr = Expr(:call, tuple)
                    for i in (n + 1):length(args)
                        push!(tup_expr.args, args[i])
                    end
                    tupt = Tuple{types[n:length(types)]...}
                    tup_expr.typ = tupt
                    types = (types[1:(n-1)]..., tupt)
                    args = [args[1:n]..., tup_expr]
                end
                args[1] = lm
                result = rewrite_function(lm, similar_expr(expr, args))
                if isa(result, Expr)
                    map!(result.args, result.args) do x
                        rewrite_ast(m, x)
                    end
                end
                return true, result
            end
        end
        false, expr
    end
    remove_inlinenodes(first(list))
end


remove_inlinenodes(node, insertion = []) = node

function remove_inlinenodes(node::InlineNode, insertion)
    splice!(insertion[1], insertion[2], node.deps)
    node.expression
end

function remove_inlinenodes(expr::Expr, insertion = (expr.args, 1))
    new_expr = similar_expr(expr)
    if expr.head == :block
        insert_list = new_expr.args # save last point where we can savely insert expressions
        for (i, elem) in enumerate(expr.args)
            res = remove_inlinenodes(elem, (insert_list, (i:(i - 1))))
            push!(insert_list, res)
        end
    else
        new_expr.args = map(expr.args) do elem
            remove_inlinenodes(elem, insertion)
        end
    end
    new_expr
end


function ast_dependencies!(x, ast)
    MacroTools.prewalk(ast) do expr
        if isa(expr, Expr) && expr.head != :block && expr.head != :(=)
            if expr.head == :call
                f = expr.args[1]
                type_arr = map(arg-> Sugar.expr_type(x, arg), expr.args[2:end])
                types = Tuple{type_arr...}
                for elem in type_arr
                    push!(x, elem)
                end
                isa(f, Type) && push!(x, f)
                push!(x, (f, types))
            else
                t = Sugar.expr_type(x, expr)
                # TODO this could hide problems, but there are some expr untyped which don't matter
                # but filtering would need more work!
                if isleaftype(t)
                    push!(x, t)
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
        if !isintrinsic(x)
            ast_dependencies!(x, getast!(x))
            ast_dependencies!(x, Expr(:block, getfuncargs(x)...))
        end
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

instance{F <: Function}(x::Type{F}) = F.instance
instance{T}(x::Type{T}) = x

extract_type{T}(x::Type{T}) = T

"""
Takes any value found in the context of a LazyMethod and returns
A concrete function!
"""
resolve_func(m, f::AllFuncs) = f
resolve_func{T}(m, X::Type{T}) = X
resolve_func(m, f::Union{GlobalRef, Symbol}) = eval(f)
function resolve_func(m, slot::Union{Slot, SSAValue})
    try
        instance(expr_type(m, slot))
    catch e
        println(expr_type(m, slot))
        println(slotname(m, slot))
        rethrow(e)
    end
end
function resolve_func(m, f::Expr)
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

function replace_slots(m::LazyMethod, ast)
    first(Sugar.replace_expr(ast) do expr
        if isa(expr, Slot) || isa(expr, SSAValue)
            return true, slotname(m, expr)
        elseif isa(expr, NewvarNode)
            return true, :(local $(slotname(m, expr.slot)))
        else
            return false, expr
        end
    end)
end

function get_func_expr(m::LazyMethod, name = Symbol(getfunction(m)))
    expr = sugared(m.signature..., code_lowered)
    get_func_expr(m, expr, name)
end

function get_func_expr(m::LazyMethod, expr::Expr, name = Symbol(getfunction(m)))
    body = replace_slots(m, expr)
    args = getfuncargs(m)
    Expr(:function,
        Expr(:call, name, args...),
        body
    )
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

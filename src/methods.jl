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
            #push!(parent.dependencies, obj)
            obj
        end
    end
end

LazyMethod{T}(lm::LazyMethod{T}, f, types) = LazyMethod{T}((f, Base.to_tuple_type(types)), lm, lm.cache)
LazyMethod{T}(lm::LazyMethod{T}, t) = LazyMethod{T}(t, lm, lm.cache)


LazyMethod(signature::DataType) = LazyMethod{:JL}(signature)
LazyMethod(f, types) = LazyMethod{:JL}((f, Base.to_tuple_type(types)))

"""
Like @code_typed, but will create a lazymethod!
"""
macro lazymethod(ex0)
    :($(InteractiveUtils.gen_call_with_extracted_types(Base, :LazyMethod, ex0)))
end




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
is_native_type(x::LazyMethod, T) = false
isintrinsic(x::LazyMethod, f, typ) = isintrinsic(f)
function isintrinsic(x::LazyMethod)
    if isfunction(x)
        isintrinsic(x, x.signature...)
    else
        is_native_type(x, x.signature)
    end
end

function Base.push!(decl::LazyMethod, x::LazyMethod)
    push!(decl.dependencies, x)
end
function Base.push!{T, T2}(decl::LazyMethod{T}, signature::T2)
    push!(decl.dependencies, LazyMethod(decl, signature))
end

# Make Dicts/Set work correctly
import Base: ==
Base.hash(x::LazyMethod, h::UInt64) = hash(x.signature, h)
==(x::LazyMethod, y::LazyMethod) = x.signature == y.signature

Base.show(io::IO, x::LazyMethod) = show(io, MIME"text/plain"(), x)
function Base.show(io::IO, mt::MIME"text/plain", x::LazyMethod)
    if isfunction(x)
        print(io, x.signature[1], '(', join(to_tuple(x.signature[2]), ", "), ')')
    else
        show(io, mt, x.signature)
    end
end


function Base.show_unquoted(io::IO, x::LazyMethod, ::Int, ::Int)
    if isfunction(x)
        print(io, functionname(io, x))
    else
        print(io, typename(io, x.signature))
    end
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
    slot = (T, name)
    idx = findfirst(m.slots, slot)
    if idx > 0
        # means we already have a slot with this name + type, which we can use.
        # This needs to be treated with care, since it might also be a clash.
        return TypedSlot(idx, T)
    else
        push!(m.slots, (T, name))
        return TypedSlot(length(m.slots), T)
    end
end

ssatypes(m::LazyMethod) = getcodeinfo!(m).ssavaluetypes

function getslots!(m::LazyMethod)
    if !isdefined(m, :slots)
        slotnames = Dict{Symbol, Int}()
        ci = getcodeinfo!(m)
        slots = Tuple{DataType, Symbol}[]
        for (i, (T, name)) in enumerate(zip(ci.slottypes, ci.slotnames))
            unique_name = if haskey(slotnames, name)
                id = slotnames[name] += 1
                Symbol("$(name)$(id)")
            else
                slotnames[name] = 0
                name
            end
            push!(slots, (T, unique_name))
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
function slotname(tp::LazyMethod, ssa::SSAValue)
    Symbol(string("_ssavalue_", ssa.id))
end

function slotname(m::LazyMethod, s::Slot)
    slots = getslots!(m)
    id = s.id
    if id <= length(slots)
        last(slots[id])
    else
        # TODO check in what situation this turns up, and if it should be fixed earlier in the pipeline
        Symbol("slot_$(s.id)")
    end
end

function returntype(x::LazyMethod)
    if isclosure(x.signature[1])
        # TODO isn't there an easier way?!
        ftype = x.signature[1]
        world = typemax(UInt)
        tt = Tuple{ftype, to_tuple(x.signature[2])...}
        (ti, env, meth) = Base._methods_by_ftype(tt, 1, world)[1]
        meth = Base.func_for_method_checked(meth, tt)
        params = Core.Inference.InferenceParams(world)
        (_, code, ty) = Core.Inference.typeinf_code(meth, ti, env, false, false, params)
        ty
    else
        Base.Core.Inference.return_type(x.signature...)
    end
end

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


function has_varargs(x::LazyMethod)
    # we can't introspect intrinsics, for all I know
    isintrinsic(x) && return false, 0

    n = method_nargs(x)
    calltypes, real_signature = to_tuple(x.signature[2]), to_tuple(slottypes(x)[2:(n)])
    if calltypes == real_signature
        return false, n
    else
        # vararg must be at the end of argument list an will not match call type
        # will be a tuple in the type of the actual method.
        # Note, that all typeinf methods (code_typed etc), will still want the actual
        # call types though
        l1, l2 = last(calltypes), last(real_signature)
        return l1 != l2 && l2 <: Tuple, n
    end
end

function getfuncargs(x::LazyMethod)
    functype = x.signature[1]
    calltypes, slots = to_tuple(x.signature[2]), getslots!(x)
    n = method_nargs(x)
    args = map(2:n) do i
        argtype, name = slots[i]
        # Slot types might be less specific, e.g. when the variable is unused it might end up as Any.
        # but generally the slot type is the correct one, especially in the context of varargs.
        calltype = if !isleaftype(argtype) && length(calltypes) <= i
            argtype = calltypes[i - 1]
        end
        expr = :($(name)::$(argtype))
        expr.typ = argtype
        expr
    end
    args
end

"""
OpenCL needs to decompose structs containing device pointers, since they can't be inlined into structs.
"""
needs_decompose(x, T) = false

function getast!(x::LazyMethod)
    if !isdefined(x, :ast)
        ast = if isfunction(x)
            if isintrinsic(x)
                Expr(:block)
            else
                getcodeinfo!(x) # make sure codeinfo is present
                nargs = method_nargs(x)
                expr = sugared(x.signature..., code_typed)
                st = getslots!(x)
                for (i, (T, name)) in enumerate(st)
                    slot = TypedSlot(i, T)
                    push!(x.decls, slot)
                    push!(x, T)
                    if i > nargs # if not defined in arguments, define in body
                        tmp = :($name::$T)
                        tmp.typ = T
                        unshift!(expr.args, tmp)
                    end
                end
                expr.typ = returntype(x)
                args = Any[Expr(:inbounds, true), expr.args..., Expr(:inbounds, :pop)]
                Core.Inference.meta_elim_pass!(args, true)
                expr.args = args # remove our inbounds
                expr
            end
        else
            type_ast(x.signature)
        end
        x.ast = rewrite_ast(x, ast)
    end
    x.ast
end

function rewrite_function(m, expr)
    expr.args[1] = m
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
    to_apply = resolve_func(m, expr.args[2])
    if all(x-> x <: Tuple, types[2:end])
        argtuple = apply_args[2:end]
        tuple_len = length(argtuple)
        # assign to tmp, in case it's  not a variable and instead a constructor expression
        tmp_exprs = []; args = []
        apply_types = []
        for i = 1:tuple_len
            arg_expr = argtuple[i]
            T = types[i + 1]
            push!(apply_types, to_tuple(T)...)
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
                childmethod = LazyMethod(m, getindex, (T, Int))
                expr = rewrite_function(childmethod, copy(expr))
                push!(args, expr)
            end
        end
        expr = typed_expr(orig_expr.typ, :call, to_apply, args...)
        childmethod = LazyMethod(m, to_apply, (apply_types...,))
        push!(m, childmethod)
        expr = rewrite_function(childmethod, expr)
        hasvarargs, n = has_varargs(childmethod)
        if hasvarargs
            # make a tuple out of varargs
            tupt = Tuple{apply_types[n - 1 : end]...}
            tup_expr = typed_expr(tupt, :call, tuple, expr.args[n:length(expr.args)]...)
            tup_expr = rewrite_ast(m, tup_expr)
            expr.args = [expr.args[1:n - 1]..., tup_expr]
        end
        return InlineNode(tmp_exprs, expr)
    end
    error("Unknown _apply construct. Found: $expr")
end

if isdefined(Base, :LambdaInfo)
    function get_static_parameters(lm::LazyMethod)
        to_tuple(getcodeinfo!(lm).sparam_vals)
    end
else
    function get_static_parameters(lm::LazyMethod)
        # TODO is this the correct way to get static parameters?! It seems to work at least
        world = typemax(UInt)
        y = Base._methods(lm.signature..., -1, world)
        isempty(y) && return ()
        x = first(y)
        to_tuple(x[2])
    end
end

function rewrite_quotenode(m::LazyMethod, node)
    node.value
end

specialized_typeof{T}(::T) = T
specialized_typeof{T}(::Type{T}) = Type{T}
unspecialized_type{T}(::Type{Type{T}}) = T
unspecialized_type{T}(::Type{T}) = T


make_typed_slot(m, slot::SlotNumber) = TypedSlot(slot.id, slottype(m, slot))
make_typed_slot(m, slot::TypedSlot) = slot
function make_typed_slot(m, slot::SSAValue)
    newslot!(m, slottype(m, slot), slotname(m, slot))
end

make_typed_slot(m, slot) = error("Lhs not a slot. Found: $slot")


# applicable is not overloadable
function exists(x::LazyMethod)
    istype(x) && return true # you can't construct a non existing type
    isintrinsic(x) && return true # must exist when intrinsic
    try
        getmethod!(x)
        return true
    catch e
        println(e)
        return false
    end
end
function isconcrete(x::LazyMethod)
    istype(x) && return isleaftype(x.signature)
    all(x-> isleaftype(x), Sugar.to_tuple(x.signature[2]))
end

Base.isvalid(x::LazyMethod) = exists(x) && isconcrete(x)

function assert_validity(x::LazyMethod)
    isvalid(x) && return
    if !isconcrete(x)
        throw(error("Method $x doesn't have concrete call types!"))
    end
    if !exists(x)
        throw(error("Method $x doesn't exist!"))
    end
end


function rewrite_vararg(lm, args, types)
    has_a_serious_case_of_the_varargs, n = has_varargs(lm)
    n = n - 1
    if has_a_serious_case_of_the_varargs
        # make a tuple out of varargs
        tup_expr = Expr(:call, tuple)
        for i in (n + 1):length(args)
            push!(tup_expr.args, args[i])
        end
        tupt = Tuple{types[(n):end]...}
        tup_expr.typ = tupt
        types = (types[1:n - 1]..., tupt)
        args = [args[1:n]..., tup_expr]
    end
    args, types
end

isclosure(FT) = false
function isclosure(FT::Type)
    FT <: Function && nfields(FT) > 0
end
resolve_module(x::Module) = x
resolve_module(x::GlobalRef) = getfield(x.mod, x.name)
"""
Rewrite the ast to resolve everything statically
and infers the dependencies of an expression
"""
function rewrite_ast(m, expr)
    istype(m) && return expr
    sparams = get_static_parameters(m)
    # needs to be done in a first pass for now, since the next step relies on
    # all static params being resolved!s
    expr = first(replace_expr(expr) do expr
        if isa(expr, Expr)
            if expr.head == :static_parameter
                param = sparams[expr.args[1]]
                push!(m, specialized_typeof(param))
                return true, param
            else
                T = expr.typ
                # Tuples containing types (.., Float32, ...) don't get specialized, but we can fix this
                # because inference basically has this information.
                if T <: Tuple && T != Union{}
                    types = to_tuple(T)
                    # if is call to tuple + has datatype in there, we can use the
                    # type of it's arguments
                    if any(x-> x == DataType, types) && expr.head == :call && expr.args[1] == GlobalRef(Core, :tuple)
                        expr.typ = Tuple{map(x-> Sugar.expr_type(m, x), expr.args[2:end])...}
                    end
                end
            end
        end
        false, expr
    end)
    list = replace_expr(expr) do expr
        try
            if isa(expr, SlotNumber)
                # lets make things simple and always use typed slots
                typ = expr_type(m, expr)
                push!(m, typ)
                return true, TypedSlot(expr.id, typ)
            elseif isa(expr, SSAValue)
                # lets make things simple and always use typed slots
                typ = expr_type(m, expr)
                push!(m, typ)
                return true, make_typed_slot(m, expr)
            elseif isa(expr, NewvarNode)
                # seems like newvarnodes are redundant with the way we pre define
                # slots, so we can drop them here! # TODO is this true?
                return true, ()
            elseif isa(expr, GlobalRef)
                value = getfield(expr.mod, expr.name)
                push!(m, specialized_typeof(value))
                return true, value
            elseif isa(expr, QuoteNode)
                value = rewrite_quotenode(m, expr)
                push!(m, specialized_typeof(value))
                return true, value
            elseif isa(expr, Expr)
                args, head = expr.args, expr.head
                if head == :(=)
                    lhs = make_typed_slot(m, args[1])
                    rhs = map(x-> rewrite_ast(m, x), args[2:end])
                    res = similar_expr(expr, [lhs, rhs...])
                    if !(lhs in m.decls) # if not already declared
                        # DECLARE IT!
                        push!(m.decls, lhs)
                        typ = expr_type(m, lhs)
                        decl = Expr(:(::), lhs, typ)
                        decl.typ = typ
                        push!(m, typ)
                        return true, (decl, res) # splice in declaration
                    end
                    return true, res
                elseif head == :call
                    func = args[1]
                    types = (map(x-> expr_type(m, x), args[2:end])...)
                    FT = Sugar.expr_type(m, func)
                    return_type = expr_type(m, expr)

                    f = if isclosure(FT)
                        insert!(args, 2, func) # add self reference to call
                        FT
                    else
                        resolve_func(m, func)
                    end
                    if f == typeof
                        return true, unspecialized_type(expr_type(m, expr))
                    end
                    if f == isa
                        T1 = expr_type(m, expr.args[2])
                        T2 = unspecialized_type(expr_type(m, expr.args[3]))
                        return true, (T1 <: T2)
                    end
                    if f == Core._apply
                        return true, rewrite_apply(m, types, expr)
                    end
                    if f == Core.getfield && types == (Module, Symbol) && isa(expr.args[3], Symbol)
                        return true, getfield(resolve_module(expr.args[2]), expr.args[3])
                    end
                    # TODO do this via deadcode elimination, dont eliminate if not dead
                    if f in (Base.throw, Base.throw_boundserror)
                        return true, ()
                    end
                    if f == typeassert
                        @assert length(expr.args) == 3
                        args = expr.args[2:end]
                        # typeassert(::T, Type{T}) where T
                        aT, bT = Sugar.expr_type.(m, args)
                        if !(aT <: unspecialized_type(bT))
                            error("Typeassert failed: found type $aT, needs to be $(unspecialized_type(bT))")
                        end
                        res = rewrite_ast(m, expr.args[2])
                        return true, res
                    end
                    @assert isleaftype(return_type) "Found non concrete return type: $return_type"
                    lm = LazyMethod(m, f, types)
                    assert_validity(lm) # lets try to catch errors as soon as possible!

                    result = rewrite_function(lm, similar_expr(expr, args))
                    # rewrite_function is allowed to fully eliminate function calls and return single values
                    if isa(result, Expr)
                        if result.head == :call # if still is a call
                            lm = first(result.args)
                            args, types = rewrite_vararg(lm, result.args, (map(x-> expr_type(m, x), result.args[2:end])...))
                            args[1] = lm
                            result = similar_expr(expr, args)
                        end
                        # recursively rewrite arguments
                        result.args = map(x-> rewrite_ast(m, x), result.args)
                    end
                    if needs_decompose(m, return_type)
                        m.cache[expr] = rhs
                    end
                    return true, result
                end
            end
            # at this point, only values and expressions are left
            # and we're only interested in catching the dependencies of values.
            # Expr types to be expected: return, if/else, while/for,curly and so forth
            if isa(expr, LazyMethod)
                assert_validity(expr)
                push!(m, expr)
            elseif isa(expr, Union{TypedSlot, SSAValue})
                push!(m, expr_type(m, expr))
            end
        catch e
            println(STDERR, "___________________________________________________________________")
            println(STDERR, "Error in Expr rewrite! $e")
             # TODO filter errors, there are definitely errors that we can pick out that needs to be rethrown
            println(STDERR)
            println(STDERR, "Expression resulting in the error: ")
            show_source(STDERR, m, expr)
            println(STDERR)
            println(STDERR, "happening in function tree:")
            Sugar.print_stack_trace(STDERR, m)
            println(STDERR)
            println(STDERR, "Code of the context this error occured in: ")
            # we need to use `sugared` directly, since otherwise it will
            # try to rewrite the expression and exactly run into this error while printing the error
            show_source(STDERR, m, Sugar.sugared(m.signature..., code_typed))
            println(STDERR)
            rethrow(e)
        end
        false, expr
    end
    expr = first(list)
    if isa(expr, Expr)
        remove_inlinenodes(expr, (expr.args, 1))
    else
        return expr
    end
end

function show_source(io::IO, m::LazyMethod, body = getast!(m))
    src = getcodeinfo!(m)
    emph_io = Base.IOContext(io, :TYPEEMPHASIZE => true)
    sn = [String.(Sugar.slotnames(m))...]
    Base.show_unquoted(
        Base.IOContext(
            Base.IOContext(emph_io, :SOURCEINFO => src),
            :SOURCE_SLOTNAMES => sn
        ),
        body, 2
    )
end

function type_dependencies!(lm::LazyMethod)
    typ = lm.signature
    if isleaftype(typ) || isa(typ, Type)
        for name in fieldnames(typ)
            typ == Module && continue
            ft = fieldtype(typ, name)
            # Tuples can be types that are not possible to instantiate, e.g. Tuple{1, 1}
            if !(typ <: Tuple && !isa(ft, DataType))
                push!(lm, ft)
            end
        end
        for T in typ.parameters
            isa(T, DataType) && push!(lm, T)
        end
    else
        print_stack_trace(STDERR, lm)
        error("Found non concrete type: $(lm.signature)")
    end
end

function dependencies!(lm::LazyMethod, recursive = false)
    deps = OrderedSet{typeof(lm)}()
    if isfunction(lm)
        for elem in to_tuple(lm.signature[2])
            push!(lm, elem)
        end
        RT = returntype(lm)
        if isa(RT, DataType) && RT != Nothing && RT != Union{}
            push!(lm, RT)
        end
        getast!(lm) # walks ast && insertes dependencies
    else
        type_dependencies!(lm)
    end
    for elem in lm.dependencies
        if recursive
            deps2 = dependencies!(elem, true)
            for elem2 in deps2 # lol there is no append! ?!
                push!(deps, elem2)
            end
        end
        push!(deps, elem)
    end
    deps
end

remove_inlinenodes(node, insertion) = node

function remove_inlinenodes(node::InlineNode, insertion)
    list = Any[nothing] # cant be empty for splice! to work
    results = remove_inlinenodes.(node.deps, ((list, 1:1),))
    filter!(x-> x != nothing, list)
    splice!(insertion[1], insertion[2], vcat(list, results))
    remove_inlinenodes(node.expression, insertion)
end

function remove_inlinenodes(expr::Expr, insertion)
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
    sprint() do io
        Base.show_unquoted(io, getast!(x), 0, 0)
    end
end

function gettypesource(x::LazyMethod)
    sprint() do io
        dump(io, x.signature)
    end
end

function print_stack_trace(io, x::LazyMethod)
    println(io, "Sugar stack trace:")
    i = 1
    while true
        println(io, "  [$i] ", x)
        println(io)
        i += 1
        isdefined(x, :parent) || break
        x = x.parent
    end
    return
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
expr_type(x) = expr_type(nothing, x)

expr_type(lm, x::Expr) = x.typ
expr_type(lm, x::GlobalRef) = specialized_typeof(getfield(x.mod, x.name))
expr_type{T}(lm, x::Type{T}) = Type{T}
expr_type{T}(lm, x::T) = T
expr_type(lm, x::InlineNode) = expr_type(lm, x.expression)

expr_type(lm::Nothing, x::TypedSlot) = x.typ
expr_type(lm::LazyMethod, x::TypedSlot) = x.typ

function expr_type(lm::Nothing, slot::Union{Slot, SSAValue})
    error("Can't get expression type of an untyped SSAValue/Slot without a propper method context")
end
expr_type(lm::LazyMethod, slot::Union{Slot, SSAValue}) = slottype(lm, slot)
function expr_type(lm, m::LazyMethod)
    isfunction(m) ? typeof(getfunction(m)) : m.signature
end

function instance{F <: Function}(x::Type{F})
    F.instance
end
instance{T}(x::Type{T}) = x

extract_type{T}(x::Type{T}) = T

"""
Takes any value found in the context of a LazyMethod and returns
A concrete function!
"""
function resolve_func(m, f::LazyMethod)
    if isfunction(f)
        getfunction(f)
    else
        f.signature
    end
end
resolve_func(m, f::AllFuncs) = f
resolve_func{T}(m, X::Type{Type{T}}) = T
resolve_func{T}(m, X::Type{T}) = X
resolve_func(m, f::Union{GlobalRef, Symbol}) = eval(f)
function resolve_func(m, val::Union{Slot, SSAValue, Expr})
    f = expr_type(m, val)
    if isclosure(f)
        return resolve_func(m, f)
    else
        if f <: AllFuncs
            instance(f)
        else
            resolve_func(m, f)
        end
    end
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
    functype = m.signature[1]
    calltypes, slots = to_tuple(m.signature[2]), getslots!(m)
    n = method_nargs(m)
    args = map(2:n) do i
        argtype, name = slots[i]
        # Slot types might be less specific, e.g. when the variable is unused it might end up as Any.
        # but generally the slot type is the correct one, especially in the context of varargs.
        calltype = if !isleaftype(argtype) && length(calltypes) <= i
            argtype = calltypes[i - 1]
        end
        expr = :($(name)::$(argtype))
        expr.typ = argtype
        expr
    end
    Expr(:function,
        Expr(:call, name, args...),
        body
    )
end


function show_comment(io, comment)
    println(io, "# ", comment)
end

function print_dependencies(io, method, visited = Set())
    (method in visited) && return
    push!(visited, method)
    for elem in dependencies!(method)
        print_dependencies(io, elem, visited)
    end
    isintrinsic(method) && return
    try
        show_comment(io, method.signature)
        println(io, getsource!(method))
    catch e
        println(STDERR, "___________________________________________________________________")
        println(STDERR, "Can't compile dependency: $(method.signature)")
         # TODO filter errors, there are definitely errors that we can pick out that needs to be rethrown
        println(STDERR, e)
        display(catch_stacktrace())
        println(STDERR, "happening in function tree:")
        Sugar.print_stack_trace(STDERR, method)
        println(STDERR)
        println(STDERR, "___________________________________________________________________")
    end
end

# interface for transpilers
typename(io::IO, T) = string(T)
function _typename end
function functionname(io::IO, lm::LazyMethod)
    if isfunction(lm)
        string(Symbol(getfunction(lm)))
    else
        error("Not a function: $lm")
    end
end
function show_name end
function show_type end
function show_function end

function supports_overloading end
function vecname(io::IO, T)
    println(io, T)
end

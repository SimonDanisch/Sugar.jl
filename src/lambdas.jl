struct NoMethodError <: Exception
    func
    types::Tuple
end
NoMethodError(f, types::Type) = NoMethodError(f, (types.parameters...))
function Base.showerror(io::IO, e::NoMethodError)
    args = join(map(t->"::$t", e.types), ", ")
    print(io, "$(e.func)($args) couldn't be found")
end

# Give string based stages a type
struct CodeLLVM
    source::String
end
function CodeLLVM(f, types)
    src = sprint() do io
        code_llvm(io, f, types)
    end
    CodeLLVM(src)
end
struct CodeNative
    source::String
end
function CodeNative(f, types)
    src = sprint() do io
        code_native(io, f, types)
    end
    CodeNative(src)
end

# deal with all variances in base that should really be tuples but are something else
to_tuple(x) = (x,)
to_tuple(x::Core.SimpleVector) = tuple(x...)
to_tuple(x::Tuple) = x
to_tuple(x::AbstractVector) = tuple(x...)
to_tuple(x::Type{Tuple}) = tuple(x.parameters...)

# typeof working with concrete and types at the same time
function _typeof(x::Type{T}) where T
	Type{T}
end
function _typeof(x::T) where T
	T
end

function juliabasepath(file)
    srcdir = joinpath(Sys.BINDIR,"..","..","base")
    releasedir = joinpath(Sys.BINDIR,"..","share","julia","base")
    normpath(joinpath(isdir(srcdir) ? srcdir : releasedir, file))
end

function get_source_file(path::AbstractString, ln::Int)
    isfile(path) && return path
    # if not a file, it might be in julia base
    file = juliabasepath(path)
    if !isfile(file)
        throw(LoadError(path, ln, ErrorException("file $path not found")))
    end
    file
end


function get_lambda(pass, ftype::DataType, types)
    world = typemax(UInt)
    if !isclosure(ftype)
        ftype = Type{ftype}
    end
    tt = Tuple{ftype, to_tuple(types)...}
    (ti, env, meth) = Base._methods_by_ftype(tt, 1, world)[1]
    meth = Base.func_for_method_checked(meth, tt)
    params = Core.Inference.InferenceParams(world)
    (_, code, ty) = Core.Inference.typeinf_code(meth, ti, env, false, false, params)
    code
end

function get_ast(pass, f, types)
    lambda = get_lambda(pass, f, types)
    get_ast(lambda)
end
function get_ast(li::Core.CodeInfo)
    ast = li.code
    if isa(ast, Vector{UInt8})
        return Base.uncompressed_ast(li)
    end
    ast
end

function get_static_parameters(f, types)
    m = get_method(f, types)
    mi = m.specializations.func
    spnames = map(x->x.name, to_tuple(m.tvars))
    sptypes = to_tuple(mi.sparam_vals)
    spnames, sptypes
end

function get_lambda(pass, f, types, optimize = false)
    if isintrinsic(f)
        error("$f is an intrinsic function")
    end
    lambda = try
        if pass == code_typed
            pass(f, types, optimize = optimize)
        else
            pass(f, types)
        end
    catch e
        error("Couldn't get lambda for $f $types:\n$e")
    end
    if isa(lambda, Vector)
        if isempty(lambda)
            throw(NoMethodError(f, types))
        elseif length(lambda) == 1
            lam = first(lambda)
            if isa(lam, Pair)
                return first(lam)
            else
                return lam
            end
        else
            error("
                More than one method found for signature $f $types.
                Please use more specific types!
            ")
        end
    else
        isa(lambda, LambdaInfo) && return lambda
        error("Not sure what's up with returntype of $pass. Returned: $lambda")
    end
end
function get_method(f, types::Type)
    get_method(f, (types.parameters...))
end
function get_method(ftype::DataType, types::Tuple)
    world = typemax(UInt)
    if !isclosure(ftype)
        ftype = Type{ftype}
    end
    tt = Tuple{ftype, to_tuple(types)...}
    (ti, env, meth) = Base._methods_by_ftype(tt, 1, world)[1]
    Base.func_for_method_checked(meth, tt)
end
function get_method(f, types::Tuple)
    if !all(isleaftype, types)
        error("Not all types are concrete: $types")
    end
    # make sure there is a specialization with precompile
    # TODO, figure out a better way, since this method is not very reliable.
    # (I think, e.g. anonymous functions don't work)
    precompile(f, (types...))
    x = methods(f, types)
    if isempty(x)
        throw(NoMethodError(f, types))
    elseif length(x) != 1
        error("
            More than one method found for signature $f $types.
            Please use more specific types!
        ")
    end
    first(x)
end



"""
Looks up the source of `method` in the file path found in `method`.
Returns the AST and source string, might throw an LoadError if file not found.
"""
function get_source_at(file, linestart::Int)
    file = get_source_file(file, linestart)
    code, str = open(file) do io
        line = ""
        for i=1:linestart-1
            line = readline(io)
        end
        try # lines can be one off, which will result in a parse error
            parse(line)
        catch e
            line = readline(io)
        end
        while !eof(io)
            line = line * "\n" * readline(io)
            e = Base.parse_input_line(line; filename=file)
            if !(isa(e,Expr) && e.head === :incomplete)
                return e, line
            end
        end
    end
    code, str
end

function get_source(method::Method)
    file = string(method.file)
    linestart::Int = method.line
    code, str = get_source_at(file, linestart)
    # for consistency, we always return the `function f(args...) end` form
    long = MacroTools.longdef(code)
    # and return only the body
    long.args[2], str
end

function slot_vector(lam_typed)
    if isa(lam_typed.slotnames, Void) || isa(lam_typed.slottypes, Void)
        return [(SlotNumber(-1), ("", Void))]
    end
    slotnames = copy(lam_typed.slotnames)
    slottypes = copy(lam_typed.slottypes)

    slots = [(SlotNumber(i), (string(name), slottypes[i])) for (i, name) in enumerate(slotnames)]
    ssaslot = [(SSAValue(i-1), ("ssa_$(i-1)", t)) for (i,t) in enumerate(lam_typed.ssavaluetypes)]
    vcat(slots, ssaslot)
end

function slot_dictionary(lam_typed)
    slots = slot_vector(lam_typed)
    s_dict = Dict()
    for (k, (name, T)) in slots
        if !isa(k, SSAValue)
            s_dict[k] = T
        end
        s_dict[Symbol(name)] = T
    end
    s_dict
end

"""
Returns an AST most similar to what you would get from a macro
"""
function macro_form(f, types)
    method = get_method(f, types)
    local code::Expr; local str::String
    try
        code, str = get_source(method)
    catch e
        if isa(e, LoadError)
            # file for method not found, we need to get the source the low level way
            # (this is the case when e.g. code comes from sysimg without source install or REPL/IJulia)
            # allthough for the REPL/IJUlia we might be able to figure something out, since it's theoretically saved somewhere
            # .. and what about fused functions generated for broadcast?
            code = code_lowered_clean(f, types)
            str  = sprint() do io
                show(io, code)
            end
        else
            rethrow(e)
        end
    end
end

"""
Returns only one return type. If multiple are applicable, returns a Union.
"""
function return_type(f, types)
    x = Base.return_types(f, types)
    if isempty(x)
        throw(NoMethodError(f, types))
    elseif length(x) == 1
        x[1]
    else
        Union{x...}
    end
end


function clean_form(f, types)
    ast, str = macro_form(f, types)
    static_params = get_static_parameters(f, types)
    ast = filter_expr(x-> !is_linenumber(x), ast)
    remove_static_params(ast, static_params)
end

function clean_typed(f, types)
    ast = clean_form(f, types)
    sdict = slot_dictionary(get_lambda(code_typed, f, types))
    insert_types(ast, sdict)
end

const _source_map = Dict{Function, Expr}()

macro preserve_source(expr)
    # TODO this doesn't seem to work for curly
    result = @match expr begin
        (
            f_(args__) = body_ |
            function f_(args__) body_ end |
            f_{sargs__}(args__) = body_ |
            function f_{sargs__}(args__) body_ end
        ) => (f, args, body)
    end
    if result == nothing
        error("Expr $expr doesn't declare a function")
    end
    func_expr = MacroTools.longdef(expr) # always have the function be in long form (function x(args...) end)
    quote
        # evaluate function
        $expr
        # insert into source map
        _source_map[$f] = $(Expr(:quote, func_expr))
    end
end

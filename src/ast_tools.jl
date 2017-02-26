function filter_expr(keep, ast)
    replace_or_drop(x-> (false, x), x-> !keep(x), ast)
end
function replace_expr(f, ast)
    replace_or_drop(f, x-> false, ast) # never drop/filter
end
function replace_or_drop(f, drop, ast::Vector, result = [])
    for elem in ast
        replace_or_drop(f, drop, elem, result)
    end
    result
end

function similar_expr(x::Expr, args)
    expr = Expr(x.head)
    expr.typ = x.typ
    expr.args = args
    expr
end
similar_expr(x::Expr) = similar_expr(x, [])


function replace_or_drop(f, drop, ast, result = [])
    drop(ast) && return result
    replace, replacement = f(ast)
    if replace
        push!(result, replacement)
    else
        expr = if isa(ast, Expr)
            nexpr = similar_expr(ast)
            replace_or_drop(f, drop, ast.args, nexpr.args)
            nexpr
        else
            ast
        end
        push!(result, expr)
    end
    result
end

function remove_static_params(ast, static_params)
    sp_names, sp_types = static_params
    replace_expr(ast) do expr
        if isa(expr, Symbol)
            idx = findfirst(sp_names, expr)
            if idx != 0
                return true, sp_types[idx]
            end
        end
        false, expr
    end
end


function extract_type(x::Symbol, slots)
    m = current_module()
    if isdefined(m, x)
        _typeof(getfield(m, x))
    else
        Symbol
    end
end
extract_type{T}(x::T, slots) = T
function extract_type(x::Expr, slots)
    if x.head == :(::)
        x.args[2]
    else
        extract_type(insert_types(x, slots), slots)
    end
end
function get_func(x::Expr)
    x.head == :curly && return get_func(x.args[1])
end
function get_func(x::Symbol)
    getfield(current_module(), x)
end
function get_func(x::GlobalRef)
    getfield(x.mod, x.name)
end
function extract_func(x::Expr, slots)
    @assert x.head == :call
    f = get_func(x.args[1])
    args = x.args[2:end]
    typed = insert_types(args, slots)
    _typed = !isa(typed, Vector) ? Any[typed] : typed
    f, _typed
end
isa_applytype(x) = false
function isa_applytype(x::Expr)
    x.head == :. && x.args[1] == :Core && x.args[2] == QuoteNode(:apply_type)
end
function isa_applytype(x::GlobalRef)
    x.mod == Core && x.name == :apply_type
end
function isa_applytype(x::Expr)
    x.head == :call || return false
    isa_applytype(x.args[1])
end
applytype_args(x::Expr) = x.args[2:end]

function applytype_type(x::Expr, args)
    Targs = x.args[2:end]
    Expr(:curly, Targs...)
end
function applytype_type(x::GlobalRef, args::Vector)
    Expr(:curly,  args...)
end
"""
Takes an AST and a slot dictionary (gotten with slot_dictionary)
"""
function insert_types(ast::Expr, slot_dict)
    replace_expr(ast) do expr

        if haskey(slot_dict, expr)
            return true, Expr(:(::), expr, slot_dict[expr])
        end
        if isa(expr, Symbol) # symbol not in slot_dict -> can't do much about it
            return true, expr
        end
        if !isa(expr, Expr)
            # TODO, figure out what value we can expect here, that are not symbols or values
            return true, insert_types(expr, slot_dict)
        end
        # TODO only expand unmatched without recursion loop!
        # Maybe recurse iff expand(expr) != expr (seems fragile)
        result = @match expand(expr) begin
            (lh_ = rh_) => begin
                lh = insert_types(lh, slot_dict)
                rh = insert_types(rh, slot_dict)
                true, Expr(:(=), lh, rh)
            end
            # function call
            f_(args__) => begin
                if isa_applytype(f)
                    T = applytype_type(f, args)
                    return true, Expr(:(::), Expr(:call, T, args...), T)
                end
                typed_args = map(args) do arg
                    insert_types(arg, slot_dict)
                end
                types = tuple(map(x-> extract_type(x, slot_dict), typed_args)...)
                func = get_func(f)
                @show func types
                T = return_type(func, types)
                true, Expr(:(::), Expr(:call, f, typed_args...), T)
            end
            _ => false, expr
        end
    end
end
function insert_types{T}(value::T, slot_dict)
    Expr(:(::), value, T)
end

function insert_types(sym::Symbol, slot_dict)
    if haskey(slot_dict, sym)
        Expr(:(::), sym, slot_dict[sym])
    else
        # TODO, pass through functions module!
        if isdefined(sym)
            return Expr(:(::), sym, typeof(getfield(current_module(), sym)))
        else
            sym # symbol not in slot_dict -> can't do much about it
        end
    end
end
_normalize_ast(value) = true, value
function _normalize_ast(qn::QuoteNode)
    return true, qn.value
end

function resolve_typ(x::Expr)
    x.typ.parameters[1]
end
resolve_typ(x::GlobalRef) = eval(x)

function _normalize_ast(expr::Expr)
    if expr.head == :invoke
        lam = expr.args[1] # Ignore lambda for now
        res = similar_expr(expr, map(normalize_ast, view(res.args, 2:length(expr.args))))
        return true, res
    elseif expr.head == :new
        T = resolve_typ(expr.args[1])
        expr = Expr(:call, T, map(normalize_ast, expr.args[2:end])...)
        expr.typ = T
        return true, expr
    # elseif expr.head == :static_parameter# TODO do something reasonable with static and meta
    #     # TODO, can other static parameters beside literal values escape with code_typed, optimization = false?
    #     return true, expr.args[1]
    elseif expr.head == :meta
        return true, nothing
    elseif expr.head == :call
        f = expr.args[1]
        if Sugar.isa_applytype(f)
            args = expr.args[2:end]
            T = applytype_type(f, args)
            return true, similar_expr(expr, vcat(T, map(normalize_ast, args)))
        end
        return true, similar_expr(expr, map(normalize_ast, expr.args))
    end
    return false, expr
end
function normalize_ast(expr)
    ast = Sugar.replace_expr(_normalize_ast, expr)
    Sugar.replace_or_drop(x-> (false, x), x-> x == nothing, ast)
end


function remove_inline(list)
    stack = []; result = []
    for elem in list
        if isa(elem, Expr) && elem.head == :meta
            if elem.args[1] == :push_loc
                inexpr = Expr(:inlined_func, elem.args[2:end]...)
                if !isempty(stack)
                    push!(last(stack).args, inexpr) # add to parent
                end
                push!(stack, inexpr)
            elseif elem.args[1] == :pop_loc
                if isempty(stack)
                    error("found pop_loc, but there was no push_loc")
                end
                expr = pop!(stack)
                if isempty(stack)
                    push!(result, expr)
                end
            end
        elseif !isempty(stack) # we're in the middle of an inline expr
            push!(last(stack).args, elem)
        else
            push!(result, elem)
        end
    end
    result
end

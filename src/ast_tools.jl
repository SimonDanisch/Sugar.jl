function filter_expr(keep, ast)
    replace_or_drop(x-> (false, x), x->!keep(x), identity, Any[ast])[1]
end
function replace_expr(f, ast)
    replace_or_drop(f, x-> false, Any[ast])[1]#ever drop
end
function replace_or_drop(f, drop, ast::Vector, result = [])
    for elem in ast
        replace_or_drop(f, drop, elem, result)
    end
    result
end

function replace_or_drop(f, drop, ast, result = [])
    drop(ast) && return result
    replace, replacement = f(ast)
    if replace
        push!(result, replacement)
    else
        expr = if isa(ast, Expr)
            nexpr = Expr(ast.head)
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
        extract_type(add_typing(x, slots), slots)
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
    typed = add_typing(args, slots)
    _typed = !isa(typed, Vector) ? Any[typed] : typed
    f, _typed
end


"""
Takes an AST and a slot dictionary (gotten with )
"""
function insert_types(ast::Expr, slot_dict)
    replace_expr(ast) do expr
        if haskey(slot_dict, expr)
            return true, Expr(:(::), expr, slot_dict[expr])
        end
        result = @match expr begin
            (lh_ = rh_) => begin
                lh = insert_types(lh, slot_dict)
                rh = insert_types(rh, slot_dict)
                true, Expr(:(=), lh, rh)
            end
            f_(args__) => begin
                typed_args = map(args) do arg
                    insert_types(arg, slot_dict)
                end
                types = tuple(map(x-> extract_type(x, slot_dict), typed_args)...)
                func = get_func(f)
                T = return_type(func, types)
                true, Expr(:(::), Expr(:call, f, args...), T)
            end
            _ => false, expr
        end
    end
end
function insert_types{T}(value::T, slot_dict)
    Expr(:(::), value, T)
end

function insert_types(sym::Symbol, slot_dict)
    Expr(:(::), sym, slot_dict[sym])
end

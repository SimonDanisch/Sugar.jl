"""
Creates an expression with the same head and typ
"""
function similar_expr(x::Expr, args)
    expr = Expr(x.head)
    expr.typ = x.typ
    expr.args = args
    expr
end
similar_expr(x::Expr) = similar_expr(x, [])


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

function replace_or_drop(f, drop, ast, result = [])
    drop(ast) && return result
    replace, replacement = f(ast)
    if replace
        if isa(replacement, Tuple)
            push!(result, replacement...)
        else
            push!(result, replacement)
        end
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


isa_applytype(x) = false
# function isa_applytype(x::Expr)
#     x.head == :. && x.args[1] == :Core && x.args[2] == QuoteNode(:apply_type)
# end
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

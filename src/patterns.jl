safe_resolve_func(x) = nothing
safe_resolve_func(f::AllFuncs) = f
safe_resolve_func{T}(::Type{T}) = T
safe_resolve_func(f::Union{GlobalRef, Symbol}) = getfield(f.mod, f.name)


nice_dump(x, intent = 0) = (print("    "^intent); show(x); println())
nice_dump(x::LineNumberNode, intent = 0) = nothing
function nice_dump(x::Expr, intent = 0)
    println("    "^intent, "head: ", x.head)
    intent += 1
    for elem in x.args
        nice_dump(elem, intent)
    end
end

struct Label
    label::Symbol
end
struct Goto
    label::Symbol
end
struct GotoIfNot
    condition::Any
    label::Symbol
end

function MacroTools.match(pat::Symbol, ex::GlobalRef, env)
    MacroTools.match(GlobalRef(ex.mod, pat), ex, env)
end
function MacroTools.match(pat::Expr, ex::GlobalRef, env)
    MacroTools.match(pat, Expr(:(.), Symbol(ex.mod), QuoteNode(ex.name)), env)
end
function MacroTools.match(pat::Label, ex::LabelNode, env)
    MacroTools.match(:($(pat.label)), :($(ex.label)), env)
end
function MacroTools.match(pat::Goto, ex::GotoNode, env)
    MacroTools.match(:($(pat.label)), :($(ex.label)), env)
end
function MacroTools.match(pat::GotoIfNot, ex::Expr, env)
    MacroTools.match(Expr(:gotoifnot, pat.condition, pat.label), ex, env)
end


"""
MacroTools match functor
"""
struct MTMatchFun <: Matcha.MatchFunc
    pattern
end

function (pat::MTMatchFun)(expr, hist)
    try
        MacroTools.match(pat.pattern, expr, hist.env)
        return true
    catch e
        isa(e, MacroTools.MatchError) ? false : rethrow()
    end
end

remove_meta(ast::Vector) = remove_meta!(copy(ast))
function remove_meta!(ast::Vector)
    filter!(ast) do expr
        !(
            (expr isa LineNumberNode) ||
            (expr == nothing) ||
            ((expr isa Expr) && (expr.head == :meta))
        )
    end
    ast
end

struct Slurp <: Matcha.MatchFunc
    sym::Symbol
end
function (x::Slurp)(expr, hist)
    push!(get!(hist.env, x.sym, []), expr)
    true
end

function macrotools_patterns(patterns::Vector)
    patterns = remove_meta(patterns)
    matcha_pattern = ntuple(length(patterns)) do i
        pat = patterns[i]
        if MacroTools.isslurp(pat)
            sym = MacroTools.bname(pat)
            Matcha.Greed(Slurp(sym))
        else
            MTMatchFun(pat)
        end
    end
    matcha_pattern
end

no_quote(x::QuoteNode) = x.value
no_quote(x) = x

macro ast_pattern(block)
    if block.head != :block
        error("Please supply a block. Found: $(block.head)")
    end
    special_nodes = (:Label, :Goto, :GotoIfNot)
    map!(block.args, block.args) do arg
        if isa(arg, Expr) && arg.head == :call && arg.args[1] in special_nodes
            f = arg.args[1]
            getfield(Sugar, f)(no_quote.(arg.args[2:end])...)
        else
            arg
        end
    end
    macrotools_patterns(block.args)
end


"""
usage @exctract dict (a, b, c, d)
"""
macro extract(scene, args)
    if args.head != :tuple
        error("Usage: args need to be a tuple. Found: $args")
    end
    expr = Expr(:block)
    for elem in args.args
        push!(expr.args, :($(esc(elem)) = $(esc(scene))[$(QuoteNode(elem))]))
    end
    expr
end

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
        x = copy(hist.env)
        MacroTools.match(pat.pattern, expr, x)
        merge!(hist.env, x)
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

function Matcha.view_constructor(x::Slurp, h::Matcha.History{X, T, Y}, a, b) where {X, Y, T <: SubArray}
    match = view(h.buffer, a:b)
    if !haskey(h.env, x.sym)
        h.env[x.sym] = match
    end
    match
end

(x::Slurp)(expr) = true

function macrotools_patterns(patterns::Vector)
    patterns = remove_meta(patterns)
    matcha_pattern = ntuple(length(patterns)) do i
        pat = patterns[i]
        if pat isa Union{Greed, Matcha.MatchFunc}
            pat
        elseif MacroTools.isslurp(pat)
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

eval_range(x) = error("Invalid range: $x")
eval_range(x::Range) = x
function eval_range(x::Expr)
    Meta.isexpr(x, :call) && x.args[1] == :(:) && return x.args[2] : x.args[3]
    error("Invalid range: $x")
end

function eval_special_nodes(arg::Expr)
    special_nodes = (:Label, :Goto, :GotoIfNot)
    if Meta.isexpr(arg, :call)
        f = arg.args[1]
        if f in special_nodes
            return getfield(Sugar, f)(no_quote.(arg.args[2:end])...)
        elseif f == :Greed
            expr = arg.args[2]
            range = arg.args[3]
            if MacroTools.isslurp(expr)
                error("Can't slurp and greed at the same time. Slurping greed: $arg")
            end
            return Greed(MTMatchFun(eval_special_nodes(expr)), eval_range(range))
        end
    end
    arg
end
macro ast_pattern(block)
    if block.head != :block
        error("Please supply a block. Found: $(block.head)")
    end
    map!(block.args, block.args) do arg
        if isa(arg, Expr) && arg.head == :call
            eval_special_nodes(arg)
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

is_call(x) = false
is_call(x::Expr) = x.head == :call


isunless(x::Expr) = x.head == :gotoifnot
isunless(x) = false
islabelnode(x::LabelNode) = true
islabelnode(x) = false
isgoto(x::GotoNode) = true
isgoto(x) = false

function is_unless_label(label, hist, histpos = 1)
    islabelnode(label) || return false
    unless = hist[histpos][1]
    unless_label = unless.args[2]
    unless_label == label.label
end
function is_goto_label(label, hist, histpos)
    islabelnode(label) || return false
    goto = hist[histpos][1]
    goto.label == label.label
end
function is_goto(goto, hist, histpos)
    isgoto(goto) || return false
    label = hist[histpos][1]
    goto.label == label.label
end
function is_unless_goto(goto, hist, histpos)
    isgoto(goto) || return false
    unless = hist[histpos][1]
    goto.label == unless.args[2]
end

safe_resolve_func(x) = nothing
safe_resolve_func(f::AllFuncs) = f
safe_resolve_func{T}(::Type{T}) = T
safe_resolve_func(f::Union{GlobalRef, Symbol}) = getfield(f.mod, f.name)

function iscolon(expr)
    isa(expr, Expr) && expr.head == :(=) || return false
    lhs, rhs = expr.args
    isa(rhs, Expr) && rhs.head == :call || return false
    safe_resolve_func(rhs.args[1]) == colon || return false
    return true
end

function isstart(expr, hist)
    isa(expr, Expr) && expr.head == :(=) || return false
    lhs, rhs = expr.args
    isa(rhs, Expr) && rhs.head == :call || return false
    safe_resolve_func(rhs.args[1]) == start || return false
    colon = hist[1][1]
    slot = colon.args[1]
    slotstart = rhs.args[2]
    slot == slotstart || return false
    return true
end
function isnext(expr, hist)
    isa(expr, Expr) && expr.head == :(=) || return false
    lhs, rhs = expr.args
    isa(rhs, Expr) && rhs.head == :call || return false
    safe_resolve_func(rhs.args[1]) == next || return false
    colon = hist[1][1]; slot = colon.args[1]
    slotnext = rhs.args[2]
    slot == slotnext || return false
    return true
end
function is_done_unless(expr, hist)
    Sugar.isunless(expr) || return false
    condition = expr.args[1]
    isa(condition, Expr) && condition.head == :call || return false
    safe_resolve_func(condition.args[1]) == (!) || return false
    done_expr = condition.args[2]
    isa(done_expr, Expr) && done_expr.head == :call || return false
    safe_resolve_func(done_expr.args[1]) == done || return false
    colon = hist[1][1]; slot = colon.args[1]
    slotdone = done_expr.args[2]
    slot == slotdone || return false
    return true
end
function isgetfield(expr, slotnext)
    isa(expr, Expr) && expr.head == :(=) || return false
    lhs, rhs = expr.args
    isa(rhs, Expr) && rhs.head == :call || return false
    safe_resolve_func(rhs.args[1]) == getfield || return false
    slot = rhs.args[2]
    slot == slotnext || return false
    return true
end

nice_dump(x, intent = 0) = (print("    "^intent); show(x); println())
nice_dump(x::LineNumberNode, intent = 0) = nothing
function nice_dump(x::Expr, intent = 0)
    println("    "^intent, "head: ", x.head)
    intent += 1
    for elem in x.args
        nice_dump(elem, intent)
    end
end



macro expressionmatch(expr)
    nice_dump(expr)
end

using MacroTools
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

struct MTMatchFun
    idx::Int
    patterns::Vector
    env::Dict{Any, Any}
end
function (pat::MTMatchFun)(expr)
    try
        MacroTools.match(pat.patterns[pat.idx], expr, pat.env)
        return true
    catch e
        isa(e, MacroTools.MatchError) ? (return false) : rethrow()
    end
end

struct FrameBuffer{N, ElTypes}
    buffers::NTuple{N, <: Texture}
end


function mt_match(patterns::Vector)
    env = Dict()
    map((1:length(patterns)...,)) do i
        pat = patterns[i]
        if MacroTools.isslurp(pat)
            sym = MacroTools.bname(pat)
            (expr)-> (push!(get!(env, pat, []), expr); true)
        else
            function (expr)
                try
                    MacroTools.match(patterns[i], expr, env)
                    return true
                catch e
                    empty!(env)
                    isa(e, MacroTools.MatchError) ? (return false) : rethrow()
                end
            end
        end
    end
end

pat = quote
    ssa0_ = colon(start_, end_)
    state_ = start(ssa0_)

    $(Label(:startlabel_))

    ssa1_ = done(ssa0_, state_)
    ssa2_ = typeassert(ssa1_, Bool)
    ssa3_ = Base.not_int(ssa2_)

    $(GotoIfNot(:ssa3_, :endlabel_))

    ssa4_ = next(ssa0_, state_)
    idx_ = getfield(ssa4_, 1)
    state_ = getfield(ssa4_, 2)

    body__

    $(Label(:prebody_))
    $(Goto(:startlabel_))
    $(Label(:endlabel_))
end
filter!(x-> !isa(x, LineNumberNode), pat.args)

##########################
# code lowered AST patterns
const for_pattern = (
    iscolon,
    isstart,
    islabelnode, # loop goto label
    is_done_unless, # while condition branch
    anything, # new varnodes etc
    isnext,
    anything, # body
    Greed(islabelnode, 0:1), # optional continue label
    (l,h)-> is_goto(l, h, 3), # goto label, matching first label
    (l,h)-> is_unless_label(l, h, 4) # goto and break
)

const ifelse_pattern = (
    isunless, # if branch
    anything, # if body
    isgoto, # goto to jump over else
    (l, h)-> is_unless_label(l, h, 1),
    anything,   # else body
    (l, h)-> is_goto_label(l, h, 3) # label matching above goto
)
const while_pattern = (
    islabelnode, # loop goto label
    isunless, # while condition branch
    anything, # body
    Greed(islabelnode, 0:1), # optional continue label
    (l, h)-> is_goto(l, h, 1), # goto label, matching first label
    (l, h)-> is_unless_label(l, h, 2) # goto and break
)

const if_pattern = (
    isunless, # condition
    anything, # body
    Greed(is_unless_label, 0:1)
)

const goto_neighbours = (
    isgoto, # goto label directly next to it
    (l, h)-> is_goto_label(l, h, 1)
)


##########################
# LLVM string patterns

# Function call
# %15 = call i8 @julia_mapreduce_sc_impl_60977(%jl_value_t* %0)
llvm_function_call = r"(.*) = call (.*) @(.*)\(.*\)"


##########################
# Assembly string patterns
assembly_source_line = r"Source line: ([1-9][0-9]+)"

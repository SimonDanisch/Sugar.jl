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

##########################
# code lowered AST patterns

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
    (l,h)-> is_goto(l, h, 1), # goto label, matching first label
    (l,h)-> is_unless_label(l, h, 2) # goto and break
)

const if_pattern = (isunless, anything, is_unless_label)


##########################
# LLVM string patterns

# Function call
# %15 = call i8 @julia_mapreduce_sc_impl_60977(%jl_value_t* %0)
llvm_function_call = r"(.*) = call (.*) @(.*)\(.*\)"


##########################
# Assembly string patterns

assembly_source_line = r"Source line: ([1-9][0-9]+)"

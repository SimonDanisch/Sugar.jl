__precompile__(true)
module Sugar

using Matcha, MacroTools, DataStructures, Compat

const AllFuncs = Union{Function, Core.Builtin, Core.IntrinsicFunction}
const IntrinsicFuncs = Union{Core.Builtin, Core.IntrinsicFunction}

# All kind of patterns for regex/matcha. Contains also matching isa functions
include("patterns.jl")

# various tools to replace and work with asts
# TODO figure out what can be used from the great MacroTools
include("ast_tools.jl")
export normalize_ast
# Tools for extracting all kind of representations out of a method/function
include("lambdas.jl")
export slot_vector, get_lambda, clean_typed

# "Sugarcoats" tools to transform the unsightly representation returned by code_typed
# into something sweet and beautiful (namely an Expr tree closer to what you get
# from a macro)
include("sugarcoating.jl")
export remove_goto, sugared

include("show.jl")

# helper to work with methods
include("methods.jl")
# include("pointer_tracking.jl")

export LazyMethod, getast!, getfunction, isfunction, istype, dependencies!, @lazymethod

end # module

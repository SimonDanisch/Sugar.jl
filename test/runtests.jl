using Sugar
using Base.Test

dir = dirname(@__FILE__)

include("testfunctions.jl")

controlflow_1_cleantypedast = clean_typed(controlflow_1, (Int, Int))
# jeez, lets just test that it doesn't fail doing it.
# TODO test the resulting AST


controlflow_1_cleanast = code_lowered_clean(controlflow_1, (Int, Int))

controlflow_1_ast = open(dir*"/controlflow_1.jls") do io
    deserialize(io)
end
@test controlflow_1_cleanast == controlflow_1_ast

mapping = slot_vector(get_lambda(code_typed, controlflow_1, (Int, Int)))
mapping_expected = [
    (SlotNumber(1),("#self#", typeof(controlflow_1)))
    (SlotNumber(2),("a",Int64))
    (SlotNumber(3),("b",Int64))
    (SlotNumber(4),("x",Int64))
    (SlotNumber(5),("#temp#",Int64))
    (SlotNumber(6),("i",Int64))
    (SlotNumber(7),("#temp#",Int64))
    (SSAValue(0),("ssa_0",UnitRange{Int64}))
    (SSAValue(1),("ssa_1",Tuple{Int64,Int64}))
    (SSAValue(2),("ssa_2",Int64))
    (SSAValue(3),("ssa_3",Int64))
    (SSAValue(4),("ssa_4",Int64))
]

@test mapping == mapping_expected

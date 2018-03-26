using Sugar, Matcha

pat = @ast_pattern begin

     ssa19_ = (Base.sle_int)(from_, to_)
     ssa21_ = (Base.select_value)(ssa19_, to_, 0)
     idx_ = from_

     Label(startlabel_)
     ssa40_ = (Base.add_int)(ssa21_, 1)
     ssa41_ = (idx_ === ssa40_)
     ssa3_ = (Base.not_int)(ssa41_)

     GotoIfNot(ssa3_, endlabel_)

     nextidx_ = (Base.add_int)(idx_, 1)
     idxssa_ = idx_
     idx_ = nextidx_

     body__

     Label(prebody_)
     Goto(startlabel_)
     Label(endlabel_)
end;


function test(n)
    x = 0
    for i = 1:n
        x += i
    end
    x
end



ast = typed_ir(test, Tuple{Int})
matchreplace(ast, pat) do match
    @extract match (idx, from, to, body, idxssa)
    Expr(:for, :($idx in $from : $to), Expr(:block, :($idxssa = $idx), body...))
end


expr_show(x::GlobalRef, io = STDOUT) = print(io, ":($(x.name))")
expr_show(x::Any, io = STDOUT) = show(io, x)
expr_show(x::SlotNumber, io = STDOUT) = print(io, "SlotNumber($(x.id))")
expr_show(x::NewvarNode, io = STDOUT) = print(io, "NewvarNode($(sprint(io-> expr_show(x.slot, io))))")
expr_show(x::GotoNode, io = STDOUT) = print(io, "GotoNode($(x.label))")
expr_show(x::LabelNode, io = STDOUT) = print(io, "LabelNode($(x.label))")
function expr_show(x::Vector, io = STDOUT)
    println(io, "[")
    for elem in x
        print(io, "    ")
        expr_show(elem, io)
        println(io, ",")
    end
    println(io, "]")
end
function expr_show(x::Expr, io = STDOUT)
    if x.head == :return
        print(io, "Expr(:return, ")
    else
        print(io, "Expr(:(", x.head, "), ")
    end
    for elem in x.args
        expr_show(elem, io)
        print(io, ", ")
    end
    print(io, ")")
end
#
#
# pat = @ast_pattern begin
#     ssa0_ = colon(start_, end_)
#     state_ = start(ssa0_)
#
#     $(Label(:startlabel_))
#
#     ssa1_ = done(ssa0_, state_)
#     ssa2_ = typeassert(ssa1_, Bool)
#     ssa3_ = Base.not_int(ssa2_)
#
#     $(GotoIfNot(:ssa3_, :endlabel_))
#
#     ssa4_ = next(ssa0_, state_)
#     idx_ = getfield(ssa4_, 1)
#     state_ = getfield(ssa4_, 2)
#
#     body__
#
#     $(Label(:prebody_))
#     $(Goto(:startlabel_))
#     $(Label(:endlabel_))
# end

struct MTMatchFun
end
function (pat::MTMatchFun)(expr)
    println(expr)
end

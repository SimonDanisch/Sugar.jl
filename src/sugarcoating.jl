is_linenumber(x) = isexpr(x, :line) || isa(x, LineNumberNode)

"""
Replaces `goto` statements in a loop body with continue and break.
"""
function replace_continue_break(astlist, continue_label, break_label)
    map(astlist) do elem
        if isa(elem, GotoNode) && elem.label == continue_label.label
            Expr(:continue)
        elseif isa(elem, GotoNode) && elem.label == break_label.label
            Expr(:break)
        else
            elem
        end
    end
end

"""
Removes all goto/label constructs and puts them back into Julia Expr
"""
function remove_goto(ast)
    ast = matchreplace(ast, goto_neighbours) do goto, label
        # a goto that is directly next to its label can be removed!
        label[1]
    end

    ast = matchreplace(ast, for_pattern) do colon,
            start, loop_label, unless, unused,
            next, body, continue_label,
            goto, break_label
        colonargs = colon[1].args[2].args
        from, to = colonargs[2], colonargs[3]

        condition = unless[1].args[1]
        body = Any[replace_continue_break(collect(body), continue_label[1], break_label[1])...]
        push!(body, continue_label[1])
        body = remove_goto(body)
        # TODO, I guess this will never be removed anyways, so we could just always pop it
        if last(body) == continue_label[1]
            pop!(body)
        end
        # remove getfield of next unitrange
        nextslot = next[1].args[1]
        elem, i = first(body), Base.start(body)
        index = start[1].args[1] # this is index tmp, but might be a good default
        while !Base.done(body, i) && isgetfield(elem, nextslot)
            next_tuple_idx = elem.args[2].args[3]
            if next_tuple_idx == 1 # should be first element
                index = elem.args[1] # this is our real index
            end
            shift!(body)
            elem, _ = Base.next(body, i)
        end
        block = Expr(:block, body...)
        Expr(:for, :($index = $from : $to), block)
    end

    ast = matchreplace(ast, while_pattern) do loop_label, unless, whilebody, continue_label, goto, break_label
        condition = unless[1].args[1]
        whilebody = Any[replace_continue_break(collect(whilebody), continue_label[1], break_label[1])...]
        push!(whilebody, continue_label[1])
        whilebody = remove_goto(whilebody)
        if last(whilebody) == continue_label[1] # TODO, I guess this will never be removed anyways, so we could just always pop it
            pop!(whilebody)
        end
        block = Expr(:block, whilebody...)
        Expr(:while, condition, block)
    end
    ast = matchreplace(ast, ifelse_pattern) do unless, ifbody, _1, _2, elsebody, endlabel
        condition = unless[1].args[1]
        ifbody = Expr(:block, remove_goto(collect(ifbody))...)
        # drop goto end, since we will goto end because of if else branching anyways
        elsebody = filter(elsebody) do x
            !(isgoto(x) && x.label == endlabel[1].label)
        end
        elsebody = Expr(:block, remove_goto(elsebody)...)
        Expr(:if, condition, ifbody, elsebody)
    end
    ast = matchreplace(ast, if_pattern) do unless, body, label...
        condition = unless[1].args[1]
        ifbody = Expr(:block, remove_goto(collect(body))...)
        Expr(:if, condition, ifbody)
    end
    ast
end

"""
Sugared, normalized AST, which basically decompiles the expr list returned by e.g code_typed
"""
function sugared(f, types, stage = code_lowered)
    ast = get_ast(stage, f, types)
    ast = normalize_ast(ast)
    ast = remove_goto(filter(x-> x != nothing && !is_linenumber(x), ast))
    body = Expr(:block)
    append!(body.args, ast)
    body
end

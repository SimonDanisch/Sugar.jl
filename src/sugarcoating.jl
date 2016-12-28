
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
    ast = matchreplace(ast, while_pattern) do loop_label, unless, whilebody, continue_label, goto, break_label
        condition = unless[1].args[1]
        whilebody = replace_continue_break(collect(whilebody), continue_label[1], break_label[1])
        push!(whilebody, continue_label[1])
        whilebody = remove_goto(whilebody)
        if last(whilebody) == continue_label[1] # TODO, I guess this will never be removed anyways, so we could just always pop it
            pop!(whilebody)
        end
        block = Expr(:block, whilebody...)
        Expr(:while, condition, block)
    end
    ast = matchreplace(ast, ifelse_pattern) do unless, ifbody, _1, _2, elsebody, _3
        condition = unless[1].args[1]
        ifbody = Expr(:block, remove_goto(collect(ifbody))...)
        elsebody = Expr(:block, remove_goto(collect(elsebody))...)
        Expr(:if, condition, ifbody, elsebody)
    end
    ast = matchreplace(ast, if_pattern) do unless, body, label
        condition = unless[1].args[1]
        ifbody = Expr(:block, remove_goto(collect(body))...)
        Expr(:if, condition, ifbody)
    end
    ast
end


function sugared(f, types, stage = code_lowered)
    ast = get_ast(stage, f, types)
    ast = normalize_ast(ast)
    ast = remove_goto(filter(x-> x != nothing && !is_linenumber(x), ast))
    body = Expr(:block)
    append!(body.args, ast)
    body
end

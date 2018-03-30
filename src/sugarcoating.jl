is_linenumber(x::ANY) = isexpr(x, :line) || isa(x, LineNumberNode)

const for_pattern = @ast_pattern begin

     Greed(ssa19_ = (Base.sle_int)(from_, to1_), 0:1)
     Greed(ssa212_ = (Base.sub_int)(from_, 1), 0:1) # this is optional and doesn't happen for `for i in 1:n`
     Greed(to_ = (Base.select_value)(ssa19_, to1_, ssa212_), 0:1)

     idx_ = from_
     Label(startlabel_)
     ssa40_ = (Base.add_int)(to_, 1)
     ssa41_ = (idx_ === ssa40_)
     ssa3_ = (Base.not_int)(ssa41_)

     GotoIfNot(ssa3_, endlabel_)

     nextidx_ = (Base.add_int)(idx_, 1)
     idxssa_ = idx_
     idx_ = nextidx_

     body__

     Greed(Label(continuelabel_), 0:1) # continue break label, which is optional
     Goto(startlabel_)
     Label(endlabel_)
end

const while_pattern = @ast_pattern begin
    Label(start_)
    whilesetup__
    GotoIfNot(condition_, endlabel_)

    body__

    Greed(Label(continuelabel_), 0:1)
    Goto(start_)
    Label(endlabel_)
end

const ifelse_pattern = @ast_pattern begin
    GotoIfNot(condition_, elselabel_)
    ifbody__
    Goto(endlabel_)
    Label(elselabel_)
    elsebody__
    Label(endlabel_)
end

const if_pattern = @ast_pattern begin
    GotoIfNot(condition_, endlabel_)
    body__
    Greed(Label(endlabel_), 0:1)
end


"""
Replaces `goto` statements in a loop body with continue and break.
"""
function replace_continue_break(astlist, continue_label, break_label)
    map(astlist) do elem
        if isa(elem, GotoNode) && elem.label == continue_label
            Expr(:continue)
        elseif isa(elem, GotoNode) && elem.label == break_label
            Expr(:break)
        else
            elem
        end
    end
end

# The matched body comes as a view, with which remove_goto doesn't work right now (should be possible though)
_remove_goto(x) = remove_goto(collect(x))

function replace_for(ast)
    matchreplace(ast, for_pattern) do match
        @extract match (idx, from, to, body, idxssa, endlabel)
        haskey(match, :to1) && (to = match[:to1])
        if haskey(match, :continuelabel)
            body = replace_continue_break(collect(body), match[:continuelabel], endlabel)
        end
        Expr(:for, :($idx in $from : $to), Expr(:block, :($idxssa = $idx), _remove_goto(body)...))
    end
end
function replace_while(ast)
    matchreplace(ast, while_pattern) do match
        @extract match (condition, whilesetup, body, endlabel)
        if haskey(match, :continuelabel)
            body = replace_continue_break(collect(body), match[:continuelabel], endlabel)
        end
        Expr(:while, condition, Expr(:block, whilesetup..., _remove_goto(body)...))
    end
end
function replace_if(ast)
    matchreplace(ast, if_pattern) do match
        @extract match (condition, body)
        Expr(:if, condition, Expr(:block, _remove_goto(body)...))
    end
end
function replace_ifelse(ast)
    matchreplace(ast, ifelse_pattern) do match
        @extract match (condition, ifbody, elsebody)
        Expr(:if, condition, Expr(:block, _remove_goto(ifbody)...), Expr(:block, _remove_goto(elsebody)...))
    end
end

"""
Removes all goto/label constructs and puts them back into Julia Expr
"""
function remove_goto(ast)
    ast |> replace_for |> replace_while |> replace_ifelse |> replace_if
end


remove_invoke(arg::Vector) = (map!(remove_invoke, arg, arg); arg)
function remove_invoke(arg)
    Meta.isexpr(arg, :(=)) && return (arg.args .= remove_invoke.(arg.args); arg)
    Meta.isexpr(arg, :invoke) && return Expr(:call, arg.args[2:end]...)
    arg
end

"""
Sugared, normalized AST, which basically decompiles the expr list returned by e.g code_typed
"""
function sugared(f, types)
    ast = typed_ir(f, types)
    body = Expr(:block)
    append!(body.args, ast |> remove_invoke |> remove_goto)
    body
end

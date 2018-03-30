
function show_expr(state, io, ssa::SSAValue, indent::Int, prec::Int)
    print(io, "ssa_", ssa.id)
end
function show_expr(state, io, slot::Slot, indent::Int, prec::Int)
    print(io, "slot_", slot.id)
end

show_expr(state, io, ex) = show_expr(state, io, ex, 0, -1)
show_expr(state, io, ex, indent::Int, prec::Int) = print(io, ex)

function show_extendable(state, io, ::Val{HEAD}, ex::Expr, indent::Int, prec::Int) where HEAD
    error("Unsupported expression found. Head: $(ex.head): $ex")
end

function show_expr(state, io, ex::Expr, indent::Int, prec::Int)
    head, args, nargs = ex.head, ex.args, length(ex.args)

    (head == :call) && return show_call(state, io, args[1], args[2:end], indent, prec)

    (@capture ex a_ = b_) && return show_assignment(state, io, a, b, indent, prec)

    if head in (:while, :function, :if) && nargs == 2
        return print_block(state, io, head, args[1:1], args[2], indent)
    end

    if (head == :if) && nargs == 3     # if/else
        return show_ifelse(state, io, args[1], args[2], args[3], indent)
    end

    if head == :for
        for_header = args[1]
        return show_for(state, io, for_header.args[2], for_header.args[3].args[2:end]..., args[2], indent)
    end

    (nargs == 0 && head in (:break, :continue)) && return print(io, head)

    head == :block && return print_block(state, io, "", (), ex, indent)

    head == :new && return show_constructor(state, io, args[1], args[2:end])

    head == :return && return show_return(state, io, args)

    # TODO, just ignore this? Log this? We definitely don't need it in the transpiler
    (head in (:meta, :inbounds, :boundscheck)) && return

    return show_extendable(state, io, Val(head), ex, indent, prec)
end

function_symbol(f::GlobalRef) = f.name
function_symbol(f::Symbol) = f

function function_name(state, f, args)
    fsym = function_symbol(f)
    get(intrinsic_table_syms, fsym, fsym)
end

# show an indented list
function show_list(state, io::IO, items, sep, indent::Int, prec::Int=0, enclose_operators::Bool=false)
    n = length(items)
    n == 0 && return
    indent += 4
    first = true
    for item in items
        !first && print(io, sep)
        parens = !Base.is_quoted(item) &&
            (first && prec >= Base.prec_power &&
             ((item isa Expr && item.head === :call && item.args[1] in uni_ops) ||
              (item isa Real && item < 0))) ||
              (enclose_operators && item isa Symbol && Base.isoperator(item))
        parens && print(io, '(')
        show_expr(state, io, item, indent, parens ? 0 : prec)
        parens && print(io, ')')
        first = false
    end
end
# show an indented list inside the parens (op, cl)
function show_enclosed_list(state, io::IO, op, items, sep, cl, indent, prec=0, encl_ops=false)
    print(io, op)
    show_list(state, io, items, sep, indent, prec, encl_ops)
    print(io, cl)
end

slotnames(x::Core.CodeInfo) = x.slotnames
function replace_vars(state, x::String)
    slots = slotnames(state)
    for (i, slot) in enumerate(slots)
        x = replace(x, string(slot) => "slot_$i")
    end
    x
end

function show_call(state, io, f, args, indent, prec)
    fname = function_name(state, f, args)
    fname == :inline_opencl && return print(io, replace_vars(state, args[1]))
    func_prec = Base.operator_precedence(fname)
    if func_prec > 0 # is a binary operator
        na = length(args)
        if (na == 2 || (na > 2 && fname in (:+, :++, :*)))
            sep = " $fname "
            if func_prec <= prec
                show_enclosed_list(state, io, '(', args, sep, ')', indent, func_prec, true)
            else
                show_list(state, io, args, sep, indent, func_prec, true)
            end
            return
        elseif na == 1
            # 1-argument call to normally-binary operator
            print(io, fname)
            return show_enclosed_list(state, io, '(', args, ",", ')', indent)
        end
    end
    print(io, fname)
    show_enclosed_list(state, io, '(', args, ", ", ')', indent)
end

function show_for(state, io::IO, idx, from, to, body, indent)
    print(io, "for(")
    show_expr(state, io, idx)
    print(io, " = ")
    show_expr(state, io, from)
    print(io, "; ")
    show_expr(state, io, idx)
    print(io, " <= ")
    show_expr(state, io, to)
    print(io, "; ")
    show_expr(state, io, idx)
    print(io, "++)")
    print_block(state, io, "", (), body, indent)
end

function show_constructor(state, io, typ, args, indent)
    print(io, '(')
    show_expr(state, io, typ)
    print(io, ')')
    show_enclosed_list(io, '{', args, ',', '}', indent, -1, true)
end

function show_return(state, io, args)
    if length(args) == 1
        if args[1] != nothing
            if !(isa(args[1], Expr) && (args[1].typ == Void))
                # if returns void, we need to omit the return statement
                print(io, "return ")
            end
            show_expr(state, io, args[1])
        end
    else
        # ignore if empty, otherwise, LOL? What's a return with multiple args?
        if isempty(args)
            print(io, "return")
        else
            error("Unknown return Expr: $ex")
        end
    end
end

scope_delimiters(state) = ('{', '}')
list_delims(state) = ('(', ')')
block_seperator(state) = ';'

# show a block, e g if/for/etc
function print_block(state, io::IO, head, args, body, indent::Int)
    # everything empty, let's not make a fool of ourselves and print something
    isempty(args) && isa(body, Expr) && isempty(body.args) && return
    if isempty(args)
        print(io, head, scope_delimiters(state)[1])
    else
        print(io, head, list_delims(state)[1])
        show_list(state, io, args, ", ", indent)
        print(io, list_delims(state)[2], scope_delimiters(state)[1])
    end
    ind = indent + 4
    exs = Meta.isexpr(body, :block) ? body.args : Any[body]
    for (i, ex) in enumerate(exs)
        sep = i == 1 ? "" : block_seperator(state)
        print(io, sep, '\n', " "^ind)
        show_expr(state, io, ex, ind, -1)
    end
    print(io, block_seperator(state), "\n", " "^indent, scope_delimiters(state)[2], "\n")

end

function assign_variable(state, io, a)
    T = expr_type(state, a)
    show_expr(io, T, indent, prec)
    print(io, " ")
    show_expr(io, a, indent, prec)
    println(io, block_seperator(state))
end

is_assigned(x, y) = true

function show_assignment(state, io, a, b, indent, prec)
    is_assigned(state, a) || assign_variable(state, io, a)
    show_expr(state, io, a, indent, prec)
    print(io, " = ")
    show_expr(state, io, b, indent, prec)
end

function show_ifelse(state, io, condition, ifbody, elsebody, indent)
    print_block(state, io, :if, (condition,), ifbody, indent)
    print_block(state, io, :else, (), elsebody, indent)
end

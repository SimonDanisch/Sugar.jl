using Revise
using Sugar, Matcha



function ifelse_func(x)
    if x == 1
        println("heelo")
    else
        println("yo?")
    end
    return nothing
end
function if_func(x)
    if x == 1
        println("heelo")
    end
    return nothing
end

function whilefunc(x)
    while x > 3
        x -= 1
        println("o")
    end
    return nothing
end




function test_apply(x...)
    +(x...)
end
function test_apply(x::T...) where T
    (+(x...))::T
end

function test()
    x = 0
    for i = 1:3
        x += i
    end
    x
end
function test(n)
    x = 0
    for i = 1:n
        x += i
    end
    x
end

function test(a, n)
    x = 0
    for i = a:n
        x += i
        x = x + 2
    end
    x
end
function test2(a, n)
    x = 0
    for i = a:n
        x += i
        if i == 2
            x = x + 2
        end
    end
    x
end
function test3(a, n)
    x = 0
    for i = a:n
        x += i
        i == 2 && (x += 2)
    end
    x
end
function test4(a, n)
    x = 0
    for i = a:n
        x += i
        i == 2 && (x += 2)
        x += 2
    end
    x
end
function test5(a, n)
    x = 0
    for i = a:n
        x += i
        if i == 1
            x += 2
        else
            x += 3
        end
        x += 2
    end
    x
end



ast = typed_ir(test, Tuple{});
x = matchreplace(ast, pat) do match
    @extract match (idx, from, to, body, idxssa)
    Expr(:for, :($idx in $from : $to), Expr(:block, :($idxssa = $idx), body...))
end;
Expr(:block, x...)

ast = typed_ir(test, Tuple{Int, Int})
x = matchreplace(ast, pat) do match
    @extract match (idx, from, to, body, idxssa)
    Expr(:for, :($idx in $from : $to), Expr(:block, :($idxssa = $idx), body...))
end;
Expr(:block, x...);
for func in (test2, test3, test4, test5)
    ast = typed_ir(test2, Tuple{Int, Int})
    x = matchreplace(ast, pat) do match
        @extract match (idx, from, to, body, idxssa)
        if haskey(match.env, :to1)
            to = match.env[:to1]
        end
        Expr(:for, :($idx in $from : $to), Expr(:block, :($idxssa = $idx), body...))
    end
    println(Expr(:block, x...))
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


using Matcha
using Sugar: Slurp, MTMatchFun

x = [
    :(a = 22),
    :(a + 10)
]
matchat(x, (Greed(Sugar.Slurp(:body)), Greed(MTMatchFun(:(a_ + b_)), 0:1)))

# helper function to fake a return type to type inference for intrinsic function stabs
@noinline function ret{T}(::Type{T})::T
    unsafe_load(Ptr{T}(C_NULL))
end
@noinline function inline_opencl(x, ::Type{T}) where T
    unsafe_load(Ptr{T}(C_NULL))
end

@inline get_num_groups(dim::Integer) = inline_opencl("get_num_groups(dim)", Cuint)


function test(x, i)
    get_num_groups(0)
end

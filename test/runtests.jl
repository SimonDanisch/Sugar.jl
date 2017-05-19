using Sugar, MacroTools, Base.Test
using Base.Test
import Sugar: @lazymethod

function controlflow_1(a, b)
    if a == 10
        x = if b == 22
            7
        else
            8
        end
        for i = 1:100
            x += i
            x -= 77
            i == 77 && continue
            if i == 99 && (i % 2 == 0)
                break
            end
        end
        return x
    else
        return 77
    end
end

method = Sugar.LazyMethod((controlflow_1, (Int, Int)))
func_expr = Sugar.get_func_expr(method, gensym(:controlflow_1))
round_tripped = eval(func_expr)
srand()
for i = 1:1000
    x, y = rand(-5000:5000), rand(-5000:5000)
    @test round_tripped(1, 2) == controlflow_1(1, 2)
end

decl = @lazymethod controlflow_1(1, 2)

ast = Sugar.getast!(decl)
needsnotype = (:block, :if, :(=), :while, :return, :continue, :break, :for, :(:))
@testset "ast rewriting and normalization" begin
    MacroTools.prewalk(ast) do expr
        if isa(expr, Expr)
            if !(expr.head in needsnotype)
                # there shouldn't be any untyped expressions in the AST
                if expr.typ == Any
                    show(expr.head)
                end
                @test expr.typ != Any
            end
            if expr.head == :call
                f = expr.args[1]
                # all function calls should get replaced by the real function
                @test isa(f, Function)
            end
        end
        expr
    end
end
# The dependencies and implementation on 0.6 have changed quite a bit...
# TODO add a `pure` example, which doesn't rely on implementations of base!
deps = Sugar.dependencies!(decl, true)

@testset "method dependencies" begin
    deps = Sugar.dependencies!(decl, true)
    deps_test = [
        Bool,
        Int,
        (==, Tuple{Int64,Int64}),
        (+, Tuple{Int,Int}),
        (-, Tuple{Int,Int}),
        (rem, Tuple{Int,Int}),
    ]
    @test length(deps) == length(deps_test)
    @test all(x-> x.signature in deps_test, deps)
    funcs = [
        (==,Tuple{Int64,Int64}),
        (+,Tuple{Int, Int}),
        (-,Tuple{Int, Int}),
        (rem, Tuple{Int,Int}),
    ]
    funcdeps = filter(Sugar.isfunction, deps)
    @test length(funcdeps) == length(funcs)
    @test all(x-> x.signature in funcs, funcdeps)
    types = [
        Int64,
        Bool
    ]
    typedeps = filter(Sugar.istype, deps)
    @test length(typedeps) == length(types)
    @test all(x-> x.signature in types, typedeps)
end

function fortest(x)
    acc = x
    for i = 1:5
        if i == 1
            acc += x
        elseif i == 2
            acc -= x
        else
            acc += x * x
        end
    end
    return acc
end

decl = Sugar.@lazymethod fortest(1f0)
ast = Sugar.getast!(decl)
function typed_expr(head, typ, args...)
    expr = Expr(head, args...)
    expr.typ = typ
    expr
end
ast_target = []
push!(ast_target, typed_expr(:(::), Int, :i, Int))
push!(ast_target, typed_expr(:(::), Int, :xxtempx4, Int))
push!(ast_target, typed_expr(:(::), Float32, :acc, Float32))
sloti, slotx, slotacc = if VERSION < v"0.6.0-dev"
    SlotNumber(5), SlotNumber(2), SlotNumber(3)
else
    # slotnumbers seem to have changed.. besides in testing, this shouldn't be a problem!
    reverse!(ast_target)
    SlotNumber(3), SlotNumber(2), SlotNumber(5)
end

push!(ast_target, :($slotacc = $slotx))
for_loop = Expr(:for)

push!(for_loop.args, :($sloti = 1:5))
forbody = Expr(:block)
push!(for_loop.args, forbody)
# if else
call = typed_expr(:call, Float32, +, slotacc, slotx)
firstif = Expr(:if,
    typed_expr(:call, Bool, ==, sloti, 1),
    Expr(:block,
        :($(slotacc) = $call),
        Expr(:continue)
    )
)
push!(forbody.args, firstif)
call = typed_expr(:call, Float32, -, slotacc, slotx)
secondif = Expr(:if,
    typed_expr(:call, Bool, ==, sloti, 2),
    Expr(:block,
        :($(slotacc) = $call),
        Expr(:continue)
    )
)
push!(forbody.args, secondif)
call1 = typed_expr(:call, Float32, *, slotx, slotx)
call = typed_expr(:call, Float32, +, slotacc, call1)
push!(forbody.args, :($(slotacc) = $call))

push!(ast_target, for_loop)
push!(ast_target, :(return $(slotacc)))
target_expr = typed_expr(:block, Float32, ast_target...)

@testset "for + ifelse" begin
    @test target_expr == ast
end

function test1(a, b)
    c = a + b
    a == c && (c = a)
    c
end
function test2(a, b)
    c = a + b
    if a == c
        c = a
    end
    c
end
ast1 = Sugar.sugared(test1, (Int, Int), code_lowered)
ast2 = Sugar.sugared(test2, (Int, Int), code_lowered)
@test ast1 == ast2

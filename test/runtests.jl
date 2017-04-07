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
            if i == 77
                continue
            elseif i == 99
                break
            end
        end
        return x
    else
        return 77
    end
end

ast = Sugar.sugared(controlflow_1, (Int, Int), code_lowered)
# serialization doesn't work between julia versions,
# and it'd be annoying to rely on e.g. JLD/JSON (maybe reasonable, though)
ast2 = if VERSION < v"0.6.0-dev"
    open(deserialize, joinpath(dirname(@__FILE__), "controlflow_05.jls"))
else
    open(deserialize, joinpath(dirname(@__FILE__), "controlflow_06.jls"))
end

@test ast == ast2

decl = @lazymethod controlflow_1(1, 2)

ast = Sugar.getast!(decl)
needsnotype = (:block, :if, :(=), :while, :return, :continue, :break, :for, :(:))
@testset "ast rewriting and normalization" begin
    MacroTools.prewalk(ast) do expr
        if isa(expr, Expr)
            if !(expr.head in needsnotype)
                # there shouldn't be any untyped expressions in the AST
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
        Int,
        (==,Tuple{Int64,Int64}),
        (+,Tuple{Int,Int}),
        (-,Tuple{Int,Int}),
    ]
    @test length(deps) == length(deps_test)
    @test all(x-> x.signature in deps_test, deps)
    funcs = [
        (==,Tuple{Int64,Int64}),
        (+,Tuple{Int, Int}),
        (-,Tuple{Int, Int}),
    ]
    funcdeps = filter(Sugar.isfunction, deps)
    @test length(funcdeps) == length(funcs)
    @test all(x-> x.signature in funcs, funcdeps)
    types = [
        Int64,
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
push!(ast_target, :($(SlotNumber(3)) = $(SlotNumber(2))))
for_loop = Expr(:for)

push!(for_loop.args, :($(SlotNumber(4)) = 1:5))
forbody = Expr(:block)
push!(for_loop.args, forbody)
# if else
call = typed_expr(:call, Float32, +, SlotNumber(3), SlotNumber(2))
firstif = Expr(:if,
    typed_expr(:call, Bool, ==, SlotNumber(5), 1),
    Expr(:block,
        :($(SlotNumber(3)) = $call),
        Expr(:continue)
    )
)
push!(forbody.args, firstif)
call = typed_expr(:call, Float32, -, SlotNumber(3), SlotNumber(2))
secondif = Expr(:if,
    typed_expr(:call, Bool, ==, SlotNumber(5), 2),
    Expr(:block,
        :($(SlotNumber(3)) = $call),
        Expr(:continue)
    )
)
push!(forbody.args, secondif)
call1 = typed_expr(:call, Float32, *, SlotNumber(2), SlotNumber(2))
call = typed_expr(:call, Float32, +, SlotNumber(3), call1)
push!(forbody.args, :($(SlotNumber(3)) = $call))

push!(ast_target, for_loop)
push!(ast_target, :(return $(SlotNumber(3))))
target_expr = typed_expr(:block, Float32, ast_target...)

@testset "for + ifelse" begin
    @test target_expr == ast
end

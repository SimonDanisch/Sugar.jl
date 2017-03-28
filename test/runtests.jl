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
needsnotype = (:block, :if, :(=), :while, :return, :continue, :break)
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

if VERSION < v"0.6.0-dev"
    @testset "method dependencies" begin
        deps = Sugar.dependencies!(decl, true)
        @test length(deps) == 23
        deps_test = [
            Int64,
            (==,Tuple{Int64,Int64}),
            UnitRange{Int64},
            (colon,Tuple{Int64,Int64}),
            (start,Tuple{UnitRange{Int64}}),
            (!, Tuple{Bool}),
            (done,Tuple{UnitRange{Int64},Int64}),
            Tuple{Int64,Int64},
            (next,Tuple{UnitRange{Int64},Int64}),
            (getfield,Tuple{Tuple{Int64,Int64},Int64}),
            (+,Tuple{Int64,Int64}),
            (-,Tuple{Int64,Int64}),
            (UnitRange{Int64},Tuple{Int64,Int64}),
            (Base.unitrange_last,Tuple{Int64,Int64}),
            (ifelse,Tuple{Bool,Int64,Int64}),
            (>=,Tuple{Int64,Int64}),
            (<=,Tuple{Int64,Int64}),
            (one,Tuple{Int64}),
            Type{Int64},
            Bool,
            (oftype,Tuple{Int64,Int64}),
            (convert,Tuple{Type{Int64},Int64}),
            (one,Tuple{Type{Int64}})
        ]
        @test all(x-> x.signature in deps_test, deps)
        funcs = [
            (==,Tuple{Int64,Int64}),
            (colon,Tuple{Int64,Int64}),
            (start,Tuple{UnitRange{Int64}}),
            (!, Tuple{Bool}),
            (done,Tuple{UnitRange{Int64},Int64}),
            (next,Tuple{UnitRange{Int64},Int64}),
            (getfield,Tuple{Tuple{Int64,Int64},Int64}),
            (+,Tuple{Int64,Int64}),
            (-,Tuple{Int64,Int64}),
            (UnitRange{Int64},Tuple{Int64,Int64}),
            (Base.unitrange_last,Tuple{Int64,Int64}),
            (ifelse,Tuple{Bool,Int64,Int64}),
            (>=,Tuple{Int64,Int64}),
            (<=,Tuple{Int64,Int64}),
            (one,Tuple{Int64}),
            (oftype,Tuple{Int64,Int64}),
            (convert,Tuple{Type{Int64},Int64}),
            (one,Tuple{Type{Int64}})
        ]
        funcdeps = filter(Sugar.isfunction, deps)
        @test length(funcdeps) == length(funcs)
        @test all(x-> x.signature in funcs, funcdeps)
        types = [
            Int64,
            UnitRange{Int64},
            Tuple{Int64,Int64},
            Type{Int64},
            Bool,
        ]
        typedeps = filter(Sugar.istype, deps)
        @test length(typedeps) == length(types)
        @test all(x-> x.signature in types, typedeps)
    end
else
    @testset "method dependencies" begin
        deps = Sugar.dependencies!(decl, true)
        deps_test = [
            Int64,
            (==, Tuple{Int64,Int64}),
            UnitRange{Int64},
            (colon, Tuple{Int64,Int64}),
            (start, Tuple{UnitRange{Int64}}),
            (!, Tuple{Bool}),
            (done, Tuple{UnitRange{Int64},Int64}),
            Tuple{Int64,Int64},
            (next, Tuple{UnitRange{Int64},Int64}),
            (getfield, Tuple{Tuple{Int64,Int64},Int64}),
            (+, Tuple{Int64,Int64}),
            (-, Tuple{Int64,Int64}),
            (UnitRange{Int64}, Tuple{Int64,Int64}),
            (Base.unitrange_last, Tuple{Int64,Int64}),
            (ifelse, Tuple{Bool,Int64,Int64}),
            (>=, Tuple{Int64,Int64}),
            (<=, Tuple{Int64,Int64}),
            (oneunit, Tuple{Int64}),
            (one, Tuple{Int64}),
            (Int64, Tuple{Int64}),
            (one, Tuple{Type{Int64}}),
            Bool,
            (oftype, Tuple{Int64,Int64}),
            (convert, Tuple{Type{Int64},Int64}),
            (oneunit, Tuple{Type{Int64}}),
        ]
        @test length(deps_test) == length(deps)
        @test all(x-> x.signature in deps_test, deps)
        funcs = [
            (==, Tuple{Int64,Int64}),
            (colon, Tuple{Int64,Int64}),
            (start, Tuple{UnitRange{Int64}}),
            (!, Tuple{Bool}),
            (done, Tuple{UnitRange{Int64},Int64}),
            (next, Tuple{UnitRange{Int64},Int64}),
            (getfield, Tuple{Tuple{Int64,Int64},Int64}),
            (+, Tuple{Int64,Int64}),
            (-, Tuple{Int64,Int64}),
            (UnitRange{Int64}, Tuple{Int64,Int64}),
            (Base.unitrange_last, Tuple{Int64,Int64}),
            (ifelse, Tuple{Bool,Int64,Int64}),
            (>=, Tuple{Int64,Int64}),
            (<=, Tuple{Int64,Int64}),
            (oneunit, Tuple{Int64}),
            (one, Tuple{Int64}),
            (Int64, Tuple{Int64}),
            (one, Tuple{Type{Int64}}),
            (oftype, Tuple{Int64,Int64}),
            (convert, Tuple{Type{Int64},Int64}),
            (oneunit, Tuple{Type{Int64}}),
        ]
        funcdeps = filter(Sugar.isfunction, deps)
        @test length(funcdeps) == length(funcs)
        @test all(x-> x.signature in funcs, funcdeps)
        types = [
            Int64,
            UnitRange{Int64},
            Tuple{Int64,Int64},
            Bool
        ]
        typedeps = filter(Sugar.istype, deps)
        @test length(typedeps) == length(types)
        @test all(x-> x.signature in types, typedeps)
    end
end

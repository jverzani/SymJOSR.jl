using Test, SymJ, SymJOSR

const S = SymJOSR
@syms x a b c d m

# d/dx F == f, numerically
function isantiderivative(F, f)
    F === nothing && return false
    all(1:3) do _
        ps = [s => Sym(rand(3:17) // 10) for s in (x, a, b, c, d, m)]
        abs(N(subs(diff(F, x) - f, ps...))) < 1e-9
    end
end

@testset "patterns" begin
    @test S.pat("a_") == :(~a)
    @test S.pat("a.") == :(~!a)
    @test S.pat("x_") == S.XNAME
    p = SymJ.pattern(S.pat(Any["Power", Any["Add", "a.", Any["Multiply", "b.", "x_"]], "m."]))
    X = S.X
    @test match(p, X)[:b] == 1
    @test match(p, (2X + 3)^5)[:m] == 5
end

@testset "predicates" begin
    F = S.FUNCS
    X = S.X
    @test F["FreeQ"](Any[a, b], X)
    @test !F["FreeQ"](a * X, X)
    @test F["EqQ"](a * (b + c), a * b + a * c)
    @test F["IGtQ"](Sym(3), Sym(0)) && !F["IGtQ"](Sym(1) // 2, Sym(0))
    @test F["GtQ"](sqrt(Sym(2)), Sym(1)) && !F["GtQ"](a, Sym(0))
    @test F["PosQ"](Sym(2)) && !F["PosQ"](-a) && F["NegQ"](-Sym(3))
    @test F["LinearQ"](a + b * X, X) && !F["LinearQ"](X^2, X)
    @test F["PolyQ"](X^3 + a, X, Sym(3))
    @test F["SumSimplerQ"](Sym(-2), Sym(1)) == (-2 < -1)
end

# the rules come from SYMJOSR_INTEGRATION_DIR or a download
@testset "integration" begin
    R = S.load_rules()
    @test length(R.rules) > 4000
    for f in (x^2, (a + b * x)^3, 1 / (a + b * x), (a + b * x)^m, sqrt(a + b * x),
              1 / ((a + b * x) * (c + d * x)), x * (a + b * x)^5)
        @test isantiderivative(S.integrate(f, x; rules = R), f)
    end
    r = S.integrate((a + b * x)^3, x; rules = R, trace = true)
    @test !isempty(r.steps)
end

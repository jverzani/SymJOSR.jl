# SymJ before Test: on Julia 1.12, with Test loaded first, compiling SymJ code (as
# building a pattern) runs for many minutes; in this order it takes seconds
using SymJ, SymJOSR
using Test

const S = SymJOSR
@syms x a b c d m

# d/dx F == f, numerically (as the test problems are checked: repeatable points, away
# from singularities such as a d = b c)
isantiderivative(F, f) = F !== nothing && S._verify(subs(F, x => S.X), subs(f, x => S.X))

@testset "patterns" begin
    @test S.pat("a_") == :(~a)
    @test S.pat("a.") == :(~!a)
    @test S.pat("x_") == S.XNAME
    p = SymJ.pattern(S.pat(Any["Power", Any["Add", "a.", Any["Multiply", "b.", "x_"]], "m."]))
    X = S.X
    @test match(p, X)[:b] == 1
    @test match(p, (2X + 3)^5)[:m] == 5
    @test match(p, c + d) === nothing     # as in Mathematica, the term b x is required
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
    # PolyQ[u, x^n]: a polynomial in x with only powers of x^n, as RUBI
    @test F["PolyQ"](3 + a * X^4, X^2) && !F["PolyQ"](3 + X^3, X^2)
    @test !F["PolyQ"]((1 + a * X) / (1 - a * X), X^2)
    @test F["PolyQ"](1 + X^m, X^m) && !F["PolyQ"](1 + X^m + X, X^m)
    @test F["SumSimplerQ"](Sym(-2), Sym(1)) == (-2 < -1)
    # as RUBI's N[Together[u]]: b/(b c' - a d') is 1 for the c', d' of 1.1.1.2 #32
    cc, dd = b * c / (b * c - a * d), b * d / (b * c - a * d)
    @test F["GtQ"](b / (b * cc - a * dd), Sym(0))
    # EqQ of rational expressions over a common denominator
    @test F["EqQ"]((a^2 - b^2) / (a - b), a + b) && !F["EqQ"](b * c - a * d, 0)
end

@testset "structural predicates" begin
    F = S.FUNCS
    X = S.X
    @test F["LinearMatchQ"](a + b * X, X) && F["LinearMatchQ"](X, X) && !F["LinearMatchQ"](a, X)
    @test !F["LinearMatchQ"](c * (a + b * X), X)          # syntactic, as RUBI's MatchQ
    @test F["LinearMatchQ"](Any[a + X, 2X], X)
    @test F["QuadraticMatchQ"](a + c * X^2, X) && !F["QuadraticMatchQ"](a + b * X, X)
    @test F["BinomialMatchQ"](a + b * X^m, X) && !F["BinomialMatchQ"](a + b * X + c * X^2, X)
    @test F["BinomialQ"](a + b / X^2, X) && F["BinomialQ"](a + b * X^3, X, Sym(3)) && !F["BinomialQ"](X^2 + X, X)
    @test !F["BinomialQ"]((X + 1) * (X^2 + 2), X)      # (a product without a constant factor)
    @test F["RationalFunctionQ"]((X + 1) / (X^2 + a), X) && !F["RationalFunctionQ"](sqrt(X), X)
    @test F["LinearPairQ"](2X + 2, X + 1, X)
    @test F["IntBinomialQ"](a, b, c, Sym(3), Sym(1 // 2), Sym(2), X)
    @test F["IntBinomialQ"](a, b, c, d, Sym(3), Sym(-1 // 3), Sym(1), X)
    @test !F["IntBinomialQ"](a, b, c, d, Sym(3), Sym(1 // 5), Sym(1 // 7), X)
    @test F["PolynomialQuotient"](1 - X^4, 1 + X + X^2 + X^3, X) == 1 - X
    @test F["PolynomialRemainder"](X^2 + 1, X + 1, X) == 2
    # P(x) (c + d x)^n as powers of c + d x (RUBI's ExpandLinearProduct)
    e = F["ExpandIntegrand"](X^3 * sqrt(a + b * X), X)
    @test e.kind == SymJ.ADD && iszero(simplify(e - X^3 * sqrt(a + b * X)))
end

# the rules come from SYMJOSR_INTEGRATION_DIR or a download
@testset "integration" begin
    R = S.load_rules()
    @test length(R.rules) > 4000
    # the host rules' keys are rule files' names (with /, on Windows too)
    @test all(in(S.rule_files()), keys(S.HOST_RULES))
    for f in (x^2, (a + b * x)^3, 1 / (a + b * x), (a + b * x)^m, sqrt(a + b * x),
              1 / ((a + b * x) * (c + d * x)), x * (a + b * x)^5)
        @test isantiderivative(S.integrate(f, x; rules = R), f)
    end
    # reached a cycle at MAXDEPTH: a step that hands an integrand back is now rejected,
    # and another rule applies (1.1.1.2 #399)
    f = x^2 / (a + b * x)^(1 // 3)
    @test isantiderivative(S.integrate(f, x; rules = R), f)
    # looped through 1.1.1.2 #32 until the timeout (1.1.1.2 #1514)
    f = (a + b * x)^(7 // 2) * sqrt(c + d * x)
    @test isantiderivative(S.integrate(f, x; rules = R), f)
    r = S.integrate((a + b * x)^3, x; rules = R, trace = true)
    @test !isempty(r.steps)
end

@testset "verify" begin
    X = S.X
    # singular at x = 1, which the points avoid
    f = 1 / ((1 - X)^(3 // 2) * sqrt(1 + X))
    @test S._verify(sqrt(X + 1) / sqrt(1 - X), f)
    @test !S._verify(sqrt(X + 1) / sqrt(1 - X) + X, f)
    # a ₂F₁ whose argument, b x/a + 1, is on the branch cut for positive values (1.1.1.2 #294)
    F = SymJ.apply_function(:_₂F₁, Sym[Sym(1), Sym(3 // 2), Sym(5 // 2), b * X / a + 1])
    r = -2 * F * (a + b * X)^(3 // 2) / (3a)
    f = sqrt(a + b * X) / X
    @test S._verify(r, f)
    @test all(_ -> S._verify(r, f), 1:3) && !S._verify(2r, f)
end

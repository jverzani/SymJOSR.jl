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
    # trig: functions as values, and the forms RUBI's trig rules know
    @test F["TrigQ"](sin) && !F["TrigQ"](sinh) && F["HyperbolicQ"](cosh)
    @test F["InverseFunctionFreeQ"](log(a) * X, X) && !F["InverseFunctionFreeQ"](log(X) * X, X)
    @test F["KnownSineIntegrandQ"]((a + b * sin(c + d * X))^m, X)
    @test F["KnownSineIntegrandQ"](a + b * cos(X) + c * cos(X)^2, X)
    @test !F["KnownSineIntegrandQ"](X * sin(X), X) && !F["KnownSineIntegrandQ"](tan(X), X)
    @test F["KnownTangentIntegrandQ"](tan(X)^3, X)
    # MatchQ[u, Condition[pattern, test]] in constraints: some match passes the test,
    # with its bindings and the rule's (Not[MatchQ[Pq, x^m. u. /; IntegerQ[m]]])
    spec = Any["Condition", Any["Multiply", Any["Power", "x", "m."], "u."], Any["IntegerQ", "m"]]
    mq(u) = S.SPECIAL["MatchQ"](Any["Pq", spec], S.Ctx(Dict{Symbol,Any}(:Pq => u), 0))
    @test mq(X^2 * (1 + X)) && mq(3X^5) && !mq(1 + X) && !mq(sqrt(X) * (1 + X))
    spec2 = Any["Condition", Any["Power", "x", "n_"], Any["EqQ", "n", "k"]]
    @test S.SPECIAL["MatchQ"](Any["v", spec2], S.Ctx(Dict{Symbol,Any}(:v => X^3, :k => Sym(3)), 0))
    @test !S.SPECIAL["MatchQ"](Any["v", spec2], S.Ctx(Dict{Symbol,Any}(:v => X^3, :k => Sym(2)), 0))
    # SubstFor, FunctionOfQ (FunctionOfExpnQ) for v that is not a trig function
    @test F["SubstFor"](X^2, 3 + a * X^2 + c * X^4, X) == 3 + a * X + c * X^2
    @test F["SubstFor"](a + b * X, X, X) == (X - a) / b
    @test F["FunctionOfQ"](X^2, 1 + X^4, X) && !F["FunctionOfQ"](X^2, 1 + X^3, X)
    @test F["FunctionOfQ"](a + b * X, sqrt(a + b * X), X) && !F["FunctionOfQ"](a + b * X, X * sqrt(a + b * X), X)
    # trinomials, generalized binomials and trinomials, pseudo-binomials, division
    @test F["TrinomialQ"](a + b * X^2 + c * X^4, X) && !F["TrinomialQ"](a + b * X + c * X^2, X)
    @test F["TrinomialMatchQ"](a + b * X^3 + c * X^6, X)
    @test F["GeneralizedBinomialQ"](a * X^2 + b * X^5, X) && !F["GeneralizedBinomialQ"](a + b * X^5, X)
    @test !F["GeneralizedBinomialMatchQ"](a + b * X^3, X) && !F["GeneralizedTrinomialQ"](a + b * X + c * X^2, X)
    @test F["GeneralizedTrinomialDegree"](a * X + b * X^3 + c * X^5, X) == 2
    @test F["BinomialDegree"](a + b * X^3, X) == 3
    @test F["AlgebraicFunctionQ"](sqrt(X) + 1 / X, X) && !F["AlgebraicFunctionQ"](log(X), X)
    @test F["PseudoBinomialPairQ"](1 + (1 + X)^3, 5 + (1 + X)^3, X)
    @test F["PolynomialDivide"](X^3 + 1, X + 1, X) == X^2 - X + 1
    # P(x) (c + d x)^n as powers of c + d x (RUBI's ExpandLinearProduct)
    e = F["ExpandIntegrand"](X^3 * sqrt(a + b * X), X)
    @test e.kind == SymJ.ADD && iszero(simplify(e - X^3 * sqrt(a + b * X)))
end

# the rules come from SYMJOSR_INTEGRATION_DIR or a download
@testset "With and Condition" begin
    # With[{v = e, …}, body]: the values see the rule's names, all at once
    c = S.Ctx(Dict{Symbol,Any}(:a => Sym(2)), 0)
    L(bs...) = Any["List", (Any["Set", n, e] for (n, e) in bs)...]
    @test S.ev(Any["With", L("b" => Any["Multiply", "a", 3]), Any["Add", "a", "b"]], c) == 8
    @test S.ev(Any["With", L("a" => 5, "b" => "a"), "b"], c) == 2
    @test S.ev(Any["With", L("b" => 3), Any["With", L("d" => "b"), "d"]], c) == 3
    # Condition[value, test]: the rule fails when the test does not hold
    @test S.ev(Any["Condition", 1, Any["EqQ", "a", 2]], c) == 1
    @test_throws S.RuleFails S.ev(Any["Condition", 1, Any["EqQ", "a", 3]], c)
    # the locals are known names in the body; a Module local without a value is not
    @test isempty(S._unknown!(Set{String}(), Any["With", L("v" => "a"), "v"], Set(["a"])))
    @test !isempty(S._unknown!(Set{String}(), Any["With", L("v" => "a"), "w"], Set(["a"])))
    @test !isempty(S._unknown!(Set{String}(), Any["With", Any["List", "v"], "v"], Set(["a"])))
    # Module: a local without a value is a new symbol; Set and CompoundExpression in its
    # body; Sum over a local
    @test isempty(S._unknown!(Set{String}(), Any["Module", Any["List", "v"], "v"], Set(["a"])))
    v = S.ev(Any["Module", Any["List", "v"], "v"], c)
    @test v isa Sym && v.kind == SymJ.SYMBOL && !isequal(v, S.ev(Any["Module", Any["List", "v"], "v"], c))
    @test S.ev(Any["Module", Any["List", "u"], Any["CompoundExpression", Any["Set", "u", Any["Add", "a", 1]], Any["Multiply", "u", "u"]]], c) == 9
    @test S.ev(Any["Module", Any["List", "k"], Any["Sum", Any["Power", "k", 2], Any["List", "k", 1, "a"]]], c) == 5
    @test isempty(S._unknown!(Set{String}(), Any["Sum", "k", Any["List", "k", 0, "a"]], Set(["a"])))
    F = S.FUNCS
    X = S.X
    @test isequal(F["ReplaceAll"](X^2 + a, X => X - b), (X - b)^2 + a)
    @test isequal(F["ReplaceAll"](X + a, [a => b]), X + b)
    @test F["Part"](Any[a, b], Sym(2)) === b
    @test F["MemberQ"](Any[S.FuncName("sin"), S.FuncName("cos")], cos) && !F["MemberQ"](Any[S.FuncName("sin")], tan)
    @test F["NonsumQ"](a * X) && !F["NonsumQ"](a + X)
    @test F["GCD"](Sym(4), Sym(6)) == 2 && F["GCD"](Sym(1//2), Sym(3//4)) == 1//4
    @test isequal(F["DerivativeDivides"](X^2 + 1, 3 * X, X), Sym(3//2))
    @test F["DerivativeDivides"](X^2 + 1, X^2, X) === false && F["DerivativeDivides"](a * X, Sym(1), X) === false
    @test isequal(F["DerivativeDivides"](sin(X), 2 * cos(X), X), Sym(2)) && F["DerivativeDivides"](sin(X), sin(X), X) === false
    # EasyDQ: functions of easy arguments, sums, one nonfree factor; not x*sin(x)
    @test F["EasyDQ"](sin(a + b * X), X) && F["EasyDQ"](a * X^2 + sqrt(X), X) && !F["EasyDQ"](X * sin(X), X)
    # EqQ: the numeric test before simplify rejects only what is not equal
    @test F["EqQ"](sin(X)^2 + cos(X)^2, 1) && !F["EqQ"](sin(X), cos(X)) && F["EqQ"](sqrt(a)^2, a)
    # a constant integrand, without a rule for it
    @test S.integrate(a * b, x) == a * b * x
    F = S.FUNCS["InverseFunctionQ"]
    @test F(log(x)) && F(asinh(x)) && !F(sin(x)) && !F(x)
end

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

@testset "trig and hyperbolic" begin
    R = S.load_rules()
    # cos as sin(+ π/2), hyperbolic functions as trig of imaginary arguments (RUBI's
    # DeactivateTrig, 4.1.0.1 #1, which OSR does not have)
    for f in (cos(x), x * cos(x), sec(x)^2, cot(x), sinh(x), cosh(x)^2, x * sinh(x), 1 / cosh(x), tanh(x))
        @test isantiderivative(S.integrate(f, x; rules = R), f)
    end
    @test S.integrate(x * sinh(x), x; rules = R) == x * cosh(x) - sinh(x)    # back in hyperbolic form
    # RUBI's 4.5.2.1 csc rule (Cos for Csc in its result), corrected
    f = a^2 * sqrt(a * sec(x)^2) * sec(x)^4
    @test isantiderivative(S.integrate(f, x; rules = R), f)
end

@testset "exponentials" begin
    R = S.load_rules()
    X = S.X
    # rules with SubstFor: P(x^n) (a + b x^n)^p as a function of x^n; ProductLog (8.9)
    for f in (x^5 * sqrt(a + b * x^3), lambertw(x))
        @test isantiderivative(S.integrate(f, x; rules = R), f)
    end
    # by parts (2.1, guarded by !TrueQ[$UseGamma]), not the incomplete gamma
    @test S.integrate(x * exp(x), x; rules = R) == x * exp(x) - exp(x)
    # e^x sinh(x): exponentials that cancel (ExpandTrigToExp)
    @test isantiderivative(S.integrate(exp(x) * sinh(x), x; rules = R), exp(x) * sinh(x))
    # the substitution v = e^(d x) (RUBI 2.3's last rule, which OSR does not have)
    @test S.integrate(1 / (exp(x) + 1), x; rules = R) == x - log(exp(x) + 1)
    for f in (1 / (a + b * exp(c + d * x)), 1 / (exp(x) + exp(-x)), 1 / (a + b * exp(x))^2)
        @test isantiderivative(S.integrate(f, x; rules = R), f)
    end
    F = S.FUNCS
    @test F["FunctionOfExponentialQ"](1 / (a + b * exp(X)), X) && !F["FunctionOfExponentialQ"](X * exp(X), X)
    @test !F["FunctionOfExponentialQ"](2^X + exp(X), X)
end

@testset "special functions" begin
    A(n, as...) = SymJ.apply_function(n, Sym[Sym.(as)...])
    # RUBI's PolyLog is SymJ's li (log(t)/(t + 1), Apostol #156, has a Li₂ answer)
    @test S.FUNCTION_NAMES["PolyLog"] === :li
    F = S.integrate(log(x) / (x + 1), x)
    @test F !== nothing && S._verify(subs(F, x => S.X), log(S.X) / (S.X + 1))
    # registered here: values and derivatives
    @test abs(N(A(:EllipticF, SymJ.PI / 2, 1 // 2)) - 1.8540746773013719) < 1e-10
    @test abs(N(A(:EllipticE, 1 // 2)) - 1.3506438810476755) < 1e-10
    @test abs(N(A(:sinhint, 1)) - 1.0572508753757286) < 1e-10
    @test abs(N(A(:logint, 2)) - 1.045163780117493) < 1e-10
    @test iszero(simplify(diff(A(:EllipticE, x, a), x) - sqrt(1 - a * sin(x)^2)))
    @test iszero(simplify(diff(A(:coshint, x), x) - cosh(x) / x))
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

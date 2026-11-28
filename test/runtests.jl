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
    @test all(in(S.rule_files()), keys(S.HOST_MISSING))
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
    # x^m (c x)^n: SymJ writes (c x)^(-7/2) as c^-3 x^-3 (c x)^(-1/2), so RUBI's 1.4.1 rule
    # for it came back to the same integrand (4.1.0 #192)
    for f in (1 / (sqrt(c * x) * x^3), x^2 * (c * x)^(1 // 3), sqrt(c * x) / x^(3 // 2))
        @test isantiderivative(S.integrate(f, x; rules = R), f)
    end
end

@testset "trig and hyperbolic" begin
    R = S.load_rules()
    # cos as sin(+ π/2), hyperbolic functions as trig of imaginary arguments (RUBI's
    # DeactivateTrig, 4.1.0.1 #1, which OSR does not have)
    for f in (cos(x), x * cos(x), sec(x)^2, cot(x), sinh(x), cosh(x)^2, x * sinh(x), 1 / cosh(x), tanh(x),
              # ActivateTrig in a part of 4.3.7 #15's result shifted cot back (4.4.0 #25)
              sqrt(a * cot(x)^2) * cot(x)^2)
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

@testset "formal derivatives" begin
    R = S.load_rules()
    X = S.X
    f, g = SymJ.SymFunction(:f), SymJ.SymFunction(:g)
    fp, gp = diff(f(X), X), diff(g(X), X)
    # reading 8.10's Derivative[n][f][x]
    D(n, h) = Any["Apply", Any["Apply", Any["Derivative", n], Any["List", h]], Any["List", "x"]]
    @test isequal(S.read_osr(D(2, "f")), diff(f(X), X, 2))
    @test isequal(S.read_osr(Any["Multiply", D(1, "f"), Any["g", "x"]]), fp * g(X))
    @test_throws S.OSRError S.read_osr(D("n", "f"))       # a symbolic order: not supported
    # 9.1's rules: the product and quotient rules, read backwards
    # (a sum is integrated term by term first, by 1.4.1, as in RUBI: f'g - fg' stays)
    @test S.integrate(fp * g(X) - f(X) * gp, X; rules = R) === nothing
    @test isequal(S.integrate((fp * g(X) - f(X) * gp) / g(X)^2, X; rules = R), f(X) / g(X))
    @test isequal(S.integrate((fp * g(X) - f(X) * gp) / (f(X) * g(X)), X; rules = R), log(f(X) / g(X)))
    # f'(x) f(x)^n and f'/f through the other rules; checked with f concrete
    for u in (fp * f(X)^3, fp / f(X), fp / sqrt(1 + f(X)))
        r = S.integrate(u, X; rules = R)
        @test r !== nothing && S._verify(r, u)
    end
    # Derivative[n_][f_][x_]: n and f read off the match; f as bound elsewhere
    @test S._fderiv_parts(diff(f(X), X, 3)) == (3, f)
    @test S._fderiv_parts(f(X)) === nothing && S._fderiv_parts(diff(sin(X), X)) === nothing
    @test S._derived_bindings(Dict{Symbol,Any}(Symbol("∂n∂f") => diff(f(X), X, 2), :f => g)) === nothing
    # the check: a wrong answer stays wrong with f concrete
    @test !S._verify(f(X)^2, fp * f(X))
    @test S._verify(f(X)^2 / 2, fp * f(X))
end

@testset "OSR errata" begin
    # Python's json.dumps(…, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    @test S._canonical(Dict("b" => Any[1, "x\"y\\\n", nothing, true], "a" => "π")) ==
        "{\"a\":\"π\",\"b\":[1,\"x\\\"y\\\\\\n\",null,true]}"
    # every record's own digest, as OSR computes it
    recs = S.errata()
    @test !isempty(recs)
    @test all(e -> e["action"] == "replace" ? S._payload_sha(e["replacement"]) == e["replacement_sha256"] :
                   S._payload_sha(e["rule"]) == e["rule_sha256"], recs)
    # applying records: replace, enable before a rule, and a record that no longer matches
    r1 = Dict{String,Any}("id" => 1, "constraints" => Any[], "pattern" => "p", "result" => "wrong")
    r2 = Dict{String,Any}("id" => 2, "constraints" => Any[], "pattern" => "q", "result" => "s")
    new = Dict{String,Any}("constraints" => Any[], "pattern" => "p", "result" => "right")
    add = Dict{String,Any}("constraints" => Any["c"], "pattern" => "e", "result" => "t")
    rep = Dict{String,Any}("file_identity" => "F", "rule_id" => 1, "action" => "replace",
        "payload_sha256" => S._payload_sha(r1), "replacement" => new, "replacement_sha256" => S._payload_sha(new))
    en = Dict{String,Any}("file_identity" => "F", "rule_id" => 9, "action" => "enable", "insert_before" => 2,
        "rule" => add, "rule_sha256" => S._payload_sha(add))
    rs, applied = S._apply_errata(Any[r1, r2], "f.json", "F", Any[rep, en])
    @test [r["id"] for r in rs] == [1, 9, 2] && rs[1]["result"] == "right" && rs[2]["result"] == "t"
    @test [a.id for a in applied] == [1, 9] && r1["result"] == "wrong"     # the input is not changed
    @test S._apply_errata(Any[r1, r2], "f.json", "G", Any[rep, en])[1] == Any[r1, r2]   # another file
    stale = merge(rep, Dict{String,Any}("payload_sha256" => "0"^64))
    rs, applied = @test_logs (:warn, r"has changed since the record") S._apply_errata(Any[r1], "f.json", "F", Any[stale])
    @test rs[1]["result"] == "wrong" && isempty(applied)
    # the records for the rules we load all apply
    R = S.load_rules()
    mine = [e for e in recs if startswith(e["file_identity"], "rubi:")]
    @test length(R.errata) == length(mine)
    @test all(a -> any(r -> r.file == a.file && r.id == a.id, R.rules), R.errata)
    # 8.1 #52 (the residual Int, OSR #12) and 8.4 #27 (also its F guard)
    A(n, u) = SymJ.apply_function(n, Sym[u])
    for u in (A(:erf, a + b * log(x)) / x, A(:sinint, a + b * log(x)) / x)
        @test isantiderivative(S.integrate(u, x; rules = R), u)
    end
    # 9.1 cells 1 and 8 (OSR #13): f'(x) and f''/f'
    X = S.X
    f = SymJ.SymFunction(:f)
    @test isequal(S.integrate(diff(f(X), X, 2), X; rules = R), diff(f(X), X))
    @test isequal(S.integrate(diff(f(X), X, 2) / diff(f(X), X), X; rules = R), log(diff(f(X), X)))
end

@testset "fractional powers of linears" begin
    R = S.load_rules()
    X = S.X
    F = S.FUNCS
    # SubstForFractionalPowerOfLinear: {v, n, a + b x, c}, Int[u] = n c Subst[Int[v], x, (a + b x)^(1/n)]
    l = F["SubstForFractionalPowerOfLinear"](1 / (4 - X + sqrt(4 - X)), X)
    @test isequal(l[1], 1 / (X + 1)) && l[2] == 2 && isequal(l[3], 4 - X) && l[4] == -1
    @test F["SubstForFractionalPowerOfLinear"](sqrt(1 + X^2), X) === false
    @test S._qol_parts((1 + X) / (1 - X), X) == (1, 1, 1, -1)
    @test S._qol_parts(2 + 1 / (X + 3), X) == (7, 2, 3, 1)
    @test S._qol_parts(sqrt(X), X) === nothing
    @test !F["TryPureTanSubst"](atan(2 * tan(3 * X)), X) && F["TryPureTanSubst"](atan(X), X)
    # Apostol #19 and #114 (u = x^2, then a root of a linear function), and others
    for u in (X / sqrt((X^2 + 1)^(3 // 2) + X^2 + 1), X / (4 - X^2 + sqrt(4 - X^2)),
              1 / (sqrt(X) + X^(1 // 3)), 1 / (X * sqrt((1 + X) / (1 - X))))
        r = S.integrate(u, X; rules = R)
        @test r !== nothing && S._verify(r, u)
    end
end

@testset "trig substitutions" begin
    R = S.load_rules()
    X = S.X
    F = S.FUNCS
    # FunctionOfTrig[u, x], as 4.7.5's general substitutions call it
    @test isequal(F["FunctionOfTrig"](sin(2X) * cos(X), X), X) && F["FunctionOfTrig"](X^2, X) === false
    # FunctionOfQ[trig v, u, x]: RUBI's FunctionOfSinQ, FunctionOfCosQ, FunctionOfTanQ
    @test F["FunctionOfQ"](tan(X), 1 / (a^2 * sin(X)^2 + b^2 * cos(X)^2), X)
    @test F["FunctionOfQ"](sin(X), sin(X)^3 + cos(2X), X) && !F["FunctionOfQ"](sin(X), cos(X) * sin(X)^2, X)
    @test F["FunctionOfQ"](cos(X), sin(X)^2 * cos(X), X) && !F["FunctionOfQ"](cos(X), sin(X), X)
    @test F["FunctionOfQ"](tan(X), tan(X)^2, X, true) && !F["FunctionOfQ"](tan(X), sin(X)^2, X, true)
    # SubstFor[trig v, u, x]: SubstForTrig, with multiple angles
    @test isequal(F["SubstFor"](1 / (1 + X^2), tan(X), 1 / (a^2 * sin(X)^2 + b^2 * cos(X)^2), X), 1 / (a^2 * X^2 + b^2))
    @test isequal(F["SubstFor"](sin(X), sin(X)^3, X), X^3)
    s, c = S._multiple_angle(3, a, b)
    @test iszero(expand(s - (3 * b^2 * a - a^3))) && iszero(expand(c - (b^3 - 3 * a^2 * b)))
    # Apostol #145, by 4.7.5's t = tan x; 4.3.4.2 #28, whose substituted integrand has to
    # stay factored (it did not finish multiplied out)
    @test isequal(F["SubstFor"](1 / (1 + X^2), tan(X), (b * tan(X) + c * tan(X)^2) * cot(X) / (a + b * tan(X)), X),
                  factor((c * X + b) / ((b * X + a) * (X^2 + 1))))
    for u in (1 / (a^2 * sin(X)^2 + b^2 * cos(X)^2), 1 / (1 + cos(X)^2), sin(2X) / (1 + sin(X)^2))
        r = S.integrate(u, X; rules = R)
        @test r !== nothing && S._verify(r, u)
    end
end

@testset "hyperbolic substitutions" begin
    X = S.X
    F = S.FUNCS
    # FunctionOfQ[hyperbolic v, u, x]: RUBI's FunctionOfSinhQ, FunctionOfCoshQ, FunctionOfTanhQ
    @test F["FunctionOfQ"](tanh(X), 1 / (a^2 * sinh(X)^2 + b^2 * cosh(X)^2), X)
    @test F["FunctionOfQ"](sinh(X), sinh(X)^3 + cosh(2X), X) && !F["FunctionOfQ"](sinh(X), cosh(X) * sinh(X)^2, X)
    @test F["FunctionOfQ"](cosh(X), sinh(X)^2 * cosh(X), X) && !F["FunctionOfQ"](cosh(X), sinh(X), X)
    @test F["FunctionOfQ"](tanh(X), tanh(X)^2, X, true) && !F["FunctionOfQ"](tanh(X), sinh(X)^2, X, true)
    # SubstFor[hyperbolic v, u, x]: SubstForHyperbolic, with multiple angles
    @test isequal(F["SubstFor"](1 / (1 - X^2), tanh(X), 1 / (a^2 * sinh(X)^2 + b^2 * cosh(X)^2), X), 1 / (a^2 * X^2 + b^2))
    @test isequal(F["SubstFor"](sinh(X), sinh(X)^3, X), X^3)
    s, c = S._multiple_angle(3, a, b, true)
    @test iszero(expand(s - (3 * b^2 * a + a^3))) && iszero(expand(c - (b^3 + 3 * a^2 * b)))
end

@testset "time limit" begin
    R = S.load_rules()
    X = S.X
    # 1.3.1 #157: one _int on a large integrand tries the rules for minutes without entering
    # another _int; the limit is also checked before each rule and for each candidate match
    u = X^2 / (X^6 + 18 * X^4 + 324 * X^3 + 108 * X^2 + 216)^2
    t = @elapsed st = S._check(u, R, 2.0)[1]
    @test st === :timeout && t < 30
end

@testset "PiecewiseLinearQ and FunctionOfLinear" begin
    R = S.load_rules()
    X = S.X
    F = S.FUNCS
    @test F["PiecewiseLinearQ"](log(c * exp(a + b * X)), X) && F["PiecewiseLinearQ"](atan(tan(2X)), X)
    @test !F["PiecewiseLinearQ"](log(X), X) && F["PiecewiseLinearQ"](a + b * X, atanh(coth(X)), X)
    # {f(x), a, b} for u = f(a + b x)
    l = F["FunctionOfLinear"](sqrt(2X + 1) + (4X + 2)^2, X)
    @test isequal(l[1], 4X^2 + sqrt(X)) && l[2] == 1 && l[3] == 2
    @test F["FunctionOfLinear"](X * sin(X), X) === false && F["FunctionOfLinear"](sin(X), X) === false
    for u in (X * atan(tan(a + b * X)), atanh(tanh(X))^2, 1 / (sqrt(2X + 1) + (2X + 1)), exp(2X + 1) / (1 + exp(2X + 1))^2)
        r = S.integrate(u, X; rules = R)
        @test r !== nothing && S._verify(r, u)
    end
end

@testset "NormalizeIntegrand" begin
    R = S.load_rules()
    X = S.X
    NI = S.FUNCS["NormalizeIntegrand"]
    @test any(r -> endswith(r.file, "9.3-Miscellaneous-integration-rules.json") && r.id == 67, R.rules)
    # like powers of x collected; the least power of x taken out of a sum of monomials
    @test isequal(NI(1 / (a * X^m + b * X^m)^3, X), 1 / ((a + b)^3 * X^(3m)))
    @test isequal(NI((a * X^2 + b * X^3)^2, X), X^4 * (a + b * X)^2)
    # powers of proportional linear factors merged; a sum that is not a polynomial factored
    v = NI((2X + 2)^2 * (X + 1)^3, X)          # one power of a linear factor
    @test v.kind == SymJ.MUL && length(v.args) == 1 && iszero(expand(v - 4 * (X + 1)^5))
    @test isequal(NI(sin(X)^2 / (sin(X) + sin(X)^2), X), sin(X) / (1 + sin(X)))
    # unchanged: u itself
    @test isequal(NI((X - 1)^2 / X, X), (X - 1)^2 / X)
    for u in (1 / (a * X^m + b * X^m)^3, sin(X)^2 / (sin(X) + sin(X)^2))
        r = S.integrate(u, X; rules = R)
        @test r !== nothing && S._verify(r, u)
    end
end

@testset "TrigReduce and ExpandTrigReduce" begin
    R = S.load_rules()
    X = S.X
    T = S.FUNCS["TrigReduce"]
    same(u, v) = abs(ComplexF64(N(subs(u - v, X => 0.37, a => 0.6, b => 1.3)))) < 1e-12
    @test isequal(T(sin(X)^3), 3 * sin(X) / 4 - sin(3X) / 4)
    @test isequal(T(sin(X)^2 * cos(X)^2), 1 // 8 - cos(4X) / 8)
    for u in (cos(a + b * X)^3, sin(X) * cos(2X), sinh(X)^3, cosh(a + b * X)^2 * sinh(a + b * X))
        @test same(T(u), u)
    end
    @test isequal(T(X * sin(X)), X * sin(X))                 # one factor to the first power: unchanged
    # x^m sin(a + b x)^n by 4.1.10 and 6.1.3, term by term to Si and Ci
    for u in (cos(X)^3 / X, sin(a + b * X)^2 / X, cos(X)^3 * sin(X)^2 / X, sinh(X)^3 / X)
        r = S.integrate(u, X; rules = R)
        @test r !== nothing && S._verify(r, u)
    end
end

@testset "Complex in patterns, ComplexFreeQ" begin
    R = S.load_rules()
    X = S.X
    C = S.FUNCS["ComplexFreeQ"]
    @test C(a * X + 2) && C(sqrt(Sym(2))) && !C(im * b) && !C(sin(2im * X)) && !C(sqrt(Sym(-3)))
    # the 4.1.10 rules with Complex[0, fz_] in their patterns load
    @test !any(s -> occursin("Complex", s.reason), R.skipped)
    # and give RUBI's forms: ∫ sin(i b x)/x = i Shi(b x), not Si(i b x)
    for (u, h) in ((sin(im * b * X) / X, :sinhint), (sin(im * b * X + im * a) / (b * X + a), :sinhint))
        r = S.integrate(u, X; rules = R)
        @test r !== nothing && S._verify(r, u) && occursin(string(h), string(r))
    end
end

@testset "formal check against the expected answer" begin
    X = S.X
    # RUBI's ∫ (c + d x) csch(a + b x): its form fails the numeric check (atanh(exp(a + b x))
    # and polylogs of exp(a + b x) on their branch cuts), and matches the expected answer
    e = (-2d * X - 2c) * atanh(exp(b * X + a)) / b - d * S.FUNCS["PolyLog"](2, -exp(b * X + a)) / b^2 +
        d * S.FUNCS["PolyLog"](2, exp(b * X + a)) / b^2
    r = -2 * atanh(exp(b * X + a)) * d * X / b - 2 * atanh(exp(b * X + a)) * c / b -
        d * S.FUNCS["PolyLog"](2, -exp(b * X + a)) / b^2 + d * S.FUNCS["PolyLog"](2, exp(b * X + a)) / b^2
    @test S._formal_match(r, e) && S._formal_match(r + 3, e)      # up to a constant
    @test !S._formal_match(r + X, e)
    @test S._formal_match(im * cot(im * a * X), coth(a * X))          # Mathematica's Cot[I u] = -I Coth[u]
    @test S._formal_match((X + 1) * (X - 1) / (X^2 - 1) + log(X), log(X))
    u = (c + d * X) * csch(a + b * X)
    @test first(S._check(u, S.load_rules(), 30.0; expected = e)) === :verified
    # Ci(i w) = Chi(w) + iπ/2, Si(i w) = i Shi(w), and π/2 shifts (7.3.4 #483's answer)
    ci(z) = SymJ.apply_function(:cosint, Sym[z]); chi(z) = SymJ.apply_function(:coshint, Sym[z])
    si(z) = SymJ.apply_function(:sinint, Sym[z]); shi(z) = SymJ.apply_function(:sinhint, Sym[z])
    @test S._formal_match(5 * ci(3im * atanh(a * X)) / 16 + ci(im * atanh(a * X)) / 8, 5 * chi(3atanh(a * X)) / 16 + chi(atanh(a * X)) / 8)
    @test S._formal_match(im * si(im * b * X) + sin(a * X + SymJ.PI / 2), -shi(b * X) + cos(a * X))
    @test !S._formal_match(ci(im * b * X), shi(b * X))
    # r - e the same at several x, numerically: erf of (-1)^(1/4) z for Fresnel (5.2.2 #82's kind)
    w = sqrt(asin(a * X)); ω = Sym(-1)^(1 // 4)
    fs(z) = SymJ.apply_function(:fresnels, Sym[z]); erfi(z) = SymJ.apply_function(:erfi, Sym[z])
    r = ω * sqrt(Sym(π)) * (SymJ.apply_function(:erf, Sym[ω * w]) - erfi(ω * w)) / 2
    @test S._const_diff(r, sqrt(2Sym(π)) * fs(sqrt(2 / Sym(π)) * w) + 3, w)
    @test !S._const_diff(r + X, sqrt(2Sym(π)) * fs(sqrt(2 / Sym(π)) * w), w)
end

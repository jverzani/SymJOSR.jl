# RUBI's structural predicates on linear, quadratic and binomial forms, and the
# "integrable in terms of non-hypergeometric functions" tests that rule files define
# for themselves (IntLinearQ in 1.1.1.2, IntBinomialQ in 1.1.3.2-1.1.3.4,
# IntQuadraticQ in 1.2.1.2). After IntegrationUtilityFunctions.m, RUBI 4.16.1.
#
# The *MatchQ predicates are syntactic in RUBI (MatchQ on the expression as it stands),
# so here they read SymJ's canonical form: a number is distributed over a sum (2(x+1)
# is 2x + 2), a symbol is not (c(x+1) stays a product), much as in Mathematica.

_each(f, u) = u isa AbstractVector ? all(f, u) : f(u)

# u = c x^k with c free of x: (c, k), or nothing. (x alone: (1, 1).)
function _monomial(u::Sym, x::Sym)
    _free(u, x) && return (u, SymJ.ZERO)
    isequal(u, x) && return (SymJ.ONE, SymJ.ONE)
    u.kind == SymJ.POW && isequal(u.args[1], x) && _free(u.args[2], x) && return (SymJ.ONE, u.args[2])
    u.kind == SymJ.MUL || return nothing
    c, w = FUNCS["FreeFactors"](u, x), FUNCS["NonfreeFactors"](u, x)
    isequal(w, u) && return nothing        # no constant factor: not c x^k
    m = _monomial(w, x)
    m === nothing ? nothing : (c * m[1], m[2])
end

# the terms of u as monomials in x: Dict(k => c), or nothing when a term is not one
function _monomials(u::Sym, x::Sym)
    out = Dict{Sym,Sym}()
    for t in _terms(u)
        m = _monomial(t, x)
        m === nothing && return nothing
        out[m[2]] = get(out, m[2], SymJ.ZERO) + m[1]
    end
    out
end

# LinearMatchQ[u, x]: u is a. + b.*x (b.*x present)
_linear_match(u, x) = (ms = _monomials(_s(u), x); ms !== nothing && haskey(ms, SymJ.ONE) &&
    all(k -> iszero(k) || isone(k), keys(ms)))
# QuadraticMatchQ[u, x]: a. + b.*x + c.*x^2 or a. + c.*x^2 (c.*x^2 present)
_quadratic_match(u, x) = (ms = _monomials(_s(u), x); ms !== nothing && haskey(ms, Sym(2)) &&
    all(k -> iszero(k) || isone(k) || isequal(k, Sym(2)), keys(ms)))
# BinomialMatchQ[u, x]: a. + b.*x^n. (n free of x, b.*x^n present)
_binomial_match(u, x) = (ms = _monomials(_s(u), x); ms !== nothing &&
    count(k -> !iszero(k), keys(ms)) == 1)

FUNCS["LinearMatchQ"] = (u, x) -> _each(v -> _linear_match(v, _s(x)), u)
FUNCS["QuadraticMatchQ"] = (u, x) -> _each(v -> _quadratic_match(v, _s(x)), u)
FUNCS["BinomialMatchQ"] = (u, x) -> _each(v -> _binomial_match(v, _s(x)), u)

# BinomialParts[u, x]: (a, b, n) with u = a + b x^n, n ≠ 0, a and b free of x; or nothing.
# (RUBI's case of a product of two binomials, (a + b x^m)(c + d x^n) with a d + b c = 0
# and the like, is not done: such a u is not a binomial here. An approximation.)
function _binomial_parts(u::Sym, x::Sym)
    _free(u, x) && return nothing
    ms = _monomials(u, x)
    ms === nothing && return nothing
    ks = [k for k in keys(ms) if !iszero(k)]
    length(ks) == 1 || return nothing
    k = only(ks)
    (get(ms, SymJ.ZERO, SymJ.ZERO), ms[k], k)
end

FUNCS["BinomialQ"] = function (u, x, n = nothing)
    _each(u) do v
        p = _binomial_parts(_s(v), _s(x))
        p !== nothing && (n === nothing || isequal(p[3], _s(n)))
    end
end
FUNCS["BinomialParts"] = (u, x) -> (p = _binomial_parts(_s(u), _s(x));
    p === nothing ? false : Any[p...])

# LinearPairQ[u, v, x]: u and v linear in x, u ≠ x, proportional
FUNCS["LinearPairQ"] = function (u, v, x)
    L, C = FUNCS["LinearQ"], FUNCS["Coefficient"]
    L(u, x) && L(v, x) && !_eq(u, x) &&
        _eq(C(u, x, Sym(0)) * C(v, x, Sym(1)) - C(u, x, Sym(1)) * C(v, x, Sym(0)), Sym(0))
end

# RationalFunctionQ[u, x]: built from x and constants with +, * and integer powers
function _rational_function(u, x)
    u isa Sym || return true
    _free(u, x) && return true
    u.kind == SymJ.SYMBOL && return true
    u.kind == SymJ.POW && return _isinteger(u.args[2]) && _rational_function(u.args[1], x)
    u.kind == SymJ.ADD && return all(t -> _rational_function(t, x), _terms(u))
    u.kind == SymJ.MUL && return all(t -> _rational_function(t, x), _factors(u))
    false
end
FUNCS["RationalFunctionQ"] = (u, x) -> _rational_function(u, _s(x))

# ---- integrable without hypergeometric (Appell) functions: the rule files' own tests

_IQ(us...) = FUNCS["IntegersQ"](us...)
_E(u, v) = _eq(u, v)
_IGt(u, n) = FUNCS["IGtQ"](_s(u), Sym(n))
_ILt(u, n) = FUNCS["ILtQ"](_s(u), Sym(n))

# IntLinearQ[a, b, c, d, m, n, x]: (a + b x)^m (c + d x)^n (1.1.1.2)
FUNCS["IntLinearQ"] = (a, b, c, d, m, n, x) ->
    _IGt(m, 0) || _IGt(n, 0) || _IQ(3m, 3n) || _IQ(4m, 4n) || _IQ(2m, 6n) || _IQ(6m, 2n) ||
    _ILt(m + n, -1) || _isinteger(m + n) && _isrational(m)

FUNCS["IntBinomialQ"] = function (args...)
    if length(args) == 7          # (c x)^m (a + b x^n)^p (1.1.3.2)
        a, b, c, n, m, p, x = args
        return _IGt(p, 0) || _isrational(m) && _IQ(n, 2p) || _isinteger((m + 1) / n + p) ||
            (_E(n, 2) || _E(n, 4)) && _IQ(2m, 4p) ||
            _E(n, 2) && _isinteger(6p) && (_isinteger(m) || _isinteger(m - p))
    elseif length(args) == 8      # (a + b x^n)^p (c + d x^n)^q (1.1.3.3)
        a, b, c, d, n, p, q, x = args
        return _IQ(p, q) || _IGt(p, 0) || _IGt(q, 0) ||
            (_E(n, 2) || _E(n, 4)) && (_IQ(p, 4q) || _IQ(4p, q)) ||
            _E(n, 2) && (_IQ(2p, 2q) || _IQ(3p, q) && _E(b * c + 3a * d, 0) ||
                         _IQ(p, 3q) && _E(3b * c + a * d, 0)) ||
            _E(n, 3) && (_IQ(p + 1 // 3, q) || _IQ(q + 1 // 3, p)) ||
            _E(n, 3) && (_IQ(p + 2 // 3, q) || _IQ(q + 2 // 3, p)) && _E(b * c + a * d, 0)
    elseif length(args) == 10     # (e x)^m (a + b x^n)^p (c + d x^n)^q (1.1.3.4)
        a, b, c, d, e, m, n, p, q, x = args
        return _IQ(p, q) || _IGt(p, 0) || _IGt(q, 0) ||
            _E(n, 2) && (_IQ(m, 2p, 2q) || _IQ(2m, p, 2q) || _IQ(2m, 2p, q)) ||
            _E(n, 4) && (_IQ(m, p, 2q) || _IQ(m, 2p, q)) ||
            _E(n, 2) && _IQ(m / 2, p + 1 // 3, q) && (_E(b * c + 3a * d, 0) || _E(b * c - 9a * d, 0)) ||
            _E(n, 2) && _IQ(m / 2, q + 1 // 3, p) && (_E(a * d + 3b * c, 0) || _E(a * d - 9b * c, 0)) ||
            _E(n, 3) && _IQ((m - 1) / 3, q, p - 1 // 2) &&
                (_E(b * c - 4a * d, 0) || _E(b * c + 8a * d, 0) || _E(b^2 * c^2 - 20a * b * c * d - 8a^2 * d^2, 0)) ||
            _E(n, 3) && _IQ((m - 1) / 3, p, q - 1 // 2) &&
                (_E(4b * c - a * d, 0) || _E(8b * c + a * d, 0) || _E(8b^2 * c^2 + 20a * b * c * d - a^2 * d^2, 0)) ||
            _E(n, 3) && (_IQ(m, q, 3p) || _IQ(m, p, 3q)) && _E(b * c + a * d, 0) ||
            _E(n, 3) && (_IQ((m + 2) / 3, p + 2 // 3, q) || _IQ((m + 2) / 3, q + 2 // 3, p)) ||
            _E(n, 3) && (_IQ(m / 3, p + 1 // 3, q) || _IQ(m / 3, q + 1 // 3, p))
    end
    throw(OSRError("IntBinomialQ with $(length(args)) arguments"))
end

# IntQuadraticQ[a, b, c, d, e, m, p, x]: (d + e x)^m (a + b x + c x^2)^p (1.2.1.2)
FUNCS["IntQuadraticQ"] = (a, b, c, d, e, m, p, x) ->
    _isinteger(p) || _IGt(m, 0) || _IQ(2m, 2p) || _IQ(m, 4p) ||
    _IQ(m, p + 1 // 3) && (_E(c^2 * d^2 - b * c * d * e + b^2 * e^2 - 3a * c * e^2, 0) ||
                          _E(c^2 * d^2 - b * c * d * e - 2b^2 * e^2 + 9a * c * e^2, 0))

# ---- polynomial division

function _divrem(u, v, x)
    x = _s(x)
    p, q = SymJ.Poly(expand(_s(u)), x), SymJ.Poly(expand(_s(v)), x)
    d, r = divrem(p, q)
    Sym(d), Sym(r)
end
FUNCS["PolynomialQuotient"] = (u, v, x) -> _divrem(u, v, x)[1]
FUNCS["PolynomialRemainder"] = (u, v, x) -> _divrem(u, v, x)[2]

# ---- functions as values: TrigQ[F], HyperbolicQ[F] (F a head slot's binding)

# the name of a function given as a value: a head slot binds a Julia function (sin) or a
# SymFunction; a name in a rule is a FuncName; an application, its head
_fname(f::Function) = nameof(f)
_fname(f::SymJ.SymFunction) = f.name
_fname(f::FuncName) = get(FUNCTION_NAMES, f.name, Symbol(f.name))
_fname(f::Sym) = f.kind == SymJ.FN ? f.name : nothing
_fname(f) = nothing

const _TRIG = (:sin, :cos, :tan, :cot, :sec, :csc)
const _HYPERBOLIC = (:sinh, :cosh, :tanh, :coth, :sech, :csch)
FUNCS["TrigQ"] = u -> _fname(u) in _TRIG
FUNCS["HyperbolicQ"] = u -> _fname(u) in _HYPERBOLIC

FUNCS["IndependentQ"] = (u, x) -> FUNCS["FreeQ"](u, x)

# InverseFunctionFreeQ[u, x]: x is not inside an inverse function (log, inverse trig and
# hyperbolic functions, polylog) or a ₂F₁
const _INVERSE = (:log, :asin, :acos, :atan, :acot, :asec, :acsc, :asinh, :acosh, :atanh,
    :acoth, :asech, :acsch, :li, :_₂F₁, :AppellF1)
function _inverse_function_free(u, x)
    u isa Sym || return true
    u.kind == SymJ.FN && u.name in _INVERSE && return !has(u, x)
    all(a -> _inverse_function_free(a, x), u.args) && all(a -> _inverse_function_free(a, x), u.exps)
end
FUNCS["InverseFunctionFreeQ"] = (u, x) -> _inverse_function_free(_s(u), _s(x))

# ---- KnownTrigIntegrandQ[list, u, x]: u is one of the forms of trig integrand RUBI
# integrates, (a + b F[e + f x])^m (A + B F[e + f x] + C F[e + f x]^2) and its special
# cases, with F in list (the MatchQ patterns of IntegrationUtilityFunctions.m)

const _KTI = Ref{Any}(nothing)
function _known_trig_patterns()
    _KTI[] === nothing || return _KTI[]
    arg = Any["Add", "e.", Any["Multiply", "f.", "x_"]]
    F = Any["func_", arg]
    base = Any["Power", Any["Add", "a.", Any["Multiply", "b.", F]], "m."]
    quad2 = Any["Add", "A.", Any["Multiply", "C.", Any["Power", F, 2]]]
    quad3 = Any["Add", "A.", Any["Multiply", "B.", F], Any["Multiply", "C.", Any["Power", F, 2]]]
    lin = Any["Add", "A.", Any["Multiply", "B.", F]]
    forms = Any[base, Any["Multiply", base, lin], quad2, quad3, Any["Multiply", base, quad2], Any["Multiply", base, quad3]]
    _KTI[] = [SymJ.pattern(pat(p)) for p in forms]
end

function _known_trig_integrand(list, u, x)
    u = _s(u)
    isone(u) && return true
    names = Set(_fname(f) for f in list)
    for p in _known_trig_patterns(), m in eachmatch(p, u)
        _fname(m[:func]) in names || continue
        all(k -> k === :func || !has(_s(m[k]), _s(x)), keys(m)) && return true
    end
    false
end
FUNCS["KnownTrigIntegrandQ"] = (list, u, x) -> _known_trig_integrand(list, u, x)
FUNCS["KnownSineIntegrandQ"] = (u, x) -> _known_trig_integrand((sin, cos), u, x)
FUNCS["KnownSecantIntegrandQ"] = (u, x) -> _known_trig_integrand((sec, csc), u, x)
FUNCS["KnownTangentIntegrandQ"] = (u, x) -> _known_trig_integrand((tan,), u, x)
FUNCS["KnownCotangentIntegrandQ"] = (u, x) -> _known_trig_integrand((cot,), u, x)

# ---- hyperbolic functions as trig functions of imaginary arguments
#
# RUBI 4.16.1 integrates hyperbolic functions of linear arguments with its trig rules:
# the first rule of 4.1.0.1, Int[u_, x_] := Int[DeactivateTrig[u, x], x] /;
# FunctionOfTrigOfLinearQ[u, x], replaces sinh(v) with -i sin(i v), and so on (RUBI's
# inert lower-case trig functions, which are SymJ's ordinary ones here). OSR does not
# have that rule (it is wrapped in If[$LoadShowSteps, ...]): HOST_MISSING in
# src/sums.jl stands in for it.

# a hyperbolic function's trig form: f(v) = c * g(i v)
const _HYP_TO_TRIG = Dict(:sinh => (:sin, -im), :cosh => (:cos, 1), :tanh => (:tan, -im),
    :coth => (:cot, im), :sech => (:sec, 1), :csch => (:csc, im))

_linear_in(v, x) = FUNCS["LinearQ"](v, x)

function _deactivate_trig(u, x)
    u isa Sym || return u
    # an integer negative power of a hyperbolic function as a power of its reciprocal,
    # as Mathematica has it (1/Cosh[x] is Sech[x]), before the conversion
    if u.kind == SymJ.POW && u.args[1].kind == SymJ.FN && u.args[1].name in _HYPERBOLIC &&
            _isinteger(u.args[2]) && _rat(u.args[2]) < 0
        b = u.args[1]
        return _deactivate_trig(apply_function(_RECIP[b.name], Sym[b.args[1]])^(-u.args[2]), x)
    end
    if u.kind == SymJ.FN && haskey(_HYP_TO_TRIG, u.name) && length(u.args) == 1 && _linear_in(u.args[1], x)
        g, c = _HYP_TO_TRIG[u.name]
        return Sym(c) * apply_function(g, Sym[expand(Sym(im) * u.args[1])])
    end
    isempty(u.args) && return u
    SymJ._rw_parts(a -> _deactivate_trig(a, x), u)
end
# UnifyInertTrigFunction, in part: RUBI's sine rules integrate cos(v) as sin(v + π/2)
# (4.1.1.1: Int[sin[c + Pi/2 + d x]] := Sin[c + d x]/d). An integrand with cos or sec but
# no sin or csc is written that way: cos(v) = sin(v + π/2), sec(v) = csc(v + π/2),
# tan(v) = -cot(v + π/2), cot(v) = -tan(v + π/2). (RUBI's 75 cases also rewrite some
# products of both; those are left as they are: approximation.)
const _SHIFT = Dict(:cos => (:sin, 1), :sec => (:csc, 1), :tan => (:cot, -1), :cot => (:tan, -1))
function _trig_names!(out, u)
    u isa Sym || return out
    u.kind == SymJ.FN && u.name in _TRIG && push!(out, u.name)
    foreach(a -> _trig_names!(out, a), u.args)
    foreach(a -> _trig_names!(out, a), u.exps)
    out
end
function _shift_cos(u, x)
    u isa Sym || return u
    if u.kind == SymJ.FN && haskey(_SHIFT, u.name) && length(u.args) == 1 && _linear_in(u.args[1], x)
        g, c = _SHIFT[u.name]
        return Sym(c) * apply_function(g, Sym[u.args[1] + SymJ.PI / 2])
    end
    isempty(u.args) && return u
    SymJ._rw_parts(a -> _shift_cos(a, x), u)
end
# the arguments of the trig functions in u are linear in x and multiples of one another
# by rational numbers
function _trig_args!(out, u)
    u isa Sym || return out
    u.kind == SymJ.FN && u.name in _TRIG && length(u.args) == 1 && push!(out, u.args[1])
    foreach(a -> _trig_args!(out, a), u.args)
    foreach(a -> _trig_args!(out, a), u.exps)
    out
end
function _commensurate_trig(u, x)
    vs = _trig_args!(Sym[], u)
    isempty(vs) && return false
    v = :null
    for w in vs
        v = _function_of_trig(apply_function(:sin, Sym[w]), v, x)
        v === false && return false
    end
    true
end
_shift_only(u, x, names) = u isa Sym && !isempty(u.args) ?
    (u.kind == SymJ.FN && u.name in names && length(u.args) == 1 && _linear_in(u.args[1], x) ?
        _shift_cos(u, x) : SymJ._rw_parts(a -> _shift_only(a, x, names), u)) : u
function _unify_inert_trig(u, x)
    ns = _trig_names!(Set{Symbol}(), u)
    isempty(ns) && return u
    _commensurate_trig(u, x) || return u
    # only cos and sec: sines; only cot: tangents. (Mixed forms such as sec^m (a + b tan)^n
    # or cot^n (a + b csc)^m have their own rules, 4.3.1.2 and 4.6.1.4, and are left as
    # they are.)
    issubset(ns, (:cos, :sec)) && return _shift_cos(u, x)
    ns == Set([:cot]) && return _shift_only(u, x, (:cot,))
    u
end

FUNCS["DeactivateTrig"] = (u, x = X) -> _unify_inert_trig(_deactivate_trig(_s(u), _s(x)), _s(x))
# (ours: the rule from 4.1.0.1 applies only when it changes the integrand; RUBI's
# active and inert trig functions are the same functions here)
FUNCS["DeactivateChangesQ"] = (u, x) -> !isequal(FUNCS["DeactivateTrig"](u, x), _s(u))

# results: trig functions of v + π/2 back to those of v
const _UNSHIFT = Dict(:sin => (:cos, 1), :cos => (:sin, -1), :tan => (:cot, -1), :cot => (:tan, -1),
    :sec => (:csc, -1), :csc => (:sec, 1))
function _unshift(u)
    u isa Sym || return u
    if u.kind == SymJ.FN && haskey(_UNSHIFT, u.name) && length(u.args) == 1
        w = expand(u.args[1] - SymJ.PI / 2)
        if !has(w, SymJ.PI)
            g, c = _UNSHIFT[u.name]
            return Sym(c) * apply_function(g, Sym[_unshift(w)])
        end
    end
    isempty(u.args) && return u
    SymJ._rw_parts(_unshift, u)
end

# a trig function of an imaginary argument back as a hyperbolic one: g(i w) = c * f(w)
const _TRIG_TO_HYP = Dict(:sin => (:sinh, im), :cos => (:cosh, 1), :tan => (:tanh, im),
    :cot => (:coth, -im), :sec => (:sech, 1), :csc => (:csch, -im),
    # and inverse functions: atanh(i w) = i atan(w), atan(i w) = i atanh(w)
    :atanh => (:atan, im), :atan => (:atanh, im))
function _activate_hyperbolic(u)
    u isa Sym || return u
    if u.kind == SymJ.FN && haskey(_TRIG_TO_HYP, u.name) && length(u.args) == 1
        w = expand(u.args[1] / Sym(im))
        if !has(w, Sym(im)) && !_has_imaginary(w)
            f, c = _TRIG_TO_HYP[u.name]
            return Sym(c) * apply_function(f, Sym[w])
        end
    end
    isempty(u.args) && return u
    SymJ._rw_parts(_activate_hyperbolic, u)
end
# (SymJ's i is (-1)^(1/2), a power; a float complex number is a number)
_has_imaginary(e::Sym) = has(e, Sym(im)) || (e.kind == SymJ.NUMBER && !iszero(imag(e.num))) ||
    ((e.kind == SymJ.ADD || e.kind == SymJ.MUL) && !iszero(imag(e.num))) ||
    any(_has_imaginary, e.args) || any(_has_imaginary, e.exps)
FUNCS["ActivateTrig"] = u -> _activate_hyperbolic(_unshift(_s(u)))

# FunctionOfTrig[u, v, x]: the common linear argument (up to a rational factor) of the
# trig and hyperbolic functions in u, :null when there are none, false when x appears
# outside them or the arguments are not commensurate
function _function_of_trig(u, v, x)
    u isa Sym || return v
    isempty(u.args) && return isequal(u, x) ? false : v
    if u.kind == SymJ.FN && length(u.args) == 1 && (u.name in _TRIG || u.name in _HYPERBOLIC) && _linear_in(u.args[1], x)
        w = u.name in _TRIG ? u.args[1] : Sym(im) * u.args[1]
        v === :null && return w
        C = FUNCS["Coefficient"]
        a, b, c, d = C(v, x, Sym(0)), C(v, x, Sym(1)), C(w, x, Sym(0)), C(w, x, Sym(1))
        q = b / d
        (_eq(a * d - b * c, 0) && _isrational(q)) || return false
        n = Sym(numerator(_rat(q)))
        return a / n + b * x / n
    end
    u.kind == SymJ.FN && u.name in (:Int, :Derivative) && return false
    w = v
    for a in Iterators.flatten((u.args, u.exps))
        w = _function_of_trig(a, w, x)
        w === false && return false
    end
    w
end

# AlgebraicTrigFunctionQ[u, x]: u is built with +, * and powers free of x from constants,
# x, and trig and hyperbolic functions of linear functions of x
function _algebraic_trig(u, x)
    u isa Sym || return true
    has(u, x) || return true
    k = u.kind
    k == SymJ.SYMBOL && return true
    if k == SymJ.FN
        return length(u.args) == 1 && (u.name in _TRIG || u.name in _HYPERBOLIC) && _linear_in(u.args[1], x)
    end
    k == SymJ.POW && return !has(u.args[2], x) && _algebraic_trig(u.args[1], x)
    all(e -> !has(e, x), u.exps) && all(a -> _algebraic_trig(a, x), u.args)
end

const _FOTL = Ref{Any}(nothing)
function _fotl_pattern()
    _FOTL[] === nothing || return _FOTL[]
    trig = Any["trig_", Any["Add", "e.", Any["Multiply", "f.", "x_"]]]
    p = Any["Multiply", Any["Power", Any["Add", "c.", Any["Multiply", "d.", "x_"]], "m."],
        Any["Power", Any["Add", "a.", Any["Multiply", "b.", trig]], "n."]]
    _FOTL[] = SymJ.pattern(pat(p))
end

function _function_of_trig_of_linear(u, x)
    u = _s(u)
    for m in eachmatch(_fotl_pattern(), u)
        n = _fname(m[:trig])
        (n in _TRIG || n in _HYPERBOLIC) || continue
        all(k -> k === :trig || !has(_s(m[k]), x), keys(m)) && return true
    end
    w = _function_of_trig(u, :null, x)
    w !== :null && w !== false && _algebraic_trig(u, x)
end
FUNCS["FunctionOfTrigOfLinearQ"] = (u, x) -> _function_of_trig_of_linear(_s(u), _s(x))
FUNCS["FunctionOfTrig"] = (u, v, x) -> (w = _function_of_trig(_s(u), v === nothing ? :null : v, _s(x)); w === :null ? nothing : w)

# (ours: the rule from 4.1.0.1 changes nothing here unless u has a hyperbolic function)
_has_hyperbolic(u) = u isa Sym && ((u.kind == SymJ.FN && u.name in _HYPERBOLIC) ||
    any(_has_hyperbolic, u.args) || any(_has_hyperbolic, u.exps))
FUNCS["HasHyperbolicQ"] = u -> _has_hyperbolic(_s(u))

# Mathematica writes an integer negative power of a trig or hyperbolic function as a
# power of its reciprocal (1/Sin[x] is Csc[x]); SymJ keeps sin(x)^-1. Our trig functions
# are both RUBI's active and inert ones, and integrands do better left as they are (RUBI's
# inert-trig rules take cos^2/sin^3; with csc^3 it went to the active-trig rules of 4.7.9,
# many of which OSR does not have). _mma_trig is not applied to integrands for now; the
# reciprocal table is used for hyperbolic powers in _deactivate_trig.
const _RECIP = Dict(:sin => :csc, :cos => :sec, :tan => :cot, :cot => :tan, :sec => :cos, :csc => :sin,
    :sinh => :csch, :cosh => :sech, :tanh => :coth, :coth => :tanh, :sech => :cosh, :csch => :sinh)
function _mma_trig(u)
    u isa Sym || return u
    isempty(u.args) && return u
    if u.kind == SymJ.POW
        b, e = u.args
        if b.kind == SymJ.FN && haskey(_RECIP, b.name) && length(b.args) == 1 && _isinteger(e) && _rat(e) < 0
            return apply_function(_RECIP[b.name], Sym[_mma_trig(b.args[1])])^(-e)
        end
    elseif u.kind == SymJ.MUL
        any(i -> (b = u.args[i]; b.kind == SymJ.FN && haskey(_RECIP, b.name) && _isinteger(u.exps[i]) && _rat(u.exps[i]) < 0), eachindex(u.args)) ||
            return SymJ._rw_parts(_mma_trig, u)
        fs = [_mma_trig(b^e) for (b, e) in zip(u.args, u.exps)]
        return Sym(u.num) * prod(fs)
    end
    SymJ._rw_parts(_mma_trig, u)
end
_has_trig_fn(u) = u isa Sym && ((u.kind == SymJ.FN && haskey(_RECIP, u.name)) || any(_has_trig_fn, u.args) || any(_has_trig_fn, u.exps))
FUNCS["HasTrigQ"] = u -> _has_trig_fn(_s(u))

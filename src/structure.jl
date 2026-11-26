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
# InverseFunctionQ[u]: u is a log, an inverse trig or hyperbolic function, or a polylog
FUNCS["InverseFunctionQ"] = function (u)
    v = _s(u)
    v.kind == SymJ.FN && v.name in _INVERSE && !(v.name in (:_₂F₁, :AppellF1))
end

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
# ActivateTrig stays as in utilities.jl, the identity: rules apply it to a part of their
# result only (4.3.7 #15: ActivateTrig[u] (b tan^n)^p ...), so shifting back there would
# leave tan(v + π/2) and cot(v) side by side; _tidy_result shifts the answer back.

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

# TrigToExp[u]: trig and hyperbolic functions as exponentials; ExpandTrigToExp[u, v, x]:
# u times that of v, expanded (RUBI uses it where F^(c (a + b x)) sinh(d + e x)^n has
# e^2 = b^2 c^2 log(F)^2, so that exponentials cancel: e^x sinh(x) = (e^(2x) - 1)/2)
const _EULER = SymJ.E
function _trig_to_exp(u)
    u isa Sym || return u
    isempty(u.args) && return u
    if u.kind == SymJ.FN && length(u.args) == 1
        z = _trig_to_exp(u.args[1])
        ep, em = _EULER^z, _EULER^(-z)
        I = Sym(im); jp, jm = _EULER^(I * z), _EULER^(-I * z)
        n = u.name
        n === :sinh && return (ep - em) / 2
        n === :cosh && return (ep + em) / 2
        n === :tanh && return (ep - em) / (ep + em)
        n === :coth && return (ep + em) / (ep - em)
        n === :sech && return 2 / (ep + em)
        n === :csch && return 2 / (ep - em)
        n === :sin && return (jp - jm) / (2I)
        n === :cos && return (jp + jm) / 2
        n === :tan && return (jp - jm) / (I * (jp + jm))
        n === :cot && return I * (jp + jm) / (jp - jm)
        n === :sec && return 2 / (jp + jm)
        n === :csc && return 2I / (jp - jm)
    end
    SymJ._rw_parts(_trig_to_exp, u)
end
FUNCS["TrigToExp"] = u -> _trig_to_exp(_s(u))
FUNCS["ExpandTrigToExp"] = function (args...)
    u, v = length(args) == 2 ? (SymJ.ONE, _s(args[1])) : (_s(args[1]), _s(args[2]))
    expand(u * _trig_to_exp(v))
end

# ---- functions of exponentials: FunctionOfExponentialQ, FunctionOfExponential,
# FunctionOfExponentialFunction (after IntegrationUtilityFunctions.m). u is a function
# of F^v, v linear in x, when x appears only in exponentials F^(a + b x) (and hyperbolic
# functions of linear arguments, as exponentials) whose exponents are rational multiples
# of one another. Then v = F^(b x/D) for one of them, and each exponential is a constant
# times a power of v. (RUBI keeps the constant term of v in some cases; v here has none,
# which is the same substitution up to a constant factor.)

# the exponentials of u: (base, exponent) pairs, `false` when x appears elsewhere;
# `flag` is set when there is an explicit exponential
function _foe_collect!(acc, u, x, flag::Ref{Bool})
    u isa Sym || return true
    has(u, x) || return true
    isequal(u, x) && return false
    k = u.kind
    if k == SymJ.FN
        u.name in (:Int, :Derivative) && return false
        if u.name in _HYPERBOLIC && length(u.args) == 1 && _linear_in(u.args[1], x)
            push!(acc, (SymJ.E, u.args[1])); return true
        end
        return all(a -> _foe_collect!(acc, a, x, flag), u.args)
    elseif k == SymJ.POW
        b, e = u.args
        if !has(b, x)
            _linear_in(e, x) || return false
            flag[] = true; push!(acc, (b, e)); return true
        end
        has(e, x) && return false
        return _foe_collect!(acc, b, x, flag)
    elseif k == SymJ.MUL
        for (b, e) in zip(u.args, u.exps)
            if !has(b, x) && has(e, x)
                _linear_in(e, x) || return false
                flag[] = true; push!(acc, (b, e))
            else
                has(e, x) && return false
                _foe_collect!(acc, b, x, flag) || return false
            end
        end
        return true
    end
    all(a -> _foe_collect!(acc, a, x, flag), u.args)
end

# the substitution: (base, unit exponent w with v = base^w, D), or nothing
function _foe(u, x)
    acc, flag = Tuple{Sym,Sym}[], Ref(false)
    _foe_collect!(acc, _s(u), x, flag) || return nothing
    (flag[] && !isempty(acc)) || return nothing
    C = FUNCS["Coefficient"]
    B0, w0 = acc[1]
    e1 = C(w0, x, Sym(1))
    D = 1
    for (B, w) in acc
        r = cancel(log(B) * C(w, x, Sym(1)) / (log(B0) * e1))
        _isrational(r) || return nothing
        D = lcm(D, Int(denominator(_rat(r))))
    end
    (B0, e1 * x / D, D)
end

FUNCS["FunctionOfExponentialQ"] = (u, x) -> _foe(_s(u), _s(x)) !== nothing
FUNCS["FunctionOfExponential"] = function (u, x)
    s = _foe(_s(u), _s(x)); s === nothing && throw(OSRError("FunctionOfExponential"))
    s[1]^s[2]
end

# u with each exponential written as a constant times a power of x (the new variable)
function _foe_replace(u, x, B0, w)
    u isa Sym || return u
    has(u, x) || return u
    C = FUNCS["Coefficient"]
    unit = log(B0) * C(w, x, Sym(1))                  # log of v per unit of x
    pw(B, e) = B^C(e, x, Sym(0)) * x^cancel(log(B) * C(e, x, Sym(1)) / unit)
    k = u.kind
    if k == SymJ.FN && u.name in _HYPERBOLIC && length(u.args) == 1 && _linear_in(u.args[1], x)
        return _foe_replace(_trig_to_exp(u), x, B0, w)
    elseif k == SymJ.POW && !has(u.args[1], x)
        return pw(u.args[1], u.args[2])
    elseif k == SymJ.MUL
        return Sym(u.num) * prod((!has(b, x) && has(e, x)) ? pw(b, e) : _foe_replace(b, x, B0, w)^e
                                 for (b, e) in zip(u.args, u.exps); init = SymJ.ONE)
    end
    SymJ._rw_parts(a -> _foe_replace(a, x, B0, w), u)
end
FUNCS["FunctionOfExponentialFunction"] = function (u, x)
    x = _s(x); s = _foe(_s(u), x); s === nothing && throw(OSRError("FunctionOfExponentialFunction"))
    _simplify_integrand(_foe_replace(_s(u), x, s[1], s[2]))
end

FUNCS["D"] = (u, x) -> diff(_s(u), _s(x))

# (ours: the two exclusions of RUBI's rule, Not[MatchQ[u, w_*(a_.*v_^n_)^m_ /; FreeQ[{a,
# m, n}, x] && IntegerQ[m*n]]] and Not[MatchQ[u, E^(c_.*(a_. + b_.*x))*F_[v_] /;
# InverseFunctionQ[F[x]]]]: a power of a power with an integer total exponent, and an
# exponential times an inverse function, are left to other rules)
function _foe_excluded(u, x)
    for f in _factors(u)
        f.kind == SymJ.POW && f.args[1].kind == SymJ.MUL && _isinteger(f.args[2]) &&
            any(e -> !_isinteger(e) && _isinteger(e * f.args[2]), f.args[1].exps) && return true
        f.kind == SymJ.FN && f.name in _INVERSE && return true
    end
    false
end
FUNCS["FunctionOfExponentialExcludedQ"] = (u, x) -> _foe_excluded(_s(u), _s(x))

# ---- SubstFor[v, u, x]: u as a function of v, with x standing for v; FunctionOfQ[v, u,
# x]: u is a function of v (after IntegrationUtilityFunctions.m, for v that is not a trig
# or hyperbolic function: those, RUBI's SubstForTrig and SubstForHyperbolic, are not
# done here, so SubstFor rejects the rule and FunctionOfQ is false)

const _T = Sym(:𝓉)          # the new variable while substituting

# SubstForAux[u, v, x]: occurrences of v, and of powers of v's base, as powers of _T
function _subst_for_aux(u::Sym, v::Sym, x::Sym)
    isequal(u, v) && return _T
    if isempty(u.args)
        v.kind == SymJ.POW && !has(v.args[2], x) && isequal(u, v.args[1]) && return _T^(1 / v.args[2])
        return u
    end
    if u.kind == SymJ.POW && !has(u.args[2], x)
        b, e = u.args
        isequal(b, v) && return _T^e
        v.kind == SymJ.POW && !has(v.args[2], x) && isequal(b, v.args[1]) && return _T^cancel(e / v.args[2])
        return _subst_for_aux(b, v, x)^e
    end
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, x)
        isone(c) || return c * _subst_for_aux(FUNCS["NonfreeFactors"](u, x), v, x)
        return prod((_subst_for_aux(isone(e) ? b : b^e, v, x) for (b, e) in zip(u.args, u.exps)); init = SymJ.ONE)
    end
    SymJ._rw_parts(a -> _subst_for_aux(a, v, x), u)
end

# u in terms of v, as an expression in _T; nothing when x is left
function _subst_for(v, u, x)
    v, u, x = _s(v), _s(u), _s(x)
    (v.kind == SymJ.FN && (v.name in _TRIG || v.name in _HYPERBOLIC)) && return nothing
    isempty(v.args) && return subs(u, v => _T)                  # an atom
    c = FUNCS["FreeFactors"](v, x)
    if v.kind == SymJ.MUL && !isone(c)                         # SubstFor[w, u, x/c] with v = c w
        w = _subst_for(FUNCS["NonfreeFactors"](v, x), u, x)
        return w === nothing ? nothing : subs(w, _T => _T / c)
    end
    if _linear_in(v, x)                                         # x = (t - a)/b, exactly
        a, b = FUNCS["Coefficient"](v, x, Sym(0)), FUNCS["Coefficient"](v, x, Sym(1))
        return subs(u, x => (_T - a) / b)
    end
    w = _subst_for_aux(u, v, x)
    has(w, x) ? nothing : w
end

FUNCS["SubstFor"] = function (args...)
    w = length(args) == 4 ? _s(args[1]) : SymJ.ONE
    v, u, x = length(args) == 4 ? args[2:4] : args
    r = _subst_for(v, u, x)
    r === nothing && throw(OSRError("SubstFor: not a function of $v"))
    _simplify_integrand(w * subs(r, _T => _s(x)))
end

# FunctionOfExpnQ[u, v, x]: u is a function of v (v not a trig or hyperbolic function):
# the degree, as a rational, or false. Powers of v's base must be integer multiples of
# v's power.
function _function_of_expn(u::Sym, v::Sym, x::Sym)
    isequal(u, v) && return 1 // 1
    isempty(u.args) && return isequal(u, x) ? false : 0 // 1
    u.kind == SymJ.FN && u.name in (:Int, :Derivative) && return false
    if u.kind == SymJ.POW && !has(u.args[2], x)
        b, e = u.args
        isequal(b, v) && return _isinteger(e) ? _rat(e) : 1 // 1
        if v.kind == SymJ.POW && !has(v.args[2], x) && isequal(b, v.args[1])
            ve = v.args[2]
            if _isrational(ve)
                (_isrational(e) && isinteger(_rat(e) / _rat(ve)) && (_rat(ve) > 0 || _rat(e) < 0)) || return false
                return _rat(e) / _rat(ve)
            end
            q = cancel(e / ve)
            return _isinteger(q) ? _rat(q) : false
        end
        return _function_of_expn(b, v, x)
    end
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, x)
        isone(c) || return _function_of_expn(FUNCS["NonfreeFactors"](u, x), v, x)
        parts = [isone(e) ? b : b^e for (b, e) in zip(u.args, u.exps)]
    elseif u.kind == SymJ.ADD
        parts = _terms(u)
    else
        parts = u.args
    end
    g = 0 // 1
    for p in parts
        d = _function_of_expn(p, v, x)
        d === false && return false
        g = gcd(g, d)
    end
    g
end

FUNCS["FunctionOfQ"] = function (v, u, x, pure = false)
    v, u, x = _s(v), _s(u), _s(x)
    has(u, x) || return false
    isempty(v.args) && return true
    c = FUNCS["FreeFactors"](v, x)
    v.kind == SymJ.MUL && !isone(c) && (v = FUNCS["NonfreeFactors"](v, x))
    (v.kind == SymJ.FN && (v.name in _TRIG || v.name in _HYPERBOLIC)) && return false   # (not done)
    _function_of_expn(u, v, x) !== false
end
FUNCS["FunctionOfExpnQ"] = (u, v, x) -> (d = _function_of_expn(_s(u), _s(v), _s(x)); d === false ? false : Sym(d))

# ---- more of RUBI's algebraic predicates and normalizations (IntegrationUtilityFunctions.m).
# (PowerOfLinearQ, PowerOfLinearMatchQ and NormalizePowerOfLinear, used by four rules, are
# not defined in RUBI 4.16.1: in Mathematica the conditions stay unevaluated and the rules
# never apply, so they are left unsupported here, which comes to the same.)

_Rt(u, n) = FUNCS["Rt"](_s(u), Sym(n))

# FractionalPowerFactorQ[u]: u has a factor with a fractional power (or is complex)
function _fractional_power_factor(u)
    u isa Sym || return false
    u.kind == SymJ.NUMBER && return !iszero(imag(u.num))
    u.kind == SymJ.POW && return _isrational(u.args[2]) && !_isinteger(u.args[2])
    u.kind == SymJ.MUL && return any(e -> _isrational(e) && !_isinteger(e), u.exps) || any(_fractional_power_factor, u.args)
    false
end
FUNCS["FractionalPowerFactorQ"] = u -> _fractional_power_factor(_s(u))
FUNCS["NiceSqrtQ"] = u -> (u = _s(u); _isrational(u) ? _rat(u) > 0 : !_fractional_power_factor(_Rt(u, 2)))

# SimplerSqrtQ[u, v]: Sqrt[u] is simpler than Sqrt[v]
function _simpler_sqrt(u, v)
    lt(a) = FUNCS["LtQ"](a, Sym(0))
    lt(v) && !lt(u) && return true
    lt(u) && !lt(v) && return false
    su, sv = _Rt(u, 2), _Rt(v, 2)
    if _isinteger(su)
        return _isinteger(sv) ? _rat(su) < _rat(sv) : true
    end
    _isinteger(sv) && return false
    if _isrational(su)
        return _isrational(sv) ? _rat(su) < _rat(sv) : true
    end
    _isrational(sv) && return false
    P = FUNCS["PosQ"]
    if P(u)
        return P(v) ? leafcount(su) < leafcount(sv) : true
    end
    P(v) && return false
    leafcount(su) < leafcount(sv) && return true
    leafcount(sv) < leafcount(su) && return false
    string(u) < string(v)          # (Not[OrderedQ[{v, u}]]: an order of expressions, approximate)
end
FUNCS["SimplerSqrtQ"] = (u, v) -> _simpler_sqrt(_s(u), _s(v))

# AlgebraicFunctionQ[u, x, flag]: built from x with +, * and rational powers (any power
# free of x with flag)
function _algebraic_function(u, x, flag)
    u isa Sym || (u isa AbstractVector && return all(a -> _algebraic_function(a, x, flag), u)) || return true
    (isempty(u.args) || !has(u, x)) && return true
    if u.kind == SymJ.POW
        e = u.args[2]
        return (_isrational(e) || (flag && !has(e, x))) && _algebraic_function(u.args[1], x, flag)
    end
    if u.kind == SymJ.MUL
        return all(e -> _isrational(e) || (flag && !has(e, x)), u.exps) && all(a -> _algebraic_function(a, x, flag), u.args)
    end
    u.kind == SymJ.ADD && return all(a -> _algebraic_function(a, x, flag), u.args)
    false
end
FUNCS["AlgebraicFunctionQ"] = (u, x, flag = false) -> _algebraic_function(u isa AbstractVector ? u : _s(u), _s(x), flag === true)

FUNCS["BinomialDegree"] = (u, x) -> (p = _binomial_parts(_s(u), _s(x)); p === nothing ? throw(OSRError("BinomialDegree")) : p[3])

# TrinomialParts[u, x]: (a, b, c, n) with u = a + b x^n + c x^(2n), or nothing
function _trinomial_parts(u::Sym, x::Sym)
    cs = FUNCS["PolyQ"](u, x) ? _coeffs(u, x) : nothing
    if cs !== nothing
        L = length(cs)
        (L < 3 || iseven(L) || _eq(cs[(L+1)÷2], 0)) && return nothing
        all(i -> i in (1, (L+1)÷2, L) || _eq(cs[i], 0), 1:L) || return nothing
        return (cs[1], cs[(L+1)÷2], cs[L], Sym((L - 1) ÷ 2))
    end
    if u.kind == SymJ.POW && _eq(u.args[2], 2)
        p = _binomial_parts(u.args[1], x)
        (p === nothing || _eq(p[1], 0)) && return nothing
        return (p[1]^2, 2p[1] * p[2], p[2]^2, p[3])
    end
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, x)
        if !isone(c)
            t = _trinomial_parts(FUNCS["NonfreeFactors"](u, x), x)
            return t === nothing ? nothing : (c * t[1], c * t[2], c * t[3], t[4])
        end
        fs = _factors(u); length(fs) == 2 || return nothing
        p, q = _binomial_parts(fs[1], x), _binomial_parts(fs[2], x)
        (p === nothing || q === nothing) && return nothing
        (a, b, m), (c2, d, n) = p, q
        (_eq(m, n) && !_eq(a * d + b * c2, 0)) || return nothing
        return (a * c2, a * d + b * c2, b * d, m)
    end
    if u.kind == SymJ.ADD
        f = FUNCS["FreeTerms"](u, x)
        if !iszero(f)
            t = _trinomial_parts(FUNCS["NonfreeTerms"](u, x), x)
            return t === nothing ? nothing : (f + t[1], t[2], t[3], t[4])
        end
        ms = _monomials(u, x)
        ms === nothing && return nothing
        ks = [k for k in keys(ms) if !iszero(k)]
        length(ks) == 2 || return nothing
        n, j = _eq(ks[2], 2ks[1]) ? (ks[1], ks[2]) : _eq(ks[1], 2ks[2]) ? (ks[2], ks[1]) : (nothing, nothing)
        n === nothing && return nothing
        return (get(ms, SymJ.ZERO, SymJ.ZERO), ms[n], ms[j], n)
    end
    nothing
end
FUNCS["TrinomialQ"] = (u, x) -> _each(u) do v
    v = _s(v); x = _s(x)
    _trinomial_parts(v, x) !== nothing && !FUNCS["QuadraticQ"](v, x) &&
        !(v.kind == SymJ.POW && _eq(v.args[2], 2) && _binomial_parts(v.args[1], x) !== nothing)
end
# TrinomialMatchQ[u, x]: a. + b. x^n. + c. x^j. with j = 2 n (syntactic)
FUNCS["TrinomialMatchQ"] = (u, x) -> _each(u) do v
    ms = _monomials(_s(v), _s(x)); ms === nothing && return false
    ks = [k for k in keys(ms) if !iszero(k)]
    length(ks) == 2 && (_eq(ks[2], 2ks[1]) || _eq(ks[1], 2ks[2]))
end

# GeneralizedBinomialParts[u, x]: (a, b, n, q) with u = a x^q + b x^n, n - q > 0
# (every term has a power of x: a x^q + b x^n, unlike a binomial, has no constant term)
function _gen_binomial_parts(u::Sym, x::Sym)
    ms = _monomials(u, x)
    if ms !== nothing && length(ms) == 2 && !any(iszero, keys(ms))
        (q, a), (n, b) = collect(ms)
        if !FUNCS["PosQ"](n - q)
            q, a, n, b = n, b, q, a
        end
        FUNCS["PosQ"](n - q) && return (a, b, n, q)
    end
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, x)
        if !isone(c)
            t = _gen_binomial_parts(FUNCS["NonfreeFactors"](u, x), x)
            return t === nothing ? nothing : (c * t[1], c * t[2], t[3], t[4])
        end
        for (i, f) in enumerate(_factors(u))
            m = _monomial(f, x); (m === nothing || !isone(m[1])) && continue
            rest = prod(g for (j, g) in enumerate(_factors(u)) if j != i; init = SymJ.ONE)
            t = _gen_binomial_parts(rest, x)
            t !== nothing && !_eq(m[2] + t[3], 0) && !_eq(m[2] + t[4], 0) && return (t[1], t[2], m[2] + t[3], m[2] + t[4])
            p = _binomial_parts(rest, x)
            p !== nothing && !_eq(m[2] + p[3], 0) && return (p[1], p[2], m[2] + p[3], m[2])
        end
    end
    nothing
end
FUNCS["GeneralizedBinomialQ"] = (u, x) -> _each(v -> _gen_binomial_parts(_s(v), _s(x)) !== nothing, u)
FUNCS["GeneralizedBinomialMatchQ"] = (u, x) -> _each(u) do v
    ms = _monomials(_s(v), _s(x)); ms !== nothing && length(ms) == 2 && !any(iszero, keys(ms))
end

# GeneralizedTrinomialParts[u, x]: (a, b, c, n, q) with u = a x^q + b x^n + c x^(2n - q)
function _gen_trinomial_parts(u::Sym, x::Sym)
    ms = _monomials(u, x)
    if ms !== nothing && length(ms) == 3 && !any(iszero, keys(ms))
        ks = collect(keys(ms))
        for q in ks, n in ks, r in ks
            length(unique([q, n, r])) == 3 || continue
            _eq(r, 2n - q) || continue
            # (the term with exponent q first: RUBI's pattern a x^q + b x^n + c x^r)
            FUNCS["PosQ"](n - q) || continue
            return (ms[q], ms[n], ms[r], n, q)
        end
    end
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, x)
        if !isone(c)
            t = _gen_trinomial_parts(FUNCS["NonfreeFactors"](u, x), x)
            return t === nothing ? nothing : (c * t[1], c * t[2], c * t[3], t[4], t[5])
        end
        for (i, f) in enumerate(_factors(u))
            m = _monomial(f, x); (m === nothing || !isone(m[1])) && continue
            rest = prod(g for (j, g) in enumerate(_factors(u)) if j != i; init = SymJ.ONE)
            t = _gen_trinomial_parts(rest, x)
            t !== nothing && !_eq(m[2] + t[4], 0) && !_eq(m[2] + t[5], 0) && return (t[1], t[2], t[3], m[2] + t[4], m[2] + t[5])
            p = _trinomial_parts(rest, x)
            p !== nothing && !_eq(m[2] + p[4], 0) && return (p[1], p[2], p[3], m[2] + p[4], m[2])
        end
    end
    nothing
end
FUNCS["GeneralizedTrinomialQ"] = (u, x) -> _each(v -> _gen_trinomial_parts(_s(v), _s(x)) !== nothing, u)
FUNCS["GeneralizedTrinomialMatchQ"] = (u, x) -> _each(u) do v
    ms = _monomials(_s(v), _s(x)); ms === nothing && return false
    (length(ms) == 3 && !any(iszero, keys(ms))) || return false
    ks = collect(keys(ms))
    any(_eq(r, 2n - q) for q in ks, n in ks, r in ks if length(unique([q, n, r])) == 3)
end
FUNCS["GeneralizedTrinomialDegree"] = (u, x) -> (t = _gen_trinomial_parts(_s(u), _s(x));
    t === nothing ? throw(OSRError("GeneralizedTrinomialDegree")) : t[4] - t[5])

# PseudoBinomialParts[u, x]: (a, 1, c, d, n) with u = a + (c + d x)^n, n > 2
function _pseudo_binomial_parts(u::Sym, x::Sym)
    FUNCS["PolyQ"](u, x) || return nothing
    cs = _coeffs(u, x); n = length(cs) - 1
    n > 2 || return nothing
    d = _Rt(cs[n+1], n)
    c = cs[n] / (n * d^(n - 1))
    a = expand(u - (c + d * x)^n)
    (!_eq(a, 0) && !has(a, x)) || return nothing
    (a, SymJ.ONE, c, d, Sym(n))
end
FUNCS["PseudoBinomialPairQ"] = function (u, v, x)
    p, q = _pseudo_binomial_parts(_s(u), _s(x)), _pseudo_binomial_parts(_s(v), _s(x))
    p !== nothing && q !== nothing && all(i -> isequal(p[i], q[i]), 3:5)
end
FUNCS["NormalizePseudoBinomial"] = (u, x) -> (p = _pseudo_binomial_parts(_s(u), _s(x));
    p === nothing ? throw(OSRError("NormalizePseudoBinomial")) : p[1] + p[2] * (p[3] + p[4] * _s(x))^p[5])

# PolynomialDivide[u, v, x]: quotient + remainder/v; [u, v, w, x]: the same in w
function _polynomial_divide(u, v, x)
    q, r = _divrem(u, v, x)
    q + cancel(r) / v
end
FUNCS["PolynomialDivide"] = function (args...)
    length(args) == 3 && return _polynomial_divide(_s(args[1]), _s(args[2]), _s(args[3]))
    u, v, w, x = map(_s, args)
    su, sv = _subst_for(w, u, x), _subst_for(w, v, x)
    (su === nothing || sv === nothing) && throw(OSRError("PolynomialDivide"))
    subs(_polynomial_divide(su, sv, _T), _T => w)
end

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

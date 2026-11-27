# NormalizeIntegrand (IntegrationUtilityFunctions.m, RUBI 4.16.1): u in the form RUBI's
# rules expect, for 9.3's Int[u, x] := With[{v = NormalizeIntegrand[u, x]}, Int[v, x] /;
# UnsameQ[v, u]]. It collects like powers of x (a x^n + b x^n is (a + b) x^n), takes the
# least power of x out of a sum of monomials (a x^2 + b x^3 is x^2 (a + b x)), merges
# powers of proportional linear factors, and simplifies sums that are not polynomials
# (sin x + sin^2 x is sin x (1 + sin x)).

_sumq(u::Sym) = u.kind == SymJ.ADD
_productq(u::Sym) = u.kind == SymJ.MUL && length(_factors(u)) > 1

# MonomialQ[u, x]: u is a x^n, a and n free of x (x itself present)
_monomialq(u::Sym, x::Sym) = (m = _monomial(u, x); m !== nothing && !iszero(m[2]))
# MinimumMonomialExponent[u, x], u a sum of monomials
function _min_monomial_exponent(u::Sym, x::Sym)
    es = [_monomial(t, x)[2] for t in _terms(u)]
    n = es[1]
    for e in es[2:end]
        FUNCS["PosQ"](n - e) && (n = e)
    end
    n
end

# ExpandToSum[u, x] for a sum, with like powers of x collected (a x^n + b x^n = (a + b) x^n);
# u when its terms are not all monomials
function _collect_powers(u::Sym, x::Sym)
    v = expand(u)
    ms = _monomials(v, x)
    ms === nothing && return v
    sum(c * (iszero(k) ? SymJ.ONE : x^k) for (k, c) in ms; init = SymJ.ZERO)
end
# BinomialMatchQ and TrinomialMatchQ are syntactic in Mathematica: each power of x in one
# term (a x^n + b x^n is a binomial, but does not match a. + b. x^n.)
_distinct_powers(u::Sym, x::Sym) = (ms = _monomials(u, x); ms !== nothing && length(ms) == length(_terms(u)))

# TogetherSimplify[u]. Mathematica's Simplify also tries the factored form, and keeps it
# when it is no larger (Sin[x] + Sin[x]^2 is Sin[x] (1 + Sin[x])); SymJ's simplify does not,
# so factor is tried here, on sums small enough for it to be quick (it is not interruptible)
function _together_simplify(u::Sym)
    v = cancel(SymJ.simplify(cancel(u)))
    (_sumq(v) && leafcount(v) <= 40) || return v
    f = try factor(v) catch; v end
    f isa Sym && leafcount(f) <= leafcount(v) ? f : v
end

# UnifySum[u, x]: the terms of the sum u whose ratio is free of x combined
function _unify_sum(u::Sym, x::Sym)
    ts = Sym[]
    for t in reverse(_terms(u))                  # UnifyTerms works from the last term
        i = findfirst(s -> (r = SymJ.simplify(s / t); !has(r, x)), ts)
        if i === nothing
            pushfirst!(ts, t)
        else
            r = SymJ.simplify(ts[i] / t)
            ts[i] = (1 + r) * t
        end
    end
    sum(ts; init = SymJ.ZERO)
end

# MergeMonomials[u, x]: powers of proportional linear factors merged, (a + b x)^m (c + d x)^n
# = b^m/d^m (c + d x)^(m + n) for m an integer and b c = a d; a linear u cancelled
function _merge_monomials(u::Sym, x::Sym)
    if u.kind == SymJ.MUL
        fs = _factors(u)
        base(f) = f.kind == SymJ.POW ? (f.args[1], f.args[2]) : (f, SymJ.ONE)
        C(v, k) = FUNCS["Coefficient"](v, x, Sym(k))
        for i in eachindex(fs), j in eachindex(fs)
            i == j && continue
            (l1, m), (l2, n) = base(fs[i]), base(fs[j])
            (_isinteger(m) && !has(n, x) && _linear_in(l1, x) && _linear_in(l2, x)) || continue
            has(l1, x) && has(l2, x) || continue
            a, b, c, d = C(l1, 0), C(l1, 1), C(l2, 0), C(l2, 1)
            _eq(b * c - a * d, 0) || continue
            rest = prod(fs[k] for k in eachindex(fs) if k != i && k != j; init = SymJ.ONE)
            return rest * b^m / d^m * l2^(m + n)
        end
        return u
    end
    _linear_in(u, x) ? cancel(u) : u
end

# NormalizeIntegrandFactorBase[u, x]
function _nif_base(u::Sym, x::Sym)
    # x^m (a + b + …): x^m distributed over the sum
    if u.kind == SymJ.MUL
        fs = _factors(u)
        if length(fs) == 2
            for (p, s) in ((fs[1], fs[2]), (fs[2], fs[1]))
                if _sumq(s) && (isequal(p, x) || (p.kind == SymJ.POW && isequal(p.args[1], x) && !has(p.args[2], x)))
                    return _nif_base(sum(t -> p * t, _terms(s)), x)
                end
            end
        end
    end
    if FUNCS["BinomialQ"](u, x) || FUNCS["TrinomialQ"](u, x)
        return _distinct_powers(u, x) ? u : _collect_powers(u, x)
    end
    _productq(u) && return prod(f -> _nif(f, x), _factors(u); init = SymJ.ONE)
    if FUNCS["PolynomialQ"](u, x) && (e = try FUNCS["Expon"](u, x) catch; nothing end; e !== nothing && _rat(e) <= 4)
        return _collect_powers(u, x)
    end
    if _sumq(u)
        v = _together_simplify(u)
        # MatchQ[v, x^m_. w_ /; FreeQ[m, x] && SumQ[w]]: v is a power of x times a sum
        fs = _factors(v)
        xm = length(fs) == 2 && any(_sumq, fs) &&
             any(f -> isequal(f, x) || (f.kind == SymJ.POW && isequal(f.args[1], x) && !has(f.args[2], x)), fs)
        if _sumq(v) || xm || leafcount(v) > leafcount(u) + 2
            return _unify_sum(u, x)
        end
        return _nif_base(v, x)
    end
    _atomq(u) ? u : _map_parts(p -> _nif(p, x), u)
end

# NormalizeIntegrandFactor[u, x]
function _nif(u::Sym, x::Sym)
    _check_deadline()
    monos(b) = _sumq(b) && all(t -> _monomialq(t, x), _terms(b))
    if u.kind == SymJ.POW && !has(u.args[2], x)
        bas, deg = _nif_base(u.args[1], x), u.args[2]
        if _isinteger(deg) && monos(bas)
            m = _min_monomial_exponent(bas, x)
            return x^(m * deg) * sum(t -> SymJ.simplify(t / x^m), _terms(bas))^deg
        end
        return bas^deg
    end
    u.kind == SymJ.POW && !has(u.args[1], x) && return u.args[1]^_nif_base(u.args[2], x)
    bas = _nif_base(u, x)
    if monos(bas)
        m = _min_monomial_exponent(bas, x)
        return x^m * sum(t -> t / x^m, _terms(bas))
    end
    bas
end

# NormalizeIntegrandAux[u, x]
function _ni_aux(u::Sym, x::Sym)
    _sumq(u) && return sum(t -> _ni_aux(t, x), _terms(u))
    v = _merge_monomials(u, x)
    _productq(v) ? prod(f -> _nif(f, x), _factors(v); init = SymJ.ONE) : _nif(v, x)
end

# SignOfFactor[u]: (n, v), n = ±1, n v = u, the lead terms of v's sum factors (raised to
# integer powers) positive. Mathematica's first term of a sum is its constant term, if any.
function _lead_negative(s::Sym)
    t = iszero(s.num) ? Sym(s.coefs[1]) : Sym(s.num)
    _isrational(t) && _rat(t) < 0
end
function _sign_of_factor(u::Sym)
    (_isrational(u) && _rat(u) < 0) && return (-1, -u)
    _sumq(u) && _lead_negative(u) && return (-1, -u)
    if u.kind == SymJ.POW && _isinteger(u.args[2]) && _sumq(u.args[1]) && _lead_negative(u.args[1])
        k = _rat(u.args[2])
        return (isodd(k) ? -1 : 1, (-u.args[1])^u.args[2])
    end
    if _productq(u)
        n, v = 1, SymJ.ONE
        for f in _factors(u)
            s, w = _sign_of_factor(f)
            n *= s; v *= w
        end
        return (n, v)
    end
    (1, u)
end
# AbsorbMinusSign[u]: -u, with the sign taken into a sum factor (raised to an odd power)
function _absorb_minus_sign(u::Sym)
    for f in _factors(u)
        if _sumq(f) || (f.kind == SymJ.POW && _sumq(f.args[1]) && _isinteger(f.args[2]) && isodd(_rat(f.args[2])))
            s = f.kind == SymJ.POW ? f.args[1] : f
            e = f.kind == SymJ.POW ? f.args[2] : SymJ.ONE
            return (u / f) * (-s)^e
        end
    end
    -u
end
function _normalize_lead_term_signs(u::Sym)
    n, v = _sign_of_factor(u)
    n == 1 ? v : _absorb_minus_sign(v)
end

# NormalizeIntegrand[u, x]: u itself when only the signs of its lead terms change
function _normalize_integrand(u::Sym, x::Sym)
    v = _normalize_lead_term_signs(_ni_aux(u, x))
    isequal(v, _normalize_lead_term_signs(u)) ? u : v
end

FUNCS["NormalizeIntegrand"] = (u, x) -> _normalize_integrand(_s(u), _s(x))
FUNCS["UnsameQ"] = (u, v) -> !isequal(_s(u), _s(v))
FUNCS["SameQ"] = (u, v) -> isequal(_s(u), _s(v))

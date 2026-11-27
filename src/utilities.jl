# RUBI's utility functions used on the right side of rules. RUBI's versions also choose
# the *form* of an answer (Simp, ExpandIntegrand, ...); these first versions keep the
# value and leave the form to SymJ's canonical form, so an answer may look different
# from RUBI's optimal one while being equal to it. Each approximation is marked.

using SymJ: expand, cancel, apart, subs

# giving up: Unintegrable[u, x] and CannotIntegrate[u, x] stop the integration
struct GiveUp <: Exception
    integrand::Any
end

FUNCS["Unintegrable"] = (u, x) -> throw(GiveUp(u))
FUNCS["CannotIntegrate"] = (u, x) -> throw(GiveUp(u))

# Int[u, x]: integrate, recursively
SPECIAL["Int"] = (as, c) -> begin
    u = _s(ev(as[1], c))
    v = ev(as[2], c)
    v == X || throw(OSRError("Int in a variable other than x"))
    _int(u, c.depth + 1)
end
# IntHide[u, x]: Int, with its steps hidden when RUBI shows steps
SPECIAL["IntHide"] = SPECIAL["Int"]

# substitution: Subst[u, x, v] and Subst[u, x -> v]
FUNCS["Rule"] = (a, b) -> (_s(a) => _s(b))
FUNCS["Subst"] = function (u, a, b = nothing)
    p = b === nothing ? a : (_s(a) => _s(b))
    subs(_s(u), p)
end

# simplification: the value is kept, the form is SymJ's (approximate)
FUNCS["Simp"] = (u, x = nothing) -> _s(u)
FUNCS["Dist"] = (u, v, x = nothing) -> _s(u) * _s(v)
FUNCS["Simplify"] = u -> SymJ.simplify(_s(u))
FUNCS["FullSimplify"] = u -> SymJ.simplify(_s(u))
FUNCS["Together"] = u -> cancel(_s(u))
FUNCS["Cancel"] = u -> cancel(_s(u))
FUNCS["Expand"] = (u, x = nothing) -> expand(_s(u))
FUNCS["SimplifyIntegrand"] = (u, x) -> _simplify_integrand(_s(u))
FUNCS["ActivateTrig"] = u -> _s(u)
FUNCS["DeactivateTrig"] = (u, x = nothing) -> _s(u)
FUNCS["Numerator"] = u -> numerator(_s(u))
FUNCS["Denominator"] = u -> denominator(_s(u))
function _simplify_integrand(u)
    v = cancel(u)
    w = leafcount(v) <= leafcount(u) ? v : u
    _has_sin_cos(w) ? _trig_ratios(w) : w
end
_has_sin_cos(u) = u isa Sym && ((u.kind == SymJ.FN && (u.name === :sin || u.name === :cos)) ||
    any(_has_sin_cos, u.args) || any(_has_sin_cos, u.exps))

# Mathematica's automatic form of a product of powers of sin and cos of one argument:
# sin^p cos^-q is tan^p sec^(q-p) for p <= q, tan^q sin^(p-q) for p > q (Sin[x]/Cos[x] is
# Tan[x]); cos^p sin^-q likewise with cot and csc. RUBI's SimplifyIntegrand gives its
# rules that form (log(a cos x) by parts leaves -x sin(x)/cos(x), which is -x tan(x) to
# the tangent rules).
function _trig_ratios(u)
    u isa Sym || return u
    isempty(u.args) && return u
    u.kind == SymJ.MUL || return SymJ._rw_parts(_trig_ratios, u)
    fs = Pair{Sym,Sym}[b => e for (b, e) in zip(u.args, u.exps)]
    changed = false
    for i in eachindex(fs), j in eachindex(fs)
        bi, ei = fs[i]; bj, ej = fs[j]
        (bi.kind == SymJ.FN && bj.kind == SymJ.FN && length(bi.args) == 1 && length(bj.args) == 1) || continue
        isequal(bi.args[1], bj.args[1]) || continue
        (_isinteger(ei) && _isinteger(ej) && _rat(ei) > 0 && _rat(ej) < 0) || continue
        pair = (bi.name, bj.name)
        pair in ((:sin, :cos), (:cos, :sin)) || continue
        t, r, l = pair == (:sin, :cos) ? (:tan, :sec, :sin) : (:cot, :csc, :cos)
        p, q = _rat(ei), -_rat(ej)
        v = bi.args[1]
        k = min(p, q)
        fs[i] = apply_function(t, Sym[v]) => Sym(k)
        fs[j] = (p <= q ? apply_function(r, Sym[v]) : apply_function(l, Sym[v])) => Sym(abs(q - p))
        changed = true
    end
    changed || return SymJ._rw_parts(_trig_ratios, u)
    Sym(u.num) * prod((_trig_ratios(b)^e for (b, e) in fs); init = SymJ.ONE)
end

# P(x) (c + d x)^n, P a polynomial and n not a nonnegative integer, as a sum of powers
# of c + d x: P(x) = Σ p_k (c + d x)^k, so the terms are p_k (c + d x)^(n + k). RUBI's
# ExpandLinearProduct, the case its rules expect from Int[ExpandIntegrand[(a + b x)^m
# (c + d x)^n, x], x] with m a positive integer (1.1.1.2 #12): expand + apart leaves
# x^3 sqrt(a + b x) as it is. Nothing when u is not of this form.
function _expand_linear_product(u::Sym)
    u.kind == SymJ.MUL || return nothing
    fs = _factors(u)
    i = findfirst(f -> f.kind == SymJ.POW && FUNCS["LinearQ"](f.args[1], X) && _free(f.args[2], X) &&
                       !(_isinteger(f.args[2]) && _rat(f.args[2]) >= 0), fs)
    i === nothing && return nothing
    w, n = fs[i].args
    P = prod(fs[j] for j in eachindex(fs) if j != i; init = SymJ.ONE)
    (_free(P, X) || !FUNCS["PolyQ"](P, X)) && return nothing
    c, d = FUNCS["Coefficient"](w, X, Sym(0)), FUNCS["Coefficient"](w, X, Sym(1))
    iszero(c) && return nothing          # (d x)^n P(x): plain expansion does it
    y = Sym(:𝓎)
    ps = _coeffs(subs(expand(P), X => (y - c) / d), y)
    (ps === nothing || any(p -> has(p, y) || has(p, X), ps)) && return nothing
    sum((ps[k+1] * w^(n + k) for k in 0:length(ps)-1 if !iszero(ps[k+1])); init = SymJ.ZERO)
end

# ExpandIntegrand[u, x], ExpandIntegrand[u, v, x]: a sum of simpler terms. RUBI's has
# many special cases; this expands, and splits a rational function of x into partial
# fractions (approximate: other forms of the terms than RUBI's).
FUNCS["ExpandIntegrand"] = function (as...)
    u = length(as) == 3 ? _s(as[1]) * _s(as[2]) : _s(as[1])
    v = _expand_linear_product(u)
    v === nothing || return v
    e = expand(u)
    _is_rational_in_x(e) || return e
    try
        apart(e, X)
    catch
        e
    end
end
FUNCS["ExpandToSum"] = (as...) -> expand(length(as) == 3 ? _s(as[1]) * _s(as[2]) : _s(as[1]))
FUNCS["ExpandTrig"] = (as...) -> expand(length(as) == 3 ? _s(as[1]) * _s(as[2]) : _s(as[1]))
FUNCS["ExpandTrigReduce"] = FUNCS["ExpandTrig"]

function _is_rational_in_x(e::Sym)
    k = e.kind
    k in (SymJ.NUMBER, SymJ.SYMBOL, SymJ.CONSTANT, SymJ.PARAMETER) && return true
    k == SymJ.ADD && return all(_is_rational_in_x, e.args)
    k == SymJ.MUL && return all(_is_rational_in_x, e.args) &&
        all(i -> !has(e.args[i], X) || _isinteger(e.exps[i]), eachindex(e.args))
    k == SymJ.POW && return _is_rational_in_x(e.args[1]) && (!has(e.args[1], X) ? !has(e.args[2], X) : _isinteger(e.args[2]))
    !has(e, X)
end

# RemoveContent[u, x]: u without its factors free of x (in RUBI, for the argument of a
# log, where a constant factor only changes the constant of integration)
FUNCS["RemoveContent"] = function (u, x)
    u = _s(u)
    u.kind == SymJ.MUL || return u
    prod((a^e for (a, e) in zip(u.args, u.exps) if has(a, X) || has(e, X)); init = SymJ.ONE)
end

# roots and the parts of numbers
FUNCS["Rt"] = (u, n) -> _s(u)^(1 / _s(n))
# IntPart and FracPart: of a rational, its integer and fractional parts (toward zero, as
# Mathematica's IntegerPart); of a sum, term by term; of anything else, 0 and itself.
# IntPart[u] + FracPart[u] == u always, which is all the rules need for correctness.
function _intpart(u)
    u = _s(u)
    _isrational(u) && return Sym(trunc(Int, _rat(u)))
    u.kind == SymJ.ADD && return sum(_intpart(Sym(c) * a) for (a, c) in zip(u.args, u.coefs); init = _intpart(Sym(u.num)))
    SymJ.ZERO
end
@osrfunc IntPart(u) = _intpart(u)
@osrfunc FracPart(u) = _s(u) - _intpart(u)
@osrfunc IntegerPart(u) = _intpart(u)
@osrfunc FractionalPart(u) = _s(u) - _intpart(u)
@osrfunc Floor(u) = _isrational(u) ? Sym(floor(Int, _rat(u))) : throw(OSRError("Floor"))
@osrfunc Ceiling(u) = _isrational(u) ? Sym(ceil(Int, _rat(u))) : throw(OSRError("Ceiling"))
@osrfunc Mod(a, b) = (_isrational(a) && _isrational(b)) ? Sym(mod(_rat(a), _rat(b))) : throw(OSRError("Mod"))
@osrfunc Re(u) = real(_s(u))
@osrfunc Im(u) = imag(_s(u))
FUNCS["Max"] = (us...) -> (vs = map(_realval, us); any(isnothing, vs) ? throw(OSRError("Max")) : us[argmax(vs)])
FUNCS["Min"] = (us...) -> (vs = map(_realval, us); any(isnothing, vs) ? throw(OSRError("Min")) : us[argmin(vs)])
@osrfunc D(u, x) = diff(_s(u), _s(x))

# ---- lists, replacement and small utilities used by RUBI's With and Module rules

# ReplaceAll[u, x -> v] and ReplaceAll[u, {a -> b, …}]: substitution
FUNCS["ReplaceAll"] = (u, r) -> subs(_s(u), (r isa Pair ? (r,) : Tuple(r))...)
# Part[list, i] (lists from With's values; 1-based)
FUNCS["Part"] = function (l, i)
    (l isa AbstractVector && _isinteger(i)) || throw(OSRError("Part: not a list and an integer"))
    l[Int(_rat(i))]
end
# MemberQ[list, u]: u is in the list; a function name and a head slot's function are
# compared by name (MemberQ[{sin, cos, …}, trig])
FUNCS["MemberQ"] = function (l, u)
    l isa AbstractVector || return false
    n = _fname(u)
    any(a -> isequal(a, u) || (n !== nothing && _fname(a) === n), l)
end
FUNCS["NonsumQ"] = u -> !FUNCS["SumQ"](u)
# GCD of exact rationals
FUNCS["GCD"] = function (us...)
    all(_isrational, us) || throw(OSRError("GCD of numbers that are not rational"))
    Sym(reduce(gcd, map(_rat, us)))
end
# Numer, Denom: RUBI's numerator and denominator (its versions also split numbers)
FUNCS["Numer"] = FUNCS["Numerator"]
FUNCS["Denom"] = FUNCS["Denominator"]

# EasyDQ[u, x]: u is easy to differentiate (RUBI's test before DerivativeDivides tries
# u as the y of u' y^m; without it the 9.3 rules differentiate and simplify every way of
# splitting a product). Its RationalFunctionExponents case is left out.
function _easyd(u, x)
    u isa Sym || return true
    (u.kind in (SymJ.SYMBOL, SymJ.NUMBER) || _free(u, x)) && return true
    FUNCS["BinomialQ"](u, x) && return true
    if u.kind == SymJ.MUL
        nf = filter(f -> !_free(f, x), _factors(u))
        length(nf) == 1 && return _easyd(only(nf), x)
        # a product of powers of linears
        return all(f -> (f.kind == SymJ.POW ? FUNCS["LinearQ"](f.args[1], x) && _free(f.args[2], x) : FUNCS["LinearQ"](f, x)), nf)
    elseif u.kind == SymJ.ADD
        return all(t -> _easyd(t, x), _terms(u))
    elseif u.kind == SymJ.POW
        b, e = u.args
        _free(b, x) && return _easyd(e, x)
        _free(e, x) && return _easyd(b, x)
        return false
    elseif u.kind == SymJ.FN
        length(u.args) == 1 && return _easyd(u.args[1], x)
        length(u.args) == 2 || return false
        _free(u.args[1], x) && return _easyd(u.args[2], x)
        _free(u.args[2], x) && return _easyd(u.args[1], x)
    end
    false
end
FUNCS["EasyDQ"] = (u, x) -> _easyd(_s(u), _s(x))

# q is (numerically) not free of x: its values at two points differ. A quick test before
# cancel, which is slow on trig and algebraic expressions; inconclusive (false) when a
# value can't be computed
function _numerically_nonfree(q::Sym, x::Sym)
    v1, v2 = _value_at(q, x, 0.43 + 0.29im), _value_at(q, x, 0.71 - 0.13im)
    (v1 === nothing || v2 === nothing) && return false
    abs(v1 - v2) > 1e-6 * (1 + abs(v1))
end

# DerivativeDivides[y, u, x]: u/D[y, x] when it is free of x, else False; False when y
# is a multiple of x, is not easy to differentiate (EasyDQ), or is a polynomial and u is
# not one of degree one less
FUNCS["DerivativeDivides"] = function (y, u, x)
    y, u, x = _s(y), _s(u), _s(x)
    _free(cancel(y / x), x) && return false
    if FUNCS["PolynomialQ"](y, x)
        (FUNCS["PolynomialQ"](u, x) && isequal(FUNCS["Expon"](u, x), FUNCS["Expon"](y, x) - 1)) || return false
    else
        _easyd(y, x) || return false
    end
    v = diff(y, x)
    iszero(v) && return false
    q = u / v
    _numerically_nonfree(q, x) && return false
    q = cancel(q)
    _free(q, x) ? q : false
end

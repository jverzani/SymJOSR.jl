# FunctionOfQ[v, u, x] and SubstFor[v, u, x] for v a trig function: RUBI's FunctionOfSinQ,
# FunctionOfCosQ, FunctionOfTanQ, their Pure… versions and SubstForTrig
# (IntegrationUtilityFunctions.m, RUBI 4.16.1). The rules of 4.7.5 that substitute
# t = sin v, cos v or tan v for a function of trig functions use them. (Hyperbolic v,
# RUBI's SubstForHyperbolic, is not done: FunctionOfQ is false and SubstFor rejects.)

_trigq(u::Sym) = u.kind == SymJ.FN && u.name in _TRIG && length(u.args) == 1
_intpow(u::Sym) = u.kind == SymJ.POW && _isinteger(u.args[2])

# u/v as an integer, or nothing (IntegerQuotientQ; OddQuotientQ, EvenQuotientQ)
function _int_quotient(u, v)
    q = cancel(_s(u) / _s(v))
    _isinteger(q) ? Int(_rat(q)) : nothing
end
_odd_quotient(u, v) = (q = _int_quotient(u, v); q !== nothing && isodd(q))
_even_quotient(u, v) = (q = _int_quotient(u, v); q !== nothing && iseven(q))

# u's factors as base and degree (LeadBase, LeadDegree)
_base_degree(f::Sym) = f.kind == SymJ.POW ? (f.args[1], f.args[2]) : (f, SymJ.ONE)

# FindTrigFactor[f1, f2, u, v, flag]: a factor f1[m v]^n or f2[m v]^n of the product u, n
# odd, m an integer (m v ≠ v unless flag): (m v, the other factors), or nothing
function _find_trig_factor(names, u::Sym, v, flag)
    fs = _factors(u)
    for (i, f) in enumerate(fs)
        b, e = _base_degree(f)
        if _trigq(b) && b.name in names && _isinteger(e) && isodd(Int(_rat(e))) &&
           _int_quotient(b.args[1], v) !== nothing && (flag || !_eq(b.args[1], v))
            return (b.args[1], prod(fs[j] for j in eachindex(fs) if j != i; init = SymJ.ONE))
        end
    end
    nothing
end

# the product u has the factors cos(v/2) and sin(v/2): the other factors, else nothing
function _half_angle_rest(u::Sym, v)
    fs = _factors(u)
    i = findfirst(f -> _trigq(f) && f.name === :cos && _eq(f.args[1], v / 2), fs)
    j = findfirst(f -> _trigq(f) && f.name === :sin && _eq(f.args[1], v / 2), fs)
    (i === nothing || j === nothing) && return nothing
    prod(fs[k] for k in eachindex(fs) if k != i && k != j; init = SymJ.ONE)
end

# FunctionOfSinQ[u, v, x]: u is a function of sin v
function _function_of_sin(u::Sym, v, x::Sym)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    if _trigq(u) && _int_quotient(u.args[1], v) !== nothing
        return _odd_quotient(u.args[1], v) ? u.name in (:sin, :csc) : u.name in (:cos, :sec)
    end
    if _intpow(u) && _trigq(u.args[1]) && _int_quotient(u.args[1].args[1], v) !== nothing
        return iseven(Int(_rat(u.args[2]))) || _function_of_sin(u.args[1], v, x)
    end
    if u.kind == SymJ.MUL
        r = _half_angle_rest(u, v)
        r === nothing || return _function_of_sin(r, v, x)
        l = _find_trig_factor((:sin, :csc), u, v, false)
        l !== nothing && _even_quotient(l[1], v) && return _function_of_sin(cos(v) * l[2], v, x)
        l = _find_trig_factor((:cos, :sec), u, v, false)
        l !== nothing && _odd_quotient(l[1], v) && return _function_of_sin(cos(v) * l[2], v, x)
        l = _find_trig_factor((:tan, :cot), u, v, true)
        l !== nothing && return _function_of_sin(cos(v) * l[2], v, x)
    end
    all(p -> _function_of_sin(p, v, x), _parts(u))
end

# FunctionOfCosQ[u, v, x]: u is a function of cos v
function _function_of_cos(u::Sym, v, x::Sym)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    _trigq(u) && _int_quotient(u.args[1], v) !== nothing && return u.name in (:cos, :sec)
    if _intpow(u) && _trigq(u.args[1]) && _int_quotient(u.args[1].args[1], v) !== nothing
        return iseven(Int(_rat(u.args[2]))) || _function_of_cos(u.args[1], v, x)
    end
    if u.kind == SymJ.MUL
        l = _find_trig_factor((:sin, :csc), u, v, false)
        l !== nothing && return _function_of_cos(sin(v) * l[2], v, x)
        l = _find_trig_factor((:tan, :cot), u, v, true)
        l !== nothing && return _function_of_cos(sin(v) * l[2], v, x)
    end
    all(p -> _function_of_cos(p, v, x), _parts(u))
end

# FunctionOfTanQ[u, v, x]: u is a function of tan v (and cot v)
function _function_of_tan(u::Sym, v, x::Sym)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    if _trigq(u) && _int_quotient(u.args[1], v) !== nothing
        return u.name in (:tan, :cot) || _even_quotient(u.args[1], v)
    end
    if _intpow(u) && iseven(Int(_rat(u.args[2])))
        b = u.args[1]
        _trigq(b) && _int_quotient(b.args[1], v) !== nothing && return true
        b.kind == SymJ.ADD && return _function_of_tan(expand(b^2), v, x)
    end
    if u.kind == SymJ.MUL
        l = filter(f -> !_function_of_tan(f, v, x), _factors(u))
        isempty(l) && return true
        return length(l) == 2 && _odd_trig_power(l[1], v, x) && _odd_trig_power(l[2], v, x)
    end
    all(p -> _function_of_tan(p, v, x), _parts(u))
end
# OddTrigPowerQ[u, v, x]
function _odd_trig_power(u::Sym, v, x::Sym)
    _trigq(u) && u.name in (:sin, :cos, :sec, :csc) && return _odd_quotient(u.args[1], v)
    u.kind == SymJ.POW && return _isinteger(u.args[2]) && isodd(Int(_rat(u.args[2]))) && _odd_trig_power(u.args[1], v, x)
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, x)
        isone(c) || return _odd_trig_power(FUNCS["NonfreeFactors"](u, x), v, x)
        l = filter(f -> !_function_of_tan(f, v, x), _factors(u))
        isempty(l) && return true
        return length(l) == 1 && _odd_trig_power(l[1], v, x)
    end
    u.kind == SymJ.ADD && return all(t -> _odd_trig_power(t, v, x), _terms(u))
    false
end

# PureFunctionOfSinQ etc.: u is a function of the trig functions in names of v itself
function _pure_function_of(u::Sym, names, v, x::Sym)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    _trigq(u) && _eq(u.args[1], v) && return u.name in names
    all(p -> _pure_function_of(p, names, v, x), _parts(u))
end

# FunctionOfQ[v, u, x, pure] for v = trig(w)
function _function_of_trigq(v::Sym, u::Sym, x::Sym, pure::Bool)
    w = v.args[1]
    if pure
        names = v.name in (:sin, :csc) ? (:sin, :csc) : v.name in (:cos, :sec) ? (:cos, :sec) :
                v.name === :tan ? (:tan, :cot) : (:cot,)
        return _pure_function_of(u, names, w, x)
    end
    v.name in (:sin, :csc) ? _function_of_sin(u, w, x) :
        v.name in (:cos, :sec) ? _function_of_cos(u, w, x) : _function_of_tan(u, w, x)
end

# sin(m v) and cos(m v) as polynomials in s = sin v and c = cos v (m an integer)
function _multiple_angle(m::Int, s, c)
    m < 0 && ((S, C) = _multiple_angle(-m, s, c); return (-S, C))
    S, C = SymJ.ZERO, SymJ.ZERO
    for k in 0:m
        t = binomial(m, k) * c^(m - k) * s^k
        iseven(k) ? (C += (-1)^(k ÷ 2) * t) : (S += (-1)^((k - 1) ÷ 2) * t)
    end
    S, C
end

# SubstForTrig[u, sin, cos, v, x]: u, a function of the trig functions of integer
# multiples of v, with sin v and cos v replaced by s and c
function _subst_for_trig(u::Sym, s, c, v, x::Sym)
    _atomq(u) && return u
    if _trigq(u) && (m = _int_quotient(u.args[1], v)) !== nothing
        S, C = m == 1 ? (s, c) : _multiple_angle(m, s, c)
        n = u.name
        return n === :sin ? S : n === :cos ? C : n === :tan ? S / C : n === :cot ? C / S : n === :sec ? 1 / C : 1 / S
    end
    if u.kind == SymJ.MUL
        r = _half_angle_rest(u, v)
        r === nothing || return s / 2 * _subst_for_trig(r, s, c, v, x)
    end
    _map_parts(p -> _subst_for_trig(p, s, c, v, x), u)
end

# SubstFor[v, u, x] for v = trig(w): u in terms of t = v (as _T), or nothing when x is left
function _subst_for_trigv(v::Sym, u::Sym, x::Sym)
    t = _T
    s, c = v.name === :sin ? (t, sqrt(1 - t^2)) : v.name === :cos ? (sqrt(1 - t^2), t) :
           v.name === :tan ? (t / sqrt(1 + t^2), 1 / sqrt(1 + t^2)) :
           v.name === :cot ? (1 / sqrt(1 + t^2), t / sqrt(1 + t^2)) :
           v.name === :sec ? (1 / sqrt(1 - t^2), 1 / t) : (1 / t, 1 / sqrt(1 - t^2))
    w = _subst_for_trig(u, s, c, v.args[1], x)
    has(w, x) ? nothing : w
end

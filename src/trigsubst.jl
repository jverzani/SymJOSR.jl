# FunctionOfQ[v, u, x] and SubstFor[v, u, x] for v a trig or hyperbolic function: RUBI's
# FunctionOfSinQ, FunctionOfCosQ, FunctionOfTanQ, their Pure… versions and SubstForTrig,
# and the hyperbolic twins FunctionOfSinhQ, … and SubstForHyperbolic
# (IntegrationUtilityFunctions.m, RUBI 4.16.1). The rules that substitute t = sin v,
# cos v, tan v (4.7.5) or t = sinh v, cosh v, tanh v (6.7) use them.
#
# The two families are written once: RUBI's hyperbolic definitions are its trig ones with
# the hyperbolic names, except for the multiple-angle formulas (_multiple_angle).

const _TRIGF = (sin = :sin, cos = :cos, tan = :tan, cot = :cot, sec = :sec, csc = :csc, hyp = false)
const _HYPF = (sin = :sinh, cos = :cosh, tan = :tanh, cot = :coth, sec = :sech, csc = :csch, hyp = true)
_family(name::Symbol) = name in _TRIG ? _TRIGF : name in _HYPERBOLIC ? _HYPF : nothing
_names(F) = (F.sin, F.cos, F.tan, F.cot, F.sec, F.csc)
_fn(name, v) = apply_function(name, Sym[v])

# TrigQ[u] (HyperbolicQ[u]): a function of F of one argument
_trigq(u::Sym, F) = u.kind == SymJ.FN && u.name in _names(F) && length(u.args) == 1
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
        if b.kind == SymJ.FN && b.name in names && length(b.args) == 1 && _isinteger(e) && isodd(Int(_rat(e))) &&
           _int_quotient(b.args[1], v) !== nothing && (flag || !_eq(b.args[1], v))
            return (b.args[1], prod(fs[j] for j in eachindex(fs) if j != i; init = SymJ.ONE))
        end
    end
    nothing
end

# the product u has the factors cos(v/2) and sin(v/2) (cosh, sinh): the other factors,
# else nothing
function _half_angle_rest(u::Sym, v, F)
    fs = _factors(u)
    i = findfirst(f -> _trigq(f, F) && f.name === F.cos && _eq(f.args[1], v / 2), fs)
    j = findfirst(f -> _trigq(f, F) && f.name === F.sin && _eq(f.args[1], v / 2), fs)
    (i === nothing || j === nothing) && return nothing
    prod(fs[k] for k in eachindex(fs) if k != i && k != j; init = SymJ.ONE)
end

# FunctionOfSinQ[u, v, x] (FunctionOfSinhQ): u is a function of sin v (sinh v)
function _function_of_sin(u::Sym, v, x::Sym, F = _TRIGF)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    if _trigq(u, F) && _int_quotient(u.args[1], v) !== nothing
        return _odd_quotient(u.args[1], v) ? u.name in (F.sin, F.csc) : u.name in (F.cos, F.sec)
    end
    if _intpow(u) && _trigq(u.args[1], F) && _int_quotient(u.args[1].args[1], v) !== nothing
        return iseven(Int(_rat(u.args[2]))) || _function_of_sin(u.args[1], v, x, F)
    end
    if u.kind == SymJ.MUL
        r = _half_angle_rest(u, v, F)
        r === nothing || return _function_of_sin(r, v, x, F)
        c = _fn(F.cos, v)
        l = _find_trig_factor((F.sin, F.csc), u, v, false)
        l !== nothing && _even_quotient(l[1], v) && return _function_of_sin(c * l[2], v, x, F)
        l = _find_trig_factor((F.cos, F.sec), u, v, false)
        l !== nothing && _odd_quotient(l[1], v) && return _function_of_sin(c * l[2], v, x, F)
        l = _find_trig_factor((F.tan, F.cot), u, v, true)
        l !== nothing && return _function_of_sin(c * l[2], v, x, F)
    end
    all(p -> _function_of_sin(p, v, x, F), _parts(u))
end

# FunctionOfCosQ[u, v, x] (FunctionOfCoshQ): u is a function of cos v (cosh v)
function _function_of_cos(u::Sym, v, x::Sym, F = _TRIGF)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    _trigq(u, F) && _int_quotient(u.args[1], v) !== nothing && return u.name in (F.cos, F.sec)
    if _intpow(u) && _trigq(u.args[1], F) && _int_quotient(u.args[1].args[1], v) !== nothing
        return iseven(Int(_rat(u.args[2]))) || _function_of_cos(u.args[1], v, x, F)
    end
    if u.kind == SymJ.MUL
        s = _fn(F.sin, v)
        l = _find_trig_factor((F.sin, F.csc), u, v, false)
        l !== nothing && return _function_of_cos(s * l[2], v, x, F)
        l = _find_trig_factor((F.tan, F.cot), u, v, true)
        l !== nothing && return _function_of_cos(s * l[2], v, x, F)
    end
    all(p -> _function_of_cos(p, v, x, F), _parts(u))
end

# FunctionOfTanQ[u, v, x] (FunctionOfTanhQ): u is a function of tan v and cot v (tanh, coth)
function _function_of_tan(u::Sym, v, x::Sym, F = _TRIGF)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    if _trigq(u, F) && _int_quotient(u.args[1], v) !== nothing
        return u.name in (F.tan, F.cot) || _even_quotient(u.args[1], v)
    end
    if _intpow(u) && iseven(Int(_rat(u.args[2])))
        b = u.args[1]
        _trigq(b, F) && _int_quotient(b.args[1], v) !== nothing && return true
        b.kind == SymJ.ADD && return _function_of_tan(expand(b^2), v, x, F)
    end
    if u.kind == SymJ.MUL
        l = filter(f -> !_function_of_tan(f, v, x, F), _factors(u))
        isempty(l) && return true
        return length(l) == 2 && _odd_trig_power(l[1], v, x, F) && _odd_trig_power(l[2], v, x, F)
    end
    all(p -> _function_of_tan(p, v, x, F), _parts(u))
end
# OddTrigPowerQ[u, v, x] (OddHyperbolicPowerQ)
function _odd_trig_power(u::Sym, v, x::Sym, F = _TRIGF)
    _trigq(u, F) && u.name in (F.sin, F.cos, F.sec, F.csc) && return _odd_quotient(u.args[1], v)
    u.kind == SymJ.POW && return _isinteger(u.args[2]) && isodd(Int(_rat(u.args[2]))) && _odd_trig_power(u.args[1], v, x, F)
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, x)
        isone(c) || return _odd_trig_power(FUNCS["NonfreeFactors"](u, x), v, x, F)
        l = filter(f -> !_function_of_tan(f, v, x, F), _factors(u))
        isempty(l) && return true
        return length(l) == 1 && _odd_trig_power(l[1], v, x, F)
    end
    u.kind == SymJ.ADD && return all(t -> _odd_trig_power(t, v, x, F), _terms(u))
    false
end

# PureFunctionOfSinQ etc.: u is a function of the functions in names, of v itself
function _pure_function_of(u::Sym, names, v, x::Sym, F)
    _atomq(u) && return !isequal(u, x)
    _calculusq(u) && return false
    _trigq(u, F) && _eq(u.args[1], v) && return u.name in names
    all(p -> _pure_function_of(p, names, v, x, F), _parts(u))
end

# FunctionOfQ[v, u, x, pure] for v = f(w), f a trig or hyperbolic function
function _function_of_trigq(v::Sym, u::Sym, x::Sym, pure::Bool)
    F = _family(v.name)
    w, n = v.args[1], v.name
    if pure
        names = n in (F.sin, F.csc) ? (F.sin, F.csc) : n in (F.cos, F.sec) ? (F.cos, F.sec) :
                n === F.tan ? (F.tan, F.cot) : (F.cot,)
        return _pure_function_of(u, names, w, x, F)
    end
    n in (F.sin, F.csc) ? _function_of_sin(u, w, x, F) :
        n in (F.cos, F.sec) ? _function_of_cos(u, w, x, F) : _function_of_tan(u, w, x, F)
end

# sin(m v) and cos(m v) as polynomials in s = sin v and c = cos v (m an integer), from
# (c + i s)^m; for the hyperbolic functions sinh(m v) and cosh(m v) from (c + s)^m
function _multiple_angle(m::Int, s, c, hyp::Bool = false)
    m < 0 && ((S, C) = _multiple_angle(-m, s, c, hyp); return (-S, C))
    S, C = SymJ.ZERO, SymJ.ZERO
    for k in 0:m
        t = binomial(m, k) * c^(m - k) * s^k
        if iseven(k)
            C += (hyp ? 1 : (-1)^(k ÷ 2)) * t
        else
            S += (hyp ? 1 : (-1)^((k - 1) ÷ 2)) * t
        end
    end
    S, C
end

# SubstForTrig[u, sin, cos, v, x] (SubstForHyperbolic): u, a function of the functions F
# of integer multiples of v, with sin v and cos v (sinh v, cosh v) replaced by s and c
function _subst_for_trig(u::Sym, s, c, v, x::Sym, F = _TRIGF)
    _atomq(u) && return u
    if _trigq(u, F) && (m = _int_quotient(u.args[1], v)) !== nothing
        S, C = m == 1 ? (s, c) : _multiple_angle(m, s, c, F.hyp)
        n = u.name
        return n === F.sin ? S : n === F.cos ? C : n === F.tan ? S / C : n === F.cot ? C / S :
               n === F.sec ? 1 / C : 1 / S
    end
    if u.kind == SymJ.MUL
        r = _half_angle_rest(u, v, F)
        r === nothing || return s / 2 * _subst_for_trig(r, s, c, v, x, F)
    end
    _map_parts(p -> _subst_for_trig(p, s, c, v, x, F), u)
end

# SubstFor[v, u, x] for v = f(w), f a trig or hyperbolic function: u in terms of t = v
# (as _T), or nothing when x is left
function _subst_for_trigv(v::Sym, u::Sym, x::Sym)
    t, n = _T, v.name
    s, c = n === :sin ? (t, sqrt(1 - t^2)) : n === :cos ? (sqrt(1 - t^2), t) :
           n === :tan ? (t / sqrt(1 + t^2), 1 / sqrt(1 + t^2)) :
           n === :cot ? (1 / sqrt(1 + t^2), t / sqrt(1 + t^2)) :
           n === :sec ? (1 / sqrt(1 - t^2), 1 / t) : n === :csc ? (1 / t, 1 / sqrt(1 - t^2)) :
           n === :sinh ? (t, sqrt(1 + t^2)) : n === :cosh ? (sqrt(-1 + t^2), t) :
           n === :tanh ? (t / sqrt(1 - t^2), 1 / sqrt(1 - t^2)) :
           n === :coth ? (1 / sqrt(-1 + t^2), t / sqrt(-1 + t^2)) :
           n === :sech ? (1 / sqrt(-1 + t^2), 1 / t) : (1 / t, 1 / sqrt(1 + t^2))
    w = _subst_for_trig(u, s, c, v.args[1], x, _family(n))
    has(w, x) ? nothing : w
end

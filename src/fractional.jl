# RUBI's general substitutions for fractional powers of a linear function, and the guard
# of its substitution t = tan v (IntegrationUtilityFunctions.m, RUBI 4.16.1): what 9.3's
# rules Int[u, x] := With[{lst = SubstForFractionalPowerOfLinear[u, x]}, …] and 4.7.5's
# Int[u, x] := With[{v = FunctionOfTrig[u, x]}, …] /; … && TryPureTanSubst[…] need.

# Mathematica's parts of u, as Scan and Map see them: the terms of a sum, the factors of a
# product (each with its power), the base and exponent of a power, a function's arguments
_parts(u::Sym) = u.kind == SymJ.ADD ? _terms(u) : u.kind == SymJ.MUL ? _factors(u) : u.args
# u with f applied to each of its parts
_map_parts(f, u::Sym) = u.kind == SymJ.ADD ? sum(f, _terms(u); init = SymJ.ZERO) :
    u.kind == SymJ.MUL ? prod(f, _factors(u); init = SymJ.ONE) : SymJ._rw_parts(f, u)

_atomq(u::Sym) = isempty(u.args)
# FractionalPowerQ[u]: a power with a rational, non-integer exponent
_fractional_power(u::Sym) = u.kind == SymJ.POW && _isrational(u.args[2]) && !_isinteger(u.args[2])
# CalculusQ[u]: an unevaluated integral, derivative, substitution
_calculusq(u::Sym) = u.kind == SymJ.FN && u.name in (:Int, :Derivative, :Subst, :Unintegrable, :CannotIntegrate)

# FractionalPowerOfLinear[u, n, v, x]: (n, v) with n the least common multiple of n and
# the denominators of u's fractional powers of the linear v (false: not yet found), or
# false when u has a fractional power of another linear function, or calculus
function _fractional_power_of_linear(u::Sym, n, v, x::Sym)
    (_atomq(u) || !has(u, x)) && return (n, v)
    _calculusq(u) && return false
    if _fractional_power(u) && _linear_in(u.args[1], x) && (v === false || _eq(u.args[1], v))
        return (lcm(denominator(_rat(u.args[2])), n), u.args[1])
    end
    lst = (n, v)
    for p in _parts(u)
        lst = _fractional_power_of_linear(p, lst..., x)
        lst === false && return false
    end
    lst
end

# SubstForFractionalPower[u, v, n, w, x]: u with v^(m/n) as x^m and x as w
function _subst_for_fractional_power(u::Sym, v, n, w, x::Sym)
    _atomq(u) && return isequal(u, x) ? w : u
    _fractional_power(u) && _eq(u.args[1], v) && return x^(n * u.args[2])
    _map_parts(p -> _subst_for_fractional_power(p, v, n, w, x), u)
end

# SubstForFractionalPowerOfLinear[u, x]: for u with fractional powers of a + b x, the
# least common denominator n of their exponents, the integrand in t = (a + b x)^(1/n)
# (written in x), a + b x and the constant factor: {v, n, a + b x, c}, with
# Int[u, x] = n c Subst[Int[v, x], x, (a + b x)^(1/n)]; else False
function _subst_for_fractional_power_of_linear(u::Sym, x::Sym)
    lst = _fractional_power_of_linear(u, 1, false, x)
    (lst === false || lst[2] === false) && return false
    n, l = lst
    a, b = FUNCS["Coefficient"](l, x, Sym(0)), FUNCS["Coefficient"](l, x, Sym(1))
    tmp = SymJ.simplify(x^(n - 1) * _subst_for_fractional_power(u, l, n, -a / b + x^n / b, x))
    Any[FUNCS["NonfreeFactors"](tmp, x), Sym(n), l, FUNCS["FreeFactors"](tmp, x) / b]
end
FUNCS["SubstForFractionalPowerOfLinear"] = (u, x) -> _subst_for_fractional_power_of_linear(_s(u), _s(x))

# SubstForFractionalPowerQ[u, v, x]: the substitution x = v^(1/n) leaves each fractional
# power of u a power of a function of v
function _subst_for_fractional_power_q(u::Sym, v, x::Sym)
    (_atomq(u) || !has(u, x)) && return true
    _fractional_power(u) && return _subst_for_fractional_power_auxq(u, v, x)
    all(p -> _subst_for_fractional_power_q(p, v, x), _parts(u))
end
function _subst_for_fractional_power_auxq(u::Sym, v, x::Sym)
    _atomq(u) && return false
    _fractional_power(u) && _eq(u.args[1], v) && return true
    any(p -> _subst_for_fractional_power_auxq(p, v, x), _parts(u))
end
FUNCS["SubstForFractionalPowerQ"] = (u, v, x) -> _subst_for_fractional_power_q(_s(u), _s(v), _s(x))

# TryPureTanSubst[u, x]: u is not F[c (a + b G[v])], F an inverse tangent or cotangent
# (circular or hyperbolic), G a tangent or cotangent, v linear: those, t = tan v makes no
# simpler
function _try_pure_tan_subst(u::Sym, x::Sym)
    (u.kind == SymJ.FN && u.name in (:atan, :acot, :atanh, :acoth) && length(u.args) == 1) || return true
    w = FUNCS["NonfreeFactors"](u.args[1], x)                  # a + b G[v]
    ts = filter(t -> has(t, x), _terms(w))
    length(ts) == 1 || return true
    g = FUNCS["NonfreeFactors"](ts[1], x)                     # G[v]
    !(g.kind == SymJ.FN && g.name in (:tan, :cot, :tanh, :coth) && length(g.args) == 1 && _linear_in(g.args[1], x))
end
FUNCS["TryPureTanSubst"] = (u, x) -> _try_pure_tan_subst(_s(u), _s(x))

# QuotientOfLinearsParts[u, x]: (a, b, c, d) with u = (a + b x)/(c + d x), or nothing
# (QuotientOfLinearsP false)
function _qol_parts(u::Sym, x::Sym)
    has(u, x) || return (u, SymJ.ZERO, SymJ.ONE, SymJ.ZERO)
    C(v, k) = FUNCS["Coefficient"](v, x, Sym(k))
    _linear_in(u, x) && return (C(u, 0), C(u, 1), SymJ.ONE, SymJ.ZERO)
    if u.kind == SymJ.MUL
        a = FUNCS["FreeFactors"](u, x)
        if !isone(a)
            p = _qol_parts(FUNCS["NonfreeFactors"](u, x), x)
            return p === nothing ? nothing : (a * p[1], a * p[2], p[3], p[4])
        end
        fs = _factors(u)
        if length(fs) == 2
            for (n, d) in ((fs[1], fs[2]), (fs[2], fs[1]))
                if d.kind == SymJ.POW && _eq(d.args[2], -1) && _linear_in(n, x) && _linear_in(d.args[1], x)
                    return (C(n, 0), C(n, 1), C(d.args[1], 0), C(d.args[1], 1))
                end
            end
        end
        return nothing
    end
    if u.kind == SymJ.ADD
        ts = _terms(u)
        a = sum(filter(t -> !has(t, x), ts); init = SymJ.ZERO)
        iszero(a) && return nothing
        p = _qol_parts(u - a, x)
        return p === nothing ? nothing : (p[1] + a * p[3], p[2] + a * p[4], p[3], p[4])
    end
    if u.kind == SymJ.POW && _eq(u.args[2], -1)
        p = _qol_parts(u.args[1], x)
        return p === nothing ? nothing : (p[3], p[4], p[1], p[2])
    end
    nothing
end
# QuotientOfLinearsQ[u, x]: u is (a + b x)/(c + d x) with b, d nonzero
function _qolq(u::Sym, x::Sym)
    p = _qol_parts(u, x)
    p !== nothing && !_eq(p[2], 0) && !_eq(p[4], 0)
end

# FractionalPowerOfQuotientOfLinears[u, n, v, x], as FractionalPowerOfLinear for powers of
# a quotient of linear functions that is not linear
function _fractional_power_of_qol(u::Sym, n, v, x::Sym)
    (_atomq(u) || !has(u, x)) && return (n, v)
    _calculusq(u) && return false
    if _fractional_power(u) && _qolq(u.args[1], x) && !_linear_in(u.args[1], x) && (v === false || _eq(u.args[1], v))
        return (lcm(denominator(_rat(u.args[2])), n), u.args[1])
    end
    lst = (n, v)
    for p in _parts(u)
        lst = _fractional_power_of_qol(p, lst..., x)
        lst === false && return false
    end
    lst
end

# SubstForFractionalPowerOfQuotientOfLinears[u, x]: {v, n, q, b c - a d} for u with
# fractional powers of q = (a + b x)/(c + d x), with
# Int[u, x] = n (b c - a d) Subst[Int[v, x], x, q^(1/n)]; else False
function _subst_for_fractional_power_of_qol(u::Sym, x::Sym)
    lst = _fractional_power_of_qol(u, 1, false, x)
    (lst === false || lst[2] === false) && return false
    n, q = lst
    a, b, c, d = _qol_parts(q, x)
    _eq(d, 0) && return false
    tmp = SymJ.simplify(x^(n - 1) * _subst_for_fractional_power(u, q, n, (-a + c * x^n) / (b - d * x^n), x) /
                        (b - d * x^n)^2)
    Any[FUNCS["NonfreeFactors"](tmp, x), Sym(n), q, FUNCS["FreeFactors"](tmp, x) * (b * c - a * d)]
end
FUNCS["SubstForFractionalPowerOfQuotientOfLinears"] = (u, x) -> _subst_for_fractional_power_of_qol(_s(u), _s(x))
FUNCS["QuotientOfLinearsQ"] = (u, x) -> u isa AbstractVector ? all(v -> _qolq(_s(v), _s(x)), u) : _qolq(_s(u), _s(x))
FUNCS["QuotientOfLinearsParts"] = function (u, x)
    p = _qol_parts(_s(u), _s(x))
    p === nothing && throw(OSRError("QuotientOfLinearsParts: not a quotient of linears"))
    Any[p...]
end

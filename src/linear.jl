# PiecewiseLinearQ and FunctionOfLinear (IntegrationUtilityFunctions.m, RUBI 4.16.1).
# PiecewiseLinearQ guards rules whose integrand has a factor with a constant derivative
# (log(c F^v), atan(tan v), …); FunctionOfLinear gives 9.3's general substitution
# Int[f(a + b x)] = 1/b Subst[Int[f(x)], x, a + b x].

# PiecewiseLinearQ[u, x]: u's derivative is free of x (where it exists): u linear,
# log(c F^v) with v linear, or atanh(tanh v), atan(tan v) and the like
const _PWL_PAIRS = Set([(:atanh, :tanh), (:atanh, :coth), (:acoth, :coth), (:acoth, :tanh),
                        (:atan, :tan), (:atan, :cot), (:acot, :cot), (:acot, :tan)])
function _piecewise_linear(u::Sym, x::Sym)
    _linear_in(u, x) && return true
    u.kind == SymJ.FN && length(u.args) == 1 || return false
    w = u.args[1]
    if u.name === :log
        p = FUNCS["NonfreeFactors"](w, x)                     # c F^v
        p.kind == SymJ.FN && p.name === :exp && length(p.args) == 1 && return _linear_in(p.args[1], x)
        return p.kind == SymJ.POW && !has(p.args[1], x) && _linear_in(p.args[2], x)
    end
    w.kind == SymJ.FN && length(w.args) == 1 && (u.name, w.name) in _PWL_PAIRS && _linear_in(w.args[1], x)
end
FUNCS["PiecewiseLinearQ"] = (args...) -> begin
    x = _s(args[end])
    all(u -> _piecewise_linear(_s(u), x), args[1:end-1])
end

# MonomialFactor[u, x][[1]]: the degree k of the factor x^k of u (0 when there is none)
function _monomial_degree(u::Sym, x::Sym)
    _atomq(u) && return isequal(u, x) ? SymJ.ONE : SymJ.ZERO
    if u.kind == SymJ.POW
        b, e = u.args
        _isinteger(e) && return _monomial_degree(b, x) * e
        return isequal(b, x) && !has(e, x) ? e : SymJ.ZERO
    end
    u.kind == SymJ.MUL && return sum(f -> _monomial_degree(f, x), _factors(u); init = SymJ.ZERO)
    if u.kind == SymJ.ADD
        ds = [_monomial_degree(t, x) for t in _terms(u)]
        all(_isrational, ds) || return SymJ.ZERO
        d = minimum(_rat, ds)
        return d <= 0 ? SymJ.ZERO : Sym(d)
    end
    SymJ.ZERO
end

# CommonFactors[{b, c}][[1 : 2]], in part: the common factor g of b and c (the gcd of
# their rational coefficients times their common symbolic factors, each to its lower
# power) and b/g
function _common_factor(b::Sym, c::Sym)
    coef_factors(u) = u.kind == SymJ.MUL ? (Sym(u.num), Dict(a => e for (a, e) in zip(u.args, u.exps))) :
               _isnum(u) ? (u, Dict{Sym,Sym}()) : u.kind == SymJ.POW ? (SymJ.ONE, Dict(u.args[1] => u.args[2])) :
               (SymJ.ONE, Dict(u => SymJ.ONE))
    (kb, fb), (kc, fc) = coef_factors(b), coef_factors(c)
    g = (_isrational(kb) && _isrational(kc)) ? Sym(gcd(_rat(kb), _rat(kc))) : SymJ.ONE
    for (a, e) in fb
        haskey(fc, a) || continue
        f = fc[a]
        (_isrational(e) && _isrational(f)) || continue
        m = min(_rat(e), _rat(f))
        m > 0 && (g *= a^m)
    end
    g, b / g
end

# FunctionOfLinear[u, a, b, x, flag]: (a, b) for u a function of a + b x (a, b false
# while unknown), or false
function _function_of_linear(u::Sym, a, b, x::Sym, flag::Bool)
    has(u, x) || return (a, b)
    _calculusq(u) && return false
    C(v, k) = FUNCS["Coefficient"](v, x, Sym(k))
    if _linear_in(u, x)
        c0, c1 = C(u, 0), C(u, 1)
        a === false && return (c0, c1)
        g, bq = _common_factor(_s(b), c1)
        _eq(c0, 0) && !flag && return (SymJ.ZERO, g)
        _eq(b * c0 - a * c1, 0) && return (a / bq, g)
        return (SymJ.ZERO, SymJ.ONE)
    end
    u.kind == SymJ.POW && !has(u.args[1], x) && return _function_of_linear(log(u.args[1]) * u.args[2], a, b, x, false)
    u.kind == SymJ.FN && u.name === :exp && length(u.args) == 1 && return _function_of_linear(u.args[1], a, b, x, false)
    u.kind == SymJ.MUL && !iszero(_monomial_degree(u, x)) && return false
    lst = (a, b)
    for p in _parts(u)
        lst = _function_of_linear(p, lst..., x, u.kind == SymJ.ADD)
        lst === false && return false
    end
    lst
end

# FunctionOfLinearSubst[u, a, b, x]: u with a + b x as x
function _function_of_linear_subst(u::Sym, a, b, x::Sym)
    has(u, x) || return u
    if _linear_in(u, x)
        c1 = FUNCS["Coefficient"](u, x, Sym(1))
        t = isequal(c1, b) ? SymJ.ONE : c1 / b
        return FUNCS["Coefficient"](u, x, Sym(0)) - a * t + t * x
    end
    if u.kind == SymJ.POW && !has(u.args[1], x)
        return exp(SymJ.simplify(_function_of_linear_subst(log(u.args[1]) * u.args[2], a, b, x)))
    end
    u.kind == SymJ.FN && u.name === :exp && length(u.args) == 1 && return exp(_function_of_linear_subst(u.args[1], a, b, x))
    _map_parts(p -> _function_of_linear_subst(p, a, b, x), u)
end

# FunctionOfLinear[u, x]: {f(x), a, b} for u = f(a + b x), not a = 0 and b = 1; else False
function _function_of_linear2(u::Sym, x::Sym)
    lst = _function_of_linear(u, false, false, x, false)
    (lst === false || lst[1] === false || (_eq(lst[1], 0) && _eq(lst[2], 1))) && return false
    a, b = lst
    Any[_function_of_linear_subst(u, a, b, x), a, b]
end
FUNCS["FunctionOfLinear"] = (u, x) -> _function_of_linear2(_s(u), _s(x))

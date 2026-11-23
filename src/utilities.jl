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
FUNCS["NormalizeIntegrand"] = (u, x) -> _s(u)
FUNCS["ActivateTrig"] = u -> _s(u)
FUNCS["DeactivateTrig"] = (u, x = nothing) -> _s(u)
FUNCS["Numerator"] = u -> numerator(_s(u))
FUNCS["Denominator"] = u -> denominator(_s(u))
function _simplify_integrand(u)
    v = cancel(u)
    leafcount(v) <= leafcount(u) ? v : u
end

# ExpandIntegrand[u, x], ExpandIntegrand[u, v, x]: a sum of simpler terms. RUBI's has
# many special cases; this expands, and splits a rational function of x into partial
# fractions (approximate: other forms of the terms than RUBI's).
FUNCS["ExpandIntegrand"] = function (as...)
    u = length(as) == 3 ? _s(as[1]) * _s(as[2]) : _s(as[1])
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

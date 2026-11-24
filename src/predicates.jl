# RUBI's predicates (rule guards), after the definitions in RUBI's
# IntegrationUtilityFunctions.m. As there, the order predicates (GtQ, LtQ, ...) hold
# only for real numeric arguments: GtQ[a, 0] is false for a symbol a. Approximations of
# RUBI's heuristics are marked.

using SymJ: has, simplify, expand, free_symbols, N

_s(v) = v isa Sym ? v : Sym(v)
_isnum(u) = u isa Sym && u.kind == SymJ.NUMBER
_isexact(u) = _isnum(u) && SymJ.isexact(u.num)
_isrational(u) = _isexact(u)
_isinteger(u) = _isexact(u) && isinteger(u)
_rat(u) = Rational{BigInt}(u.num)       # exact number as a Julia Rational

# the value of a constant expression as a Julia number, or nothing
function _numval(u)
    u isa Number && return u
    u isa Sym || return nothing
    _isnum(u) && return SymJ.isexact(u.num) ? Rational{BigInt}(u.num) : Float64(u.num)
    isempty(free_symbols(u)) || return nothing
    v = try
        N(u)
    catch
        return nothing
    end
    v isa Number ? v : nothing
end
# (as RUBI's GtQ, N[Together[u]]: with symbols, over a common denominator first, so
# b/(b c' - a d') with c' = b c/(b c - a d), d' = b d/(b c - a d) is 1. Without it,
# 1.1.1.2 #32 never hands over to #31 and rewrites its own result until the timeout.)
function _realval(u)
    v = _numval(u)
    if v === nothing && u isa Sym && !isempty(free_symbols(u))
        w = try cancel(u) catch err; err isa InterruptException && rethrow(); return nothing end
        v = isempty(free_symbols(w)) ? _numval(w) : nothing
    end
    v === nothing && return nothing
    v isa Real && return v
    abs(imag(v)) <= 1e-12 * max(1, abs(real(v))) ? real(v) : nothing
end

# u == v as expressions: canonical forms first; a rational expression in its symbols
# (+, *, integer powers) over a common denominator, which decides it; simplify
# otherwise. (simplify on the large polynomial differences of 1.1.3.x guards took
# seconds a call.)
function _eq(u, v)
    d = _s(u) - _s(v)
    iszero(d) && return true
    _isnum(d) && return false
    if _is_ratexpr(d)
        w = try cancel(d) catch err; err isa InterruptException && rethrow(); nothing end
        w === nothing || return iszero(w)
    end
    iszero(simplify(d))
end

# built from symbols and exact numbers with +, * and integer powers
function _is_ratexpr(u::Sym)
    k = u.kind
    k == SymJ.SYMBOL && return true
    k == SymJ.NUMBER && return SymJ.isexact(u.num)
    k == SymJ.POW && return _isinteger(u.args[2]) && _is_ratexpr(u.args[1])
    (k == SymJ.ADD || k == SymJ.MUL) || return false
    SymJ.isexact(u.num) || return false
    all(_isinteger, u.exps) || return false
    all(_is_ratexpr, u.args)
end

_all(f, u::AbstractVector) = all(f, u)
_all(f, u) = f(u)

# ---- structure and value

@osrfunc FreeQ(u, x) = _all(t -> !(t isa Sym) || !has(t, _s(x)), u)
@osrfunc EqQ(u, v) = _eq(u, v)
@osrfunc NeQ(u, v) = !_eq(u, v)
@osrfunc IntegerQ(u) = _isinteger(u)
FUNCS["IntegersQ"] = (us...) -> all(_isinteger, us)
FUNCS["RationalQ"] = (us...) -> all(_isrational, us)
FUNCS["FractionQ"] = (us...) -> all(u -> _isrational(u) && !_isinteger(u), us)
FUNCS["HalfIntegerQ"] = (us...) -> all(u -> _isrational(u) && denominator(_rat(u)) == 2, us)
@osrfunc EvenQ(u) = _isinteger(u) && iseven(numerator(_rat(u)))
@osrfunc OddQ(u) = _isinteger(u) && isodd(numerator(_rat(u)))
@osrfunc IGtQ(u, n) = _isinteger(u) && _rat(u) > _rat(_s(n))
@osrfunc ILtQ(u, n) = _isinteger(u) && _rat(u) < _rat(_s(n))
@osrfunc IGeQ(u, n) = _isinteger(u) && _rat(u) >= _rat(_s(n))
@osrfunc ILeQ(u, n) = _isinteger(u) && _rat(u) <= _rat(_s(n))

function _cmp(op, us)
    vs = map(_realval, us)
    any(isnothing, vs) && return false
    all(i -> op(vs[i], vs[i+1]), 1:length(vs)-1)
end
FUNCS["GtQ"] = (us...) -> _cmp(>, us)
FUNCS["LtQ"] = (us...) -> _cmp(<, us)
FUNCS["GeQ"] = (us...) -> _cmp(>=, us)
FUNCS["LeQ"] = (us...) -> _cmp(<=, us)
FUNCS["Greater"] = FUNCS["GtQ"]
FUNCS["Less"] = FUNCS["LtQ"]
FUNCS["GreaterEqual"] = FUNCS["GeQ"]
FUNCS["LessEqual"] = FUNCS["LeQ"]
@osrfunc Equal(u, v) = _eq(u, v)
@osrfunc Unequal(u, v) = !_eq(u, v)
@osrfunc Not(b) = !truthy(b)

# And, Or, If: arguments evaluated as needed
SPECIAL["And"] = (as, c) -> all(a -> truthy(ev(a, c)), as)
SPECIAL["Or"] = (as, c) -> any(a -> truthy(ev(a, c)), as)
SPECIAL["If"] = (as, c) -> truthy(ev(as[1], c)) ? ev(as[2], c) :
    length(as) >= 3 ? ev(as[3], c) : throw(OSRError("If without else"))

# PosQ: u "looks positive". RUBI's PosAux: a number by its real part (or imaginary part
# when that is 0); an odd power by its base; a product by its first factor and the rest;
# a sum by its first term; anything else true. Mathematica orders a sum with its number
# first, then terms in its canonical order, which is not SymJ's, so for sums this is an
# approximation (the rules stay correct; the form of the answer may differ).
function _posq(u)
    u = _s(u)
    _isrational(u) && return _rat(u) > 0
    v = _numval(u)
    if v !== nothing
        r, i = real(v), imag(v)
        return abs(r) <= 1e-12 * max(1, abs(i)) ? i > 0 : r > 0
    end
    k = u.kind
    if k == SymJ.POW
        e = u.args[2]
        return _isinteger(e) && isodd(numerator(_rat(e))) ? _posq(u.args[1]) : true
    elseif k == SymJ.MUL
        c = u.num
        iszero(c) && return false
        isone(c) || return (c > 0) == _posq(u / Sym(c))
        fs = [a^e for (a, e) in zip(u.args, u.exps)]
        length(fs) == 1 && return _posq(fs[1])
        return _posq(fs[1]) == _posq(prod(fs[2:end]))
    elseif k == SymJ.ADD
        iszero(u.num) || return u.num > 0
        return _posq(Sym(u.coefs[1]) * u.args[1])
    end
    true
end
@osrfunc PosQ(u) = _posq(u)
@osrfunc NegQ(u) = !_eq(u, 0) && !_posq(u)

# LeafCount: the size of the expression tree, as Mathematica counts it (approximately)
function leafcount(u)
    u isa Sym || return 1
    k = u.kind
    k in (SymJ.SYMBOL, SymJ.CONSTANT, SymJ.PARAMETER) && return 1
    k == SymJ.NUMBER && return _isinteger(u) ? 1 : 3
    if k == SymJ.ADD
        n = 1 + (iszero(u.num) ? 0 : 1)
        for (a, c) in zip(u.args, u.coefs)
            n += leafcount(a) + (isone(c) ? 0 : 2)
        end
        return n
    elseif k == SymJ.MUL
        n = 1 + (isone(u.num) ? 0 : 1)
        for (a, e) in zip(u.args, u.exps)
            n += isone(e) ? leafcount(a) : 1 + leafcount(a) + leafcount(e)
        end
        return n
    end
    1 + sum(leafcount, u.args; init = 0) + sum(leafcount, u.exps; init = 0)
end
@osrfunc LeafCount(u) = Sym(leafcount(u))

# SimplerQ[u, v]: u is simpler than v. RUBI compares numbers by size and otherwise by
# structure; this keeps the number rules and uses leaf counts for the rest (approximate).
function _simplerq(u, v)
    u, v = _s(u), _s(v)
    if _isinteger(u) && _isinteger(v)
        a, b = abs(_rat(u)), abs(_rat(v))
        return a == b ? _rat(v) < 0 : a < b
    end
    _isinteger(u) && return true
    _isinteger(v) && return false
    _isrational(u) && _isrational(v) &&
        return denominator(_rat(u)) == denominator(_rat(v)) ? abs(numerator(_rat(u))) < abs(numerator(_rat(v))) :
               denominator(_rat(u)) < denominator(_rat(v))
    _isnum(u) && return true
    _isnum(v) && return false
    leafcount(u) < leafcount(v)
end
@osrfunc SimplerQ(u, v) = _simplerq(u, v)

# SumSimplerQ[u, v]: u + v is simpler than u. Exact for rationals (as RUBI); for other
# arguments a structural comparison (approximate).
function _sumsimplerq(u, v)
    u, v = _s(u), _s(v)
    if _isrational(u) && _isrational(v)
        a, b = _rat(u), _rat(v)
        return b == 0 ? false : b > 0 ? a < -1 : a >= 1
    end
    w = expand(u + v)
    _simplerq(w, expand(u)) && !_simplerq(w, expand(v))
end
@osrfunc SumSimplerQ(u, v) = _sumsimplerq(u, v)

# ---- polynomials in x

# u as a polynomial in x: its coefficients, lowest degree first, or nothing
function _coeffs(u, x)
    x = _s(x)
    x.kind == SymJ.SYMBOL && !_maybe_poly(_s(u), x) && return nothing
    u = expand(_s(u))
    has(u, x) || return Sym[u]
    try
        p = SymJ.Poly(u, x)
        d = SymJ.degree(p)
        cs = SymJ.coefficients(p)
        length(cs) == d + 1 ? Sym[_s(c) for c in reverse(cs)] : _coeffs_slow(u, x, d)
    catch
        nothing
    end
end
# u could be a polynomial in x: x is not inside a function, nor raised to a power that is
# not a nonnegative integer. A quick test before expand and Poly, which were most of the
# time of guards on trig integrands (PolyQ, LinearQ: 500 calls, 2.7 s for one problem).
function _maybe_poly(u::Sym, x::Sym)
    has(u, x) || return true
    k = u.kind
    k == SymJ.SYMBOL && return true
    k == SymJ.FN && return false
    if k == SymJ.POW
        e = u.args[2]
        return _isinteger(e) && _rat(e) >= 0 && _maybe_poly(u.args[1], x)
    end
    for (i, a) in enumerate(u.args)
        if k == SymJ.MUL && has(a, x)
            e = u.exps[i]
            (_isinteger(e) && _rat(e) >= 0) || return false
        end
        _maybe_poly(a, x) || return false
    end
    true
end

function _coeffs_slow(u, x, d)
    terms = u.kind == SymJ.ADD ? [Sym(c) * a for (a, c) in zip(u.args, u.coefs)] : Sym[u]
    u.kind == SymJ.ADD && !iszero(u.num) && push!(terms, Sym(u.num))
    cs = fill(SymJ.ZERO, d + 1)
    for t in terms
        k = 0
        if t == x
            k = 1
        elseif t.kind == SymJ.POW && t.args[1] == x
            k = Int(_rat(t.args[2]))
        elseif t.kind == SymJ.MUL
            i = findfirst(==(x), t.args)
            i === nothing || (k = Int(_rat(t.exps[i])))
        end
        cs[k+1] += k == 0 ? t : t / x^k
    end
    cs
end

FUNCS["PolyQ"] = function (u, x, n = nothing)
    x isa AbstractVector && return false
    x = _s(x)
    # PolyQ[u, x^n]: as RUBI, a polynomial in x itself, with only powers of x^n (n a
    # positive integer), or for other v, coefficients in x^v free of x. (Not "free of
    # the subterm x^n": (1 + a x)/(1 - a x) was a polynomial of degree 0 in x^2, and
    # 1.1.3.7 #12 expanded it again and again.)
    if x.kind == SymJ.POW && x.args[1].kind == SymJ.SYMBOL && n === nothing
        b, v = x.args
        if _isinteger(v) && _rat(v) > 0
            cs = _coeffs(u, b)
            (cs === nothing || any(c -> has(c, b), cs)) && return false
            k = Int(_rat(v))
            return all(i -> i % k == 0 || iszero(cs[i+1]), 0:length(cs)-1)
        end
        cs = _coeffs(u, x)
        return cs !== nothing && !any(c -> has(c, b), cs)
    end
    cs = _coeffs(u, x)
    cs === nothing && return false
    any(c -> has(c, _s(x)), cs) && return false
    n === nothing && return true
    _isinteger(n) ? length(cs) - 1 == _rat(n) : false
end
FUNCS["PolynomialQ"] = FUNCS["PolyQ"]
@osrfunc LinearQ(u, x) = FUNCS["PolyQ"](u, x, Sym(1)) && !iszero(_coeffs(u, x)[2])
@osrfunc QuadraticQ(u, x) = FUNCS["PolyQ"](u, x, Sym(2)) && !iszero(_coeffs(u, x)[3])
FUNCS["Expon"] = (u, x) -> (cs = _coeffs(u, x); cs === nothing ? throw(OSRError("Expon")) : Sym(length(cs) - 1))
FUNCS["Coefficient"] = function (u, x, n = Sym(1))
    cs = _coeffs(u, x)
    cs === nothing && throw(OSRError("Coefficient: not a polynomial"))
    k = Int(_rat(n))
    0 <= k < length(cs) ? cs[k+1] : SymJ.ZERO
end
FUNCS["Coeff"] = FUNCS["Coefficient"]

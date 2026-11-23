# Sums and products: RUBI's IntSum, IntTerm and the free/nonfree parts of an expression
# (IntegrationUtilityFunctions.m, RUBI 4.16.1).

_terms(u::Sym) = u.kind == SymJ.ADD ?
    vcat(Sym[Sym(c) * a for (a, c) in zip(u.args, u.coefs)], iszero(u.num) ? Sym[] : Sym[Sym(u.num)]) : Sym[u]
function _factors(u::Sym)
    u.kind == SymJ.MUL || return Sym[u]
    fs = Sym[a^e for (a, e) in zip(u.args, u.exps)]
    isone(u.num) || pushfirst!(fs, Sym(u.num))
    fs
end
_free(u, x) = !has(_s(u), _s(x))

@osrfunc SumQ(u) = u isa Sym && u.kind == SymJ.ADD
@osrfunc ProductQ(u) = u isa Sym && u.kind == SymJ.MUL
@osrfunc PowerQ(u) = u isa Sym && u.kind == SymJ.POW
@osrfunc AtomQ(u) = !(u isa Sym) || u.kind in (SymJ.NUMBER, SymJ.SYMBOL, SymJ.CONSTANT, SymJ.PARAMETER)
@osrfunc FreeTerms(u, x) = sum(t for t in _terms(_s(u)) if _free(t, x); init = SymJ.ZERO)
@osrfunc NonfreeTerms(u, x) = sum(t for t in _terms(_s(u)) if !_free(t, x); init = SymJ.ZERO)
@osrfunc FreeFactors(u, x) = prod(f for f in _factors(_s(u)) if _free(f, x); init = SymJ.ONE)
@osrfunc NonfreeFactors(u, x) = prod(f for f in _factors(_s(u)) if !_free(f, x); init = SymJ.ONE)
FUNCS["Star"] = (u, v) -> _s(u) * _s(v)

# IntSum[u, x]: the integral of a sum, term by term
_intsum(u::Sym) = FUNCS["FreeTerms"](u, X) * X + _intterm(FUNCS["NonfreeTerms"](u, X))

# IntTerm[u, x]: c*(a + b*x)^m in closed form, a sum term by term, else c*Int[v, x]
function _intterm(u::Sym)
    iszero(u) && return SymJ.ZERO
    u.kind == SymJ.ADD && return sum(_intterm, _terms(u); init = SymJ.ZERO)
    c = FUNCS["FreeFactors"](u, X)
    w = FUNCS["NonfreeFactors"](u, X)
    v, m = w.kind == SymJ.POW ? (w.args[1], w.args[2]) : (w, SymJ.ONE)
    if _free(m, X) && FUNCS["LinearQ"](v, X)
        v = cancel(v)
        b = FUNCS["Coefficient"](v, X, Sym(1))
        _eq(m, -1) && return c * log(FUNCS["RemoveContent"](v, X)) / b
        isone(m) && isone(c) && v.kind == SymJ.ADD && return _intsum(v)
        return c * v^(m + 1) / (b * (m + 1))
    end
    c * _int(w, _DEPTH[] + 1)
end
FUNCS["IntSum"] = (u, x) -> _intsum(_s(u))
FUNCS["IntTerm"] = (u, x) -> _intterm(_s(u))

# ---- host rules: stopgaps for RUBI rules the OSR data does not have yet
#
# Each entry stands in for an OSR rule file that is empty (OSR known issue 3) and is
# used only while that file has no rules. The rules are written in OSR's own JSON form,
# so they go through the same loader as the data.

const HOST_RULES = Dict{String,Vector{Any}}(
    # 1.4.1: Int[u_, x_Symbol] := IntSum[u, x] /; SumQ[u]
    "1-algebraic/1.4-miscellaneous/1.4.1-Algebraic-function-simplification.json" => Any[
        Dict{String,Any}("id" => 1, "pattern" => Any["Int", "u_", "x_symbol"],
            "constraints" => Any[Any["SumQ", "u"]], "result" => Any["IntSum", "u", "x"]),
        # Int[a_, x_Symbol] := a*x /; FreeQ[a, x]: a constant integrand. RUBI's own copy
        # is in the older "9.1 Integrand simplification rules", which 4.16.1 does not
        # load; without some such rule a constant integrand is left unevaluated.
        Dict{String,Any}("id" => 2, "pattern" => Any["Int", "a_", "x_symbol"],
            "constraints" => Any[Any["FreeQ", "a", "x"]], "result" => Any["Multiply", "a", "x"]),
    ],
)

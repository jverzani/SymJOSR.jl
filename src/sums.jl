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
# The rules are written in OSR's own JSON form, so they go through the same loader as
# the data.

# Rules of RUBI 4.16.1 that OSR leaves out of files that are not empty (rules wrapped in
# If[TrueQ[$LoadShowSteps], ...], rules with With). Each is put first in its file ("at" =>
# "end": last) while the file has no rule with the same result head; `head` names it.
const HOST_MISSING = Dict{String,Vector{Any}}(
    # 2.3 (RUBI's line 104): Int[u_, x_] := With[{v = FunctionOfExponential[u, x]},
    # v/D[v, x] Subst[Int[FunctionOfExponentialFunction[u, x]/x, x], x, v]] /;
    # FunctionOfExponentialQ[u, x] && ...: the substitution v = F^(b x), dropped by OSR
    # (With). Last in its file, as in RUBI; its MatchQ exclusions are
    # FunctionOfExponentialExcludedQ.
    "2-exponentials/2.3-Miscellaneous-exponentials.json" => Any[
        Dict{String,Any}("id" => 1000, "head" => "FunctionOfExponentialFunction", "at" => "end",
            "pattern" => Any["Int", "u_", "x_symbol"],
            "constraints" => Any[Any["FunctionOfExponentialQ", "u", "x"],
                Any["Not", Any["FunctionOfExponentialExcludedQ", "u", "x"]]],
            "result" => Any["Multiply", Any["FunctionOfExponential", "u", "x"],
                Any["Power", Any["D", Any["FunctionOfExponential", "u", "x"], "x"], -1],
                Any["Subst", Any["Int", Any["Multiply", Any["FunctionOfExponentialFunction", "u", "x"], Any["Power", "x", -1]], "x"],
                    "x", Any["FunctionOfExponential", "u", "x"]]]),
    ],
    # 4.1.0.1: Int[u_, x_Symbol] := Int[DeactivateTrig[u, x], x] /;
    # FunctionOfTrigOfLinearQ[u, x]: hyperbolic functions of linear arguments as trig
    # functions of imaginary ones, and cos as sin(+ π/2), for the trig rules.
    # (HasTrigQ and DeactivateChangesQ are ours: a quick test first, as every integrand
    # comes here; and RUBI's active and inert trig functions are the same functions here,
    # so the rule is only of use when it changes the integrand.)
    "4-trig/4.1-sine/4.1.0.1-(a-sin)^m-(b-trg)^n.json" => Any[
        Dict{String,Any}("id" => 0, "head" => "DeactivateTrig",
            "pattern" => Any["Int", "u_", "x_symbol"],
            "constraints" => Any[Any["HasTrigQ", "u"], Any["FunctionOfTrigOfLinearQ", "u", "x"], Any["DeactivateChangesQ", "u", "x"]],
            "result" => Any["Int", Any["DeactivateTrig", "u", "x"], "x"]),
    ],
)

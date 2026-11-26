# Arbitrary functions and their derivatives: Mathematica's f[x] and Derivative[n][f][x],
# written in OSR as ["f", "x"] (or ["Apply", "f", ["List", "x"]]) and
# ["Apply", ["Apply", ["Derivative", n], ["List", "f"]], ["List", "x"]]. RUBI's 9.1
# "Derivative integration rules" and the 8.10 "Formal derivatives" test problems use them.
#
# In SymJ f(x) is a function node of an unknown function, SymFunction(:f)(x), and its
# n-th derivative is n nested Derivative(…, x) nodes; at an argument a that is not a
# symbol, Derivative(f^(n-1)(t), t, a) (SymDerivative).

using SymJ: SymFunction, SymDerivative

# Derivative[n] and Derivative[n][f] as values, to be applied
struct DerivOp
    n::Any
end
struct DerivFn
    f::SymFunction
    n::Int
end

_symfunction(f::SymFunction) = f
_symfunction(f::Sym) = f.kind == SymJ.SYMBOL ? SymFunction(Symbol(string(f))) :
    throw(OSRError("Derivative: $f is not a function"))
_symfunction(f) = throw(OSRError("Derivative: $f is not a function"))

FUNCS["Derivative"] = n -> DerivOp(n)

# f^(n)(u): f(u) for n = 0
function _fderiv(f::SymFunction, n::Int, u)
    n == 0 ? f(_s(u)) : SymDerivative(f, n)(_s(u))
end

# Apply[h, {args…}], h[args…] with h a value: a bound head, Derivative[n], Derivative[n][f]
SPECIAL["Apply"] = function (as, c::Ctx)
    length(as) == 2 || throw(OSRError("Apply: arity"))
    h = ev(as[1], c)
    vs = ev(as[2], c)
    vs isa AbstractVector || throw(OSRError("Apply: arguments are not a list"))
    if h isa DerivOp
        length(vs) == 1 || throw(OSRError("Derivative: one function"))
        n = h.n
        (n isa Sym && _isinteger(n) && n >= 0) || throw(OSRError("Derivative: order $n"))
        return DerivFn(_symfunction(vs[1]), Int(n))
    elseif h isa DerivFn
        length(vs) == 1 || throw(OSRError("Derivative: functions of one argument"))
        return _fderiv(h.f, h.n, vs[1])
    elseif h isa SymFunction
        return h(vs...)
    elseif h isa Sym && h.kind == SymJ.SYMBOL         # a name read from a test problem
        return SymFunction(Symbol(string(h)))(vs...)
    end
    _applyhead(h, vs)
end

# ---- patterns

# f_[x_] (a head slot) and Derivative[n][f_][x_]. With n a number the pattern is SymJ's
# own nest, Derivative(…Derivative((~f)(x), x)…, x), so f is matched as a head slot and
# agrees with f_ elsewhere in the pattern. With n a wildcard, one slot ∂n∂f matches an
# n-th derivative of an unknown function of x, n ≥ 1, and n and f are read off the match
# (_derived_bindings).
function _pat_apply(as)
    length(as) == 2 && isapp(as[2]) && head(as[2]) == "List" ||
        throw(OSRError("pattern: Apply without a list"))
    h, ps = as[1], [pat(a) for a in args(as[2])]
    w = h isa AbstractString ? wildcard(h) : nothing
    w !== nothing && w[2] === :blank && return Expr(:call, :(~$(w[1])), ps...)
    if isapp(h) && head(h) == "Apply" && length(h) == 3 && isapp(h[2]) && head(h[2]) == "Derivative" &&
       length(h[2]) == 2 && isapp(h[3]) && head(h[3]) == "List" && length(h[3]) == 2 && length(ps) == 1
        n, f = h[2][2], h[3][2]
        wf = f isa AbstractString ? wildcard(f) : nothing
        (wf !== nothing && wf[2] === :blank && ps[1] === XNAME) ||
            throw(OSRError("pattern: Derivative of $f at $(as[2])"))
        if n isa Integer && n >= 1
            e = Expr(:call, :(~$(wf[1])), XNAME)
            for _ in 1:n
                e = Expr(:call, :Derivative, e, XNAME)
            end
            return e
        end
        wn = n isa AbstractString ? wildcard(n) : nothing
        (wn !== nothing && wn[2] === :blank) || throw(OSRError("pattern: Derivative order $n"))
        slot = Symbol("∂", wn[1], "∂", wf[1])
        return :(~$(Expr(:(::), slot, _isfderiv)))
    end
    throw(OSRError("pattern: unsupported Apply"))
end

# an unknown function, as SymJ has it (no FUNCTION_RULES entry: it differentiates one by
# the chain rule), other than the inert functions of RUBI's answers (AppellF1, Int)
_unknown_fn(u::Sym) = u.kind == SymJ.FN && !haskey(SymJ.FUNCTION_RULES, u.name) &&
    !(u.name in _INERT_FNS)
const _INERT_FNS = Set{Symbol}([values(FUNCTION_NAMES)..., :Int, :Unintegrable, :CannotIntegrate])

# (n, f) for u = f^(n)(x), n ≥ 1, f unknown, else nothing
function _fderiv_parts(u)
    u isa Sym || return nothing
    n = 0
    while u.kind == SymJ.FN && u.name === :Derivative && length(u.args) == 2 && isequal(u.args[2], X)
        u, n = u.args[1], n + 1
    end
    n >= 1 && _unknown_fn(u) && length(u.args) == 1 && isequal(u.args[1], X) || return nothing
    (n, SymFunction(u.name))
end
_isfderiv(u) = _fderiv_parts(u) !== nothing

# the bindings of a match with the derived n and f of its ∂n∂f slots added, or nothing
# when they disagree with the f bound elsewhere
function _derived_bindings(d)
    any(k -> startswith(string(k), "∂"), keys(d)) || return d
    d = copy(d)
    for k in collect(keys(d))
        s = string(k)
        startswith(s, "∂") || continue
        nname, fname = split(s[nextind(s, 1):end], "∂")
        n, f = _fderiv_parts(d[k])
        delete!(d, k)
        fk = Symbol(fname)
        haskey(d, fk) && !isequal(d[fk], f) && return nothing
        d[fk] = f
        d[Symbol(nname)] = Sym(n)
    end
    d
end

# ---- checking answers: unknown functions as concrete ones

# The unknown functions of the integrand u (8.10's f, g, F), in u and in its antiderivative
# r, replaced by functions with no special relation to each other, positive for real
# arguments (so √f and log f are real): the k-th name, in order, by
# t -> exp(t/(k + 1)) + t^2/(k + 3) + k + 1; Derivative nodes are evaluated again. Gives
# (u, r) unchanged when u has none. (Only u's: an inert function of an answer, AppellF1,
# is not to be replaced.)
function _concrete_functions(u::Sym, r::Sym)
    names = sort!(collect(_unknown_names!(Set{Symbol}(), u)))
    isempty(names) && return u, r
    fs = Dict(nm => (k = i; a -> exp(a / (k + 1)) + a^2 / (k + 3) + (k + 1)) for (i, nm) in enumerate(names))
    _with_functions(u, fs), _with_functions(r, fs)
end
function _unknown_names!(out, u::Sym)
    _unknown_fn(u) && push!(out, u.name)
    foreach(a -> _unknown_names!(out, a), u.args)
    foreach(a -> _unknown_names!(out, a), u.exps)
    out
end
function _with_functions(u::Sym, fs)
    isempty(u.args) && return u
    if u.kind == SymJ.FN
        as = Sym[_with_functions(a, fs) for a in u.args]
        F = get(fs, u.name, nothing)
        F === nothing || return F(only(as))
        u.name === :Derivative && return _derivative_of(as)
        return apply_function(u.name, as)
    end
    SymJ._rw_parts(a -> _with_functions(a, fs), u)
end
# Derivative(e, t) and Derivative(e, t, a) of a known e: diff(e, t), at a
function _derivative_of(as)
    d = diff(as[1], as[2])
    length(as) == 2 ? d : subs(d, as[2] => as[3])
end

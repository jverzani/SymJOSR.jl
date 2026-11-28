# Running the OSR test problems (tests/ in the Integration tree) against the rules.

"""
    read_osr(n; free = true) -> Sym

The SymJ value of an OSR expression, as found in a test problem: names not bound are
symbols, and `x` is the integration variable.
"""
read_osr(n; free::Bool = true) = _s(ev(n, Ctx(Dict{Symbol,Any}(), 0, free)))

# d/dx r == f, numerically at a few points: parameters and x distinct rationals ±n/997
# with n/997 in (0.3, 1.7), so not 1 or each other, where integrands are often singular.
# A point where either side is infinite or can't be evaluated is a singularity, not a
# disagreement, and is replaced. The points depend only on f, so a problem gets the
# same verdict every run.
#
# Branch cuts can make the two sides differ where the answer is right. So first only
# fair points are used: every base of a non-integer power, in r and in f, positive, and
# every ₂F₁ argument off its cut z ≥ 1 (values positive at first, then of either sign:
# an argument such as b x/a + 1 is above 1 for all positive values). Disagreement at a
# fair point is "wrong". When too few fair points turn up in this range of values
# (asin(2x - 5) needs 2 < x < 3), points need only keep the ₂F₁s off their cuts.
function _verify(r::Sym, f::Sym; points = 3)
    f, r = _concrete_functions(f, r)            # f(x), f'(x): as concrete functions
    d = diff(r, X) - f
    syms = sort!(collect(SymJ.free_symbols(d) ∪ SymJ.free_symbols(f) ∪ Set([X])); by = string)
    zs = _hyp_args!(Sym[], r)
    bs = unique!(_frac_bases!(_frac_bases!(Sym[], r), f))
    floats = _has_special(r) || _has_special(f)
    v = _verify_at(d, f, syms, zs, bs, points, Random.Xoshiro(hash(string(f))), true, floats)
    v === nothing || return v
    _verify_at(d, f, syms, zs, Sym[], points, Random.Xoshiro(hash(string(f))), false, floats) === true
end

# a function other than log: evaluated at floats (see _verify_at)
_has_special(e::Sym) = (e.kind == SymJ.FN && e.name !== :log) ||
    any(_has_special, e.args) || any(_has_special, e.exps)

# true (agreement at `points` points), false (a disagreement), or nothing (too few
# points). `fair`: values positive for the first tries, then of either sign; otherwise
# positive until a point puts a ₂F₁ on its cut.
function _verify_at(d, f, syms, zs, bs, points, rng, fair, floats)
    good, signed = 0, false
    for i in 1:(fair ? 20 : 12) * points
        fair && (signed = i > 2points)
        vs = Random.randperm(rng, 1400)[1:length(syms)] .+ 299
        # exact for rational expressions and logs, so that large cancellations (rational
        # answers with (b c - a d)^-8) are exact; floats otherwise: SymJ's N at exact
        # arguments raises its BigFloat precision until the value is certain, which took
        # ~10 s for a ₂F₁ and did not finish for incomplete gammas of complex arguments,
        # or for sqrt(a + b asin(c x)) where c x > 1
        ps = [s => Sym((signed && rand(rng, Bool) ? -v : v) // 997) for (s, v) in zip(syms, vs) if v != 997]
        floats && (ps = [s => Sym(Float64(v.num)) for (s, v) in ps])
        length(ps) == length(syms) || continue
        all(b -> _positive_at(b, ps, floats), bs) || continue
        any(z -> _on_cut(z, ps, floats), zs) && (signed = true; continue)
        dv = try _num(subs(d, ps...), floats) catch; continue end
        fv = try _num(subs(f, ps...), floats) catch; continue end
        dv isa Number && fv isa Number || return false
        isfinite(dv) && isfinite(fv) || continue
        abs(dv) <= 1e-8 * (1 + abs(fv)) || return false
        (good += 1) == points && return true
    end
    nothing
end

# the last arguments (z) of the ₂F₁s in e
function _hyp_args!(out, e::Sym)
    e.kind == SymJ.FN && e.name === :_₂F₁ && push!(out, e.args[end])
    foreach(a -> _hyp_args!(out, a), e.args)
    foreach(a -> _hyp_args!(out, a), e.exps)
    out
end

# the bases of the powers in e with an exponent that is not an integer
function _frac_bases!(out, e::Sym)
    if e.kind == SymJ.POW
        _isinteger(e.args[2]) || push!(out, e.args[1])
    elseif e.kind == SymJ.MUL
        for (b, x) in zip(e.args, e.exps)
            _isinteger(x) || push!(out, b)
        end
    end
    foreach(a -> _frac_bases!(out, a), e.args)
    foreach(a -> _frac_bases!(out, a), e.exps)
    out
end

# the value of e: at floats, SymJ's plain complex evaluation; N would certify it (a tiny
# imaginary part sent N to 512- and 2048-bit evaluations that did not finish)
_num(e::Sym, floats::Bool) = floats ? SymJ._evalc(e) : N(e)

# b at the point ps is a positive real number
function _positive_at(b::Sym, ps, floats = false)
    v = try _num(subs(b, ps...), floats) catch; return false end
    v isa Number && isfinite(v) || return false
    abs(imag(v)) <= 1e-12 * (1 + abs(v)) && real(v) > 0
end

# z at the point ps is on ₂F₁'s branch cut, [1, ∞), or can't be evaluated
function _on_cut(z::Sym, ps, floats = false)
    v = try _num(subs(z, ps...), floats) catch; return true end
    v isa Number || return true
    abs(imag(v)) <= 1e-12 * (1 + abs(v)) && real(v) >= 1 - 1e-12
end

"""
    test_problems(; files, rules = load_rules(), timeout = 5.0, verbose = false)

Integrate the OSR test problems of the test files whose path contains one of `files`,
and sort them into `:verified` (an antiderivative, checked by differentiating it
numerically), `:wrong` (an answer whose derivative is not the integrand),
`:unevaluated` (no answer), `:timeout` and `:error`. Gives the counts and, per problem,
`(file, id, status, integrand, result)`.
"""
function test_problems(; files, rules::RuleSet = load_rules(), timeout::Real = 5.0, verbose::Bool = false)
    root = joinpath(rules_dir(), "tests")
    out = NamedTuple[]
    counts = Dict(s => 0 for s in (:verified, :wrong, :unevaluated, :timeout, :error, :skipped))
    for (d, _, fs) in walkdir(root), f in sort(fs)
        endswith(f, ".json") || continue
        rel = _relpath(joinpath(d, f), root)
        any(s -> occursin(s, rel), files) || continue
        for t in JSON.parsefile(joinpath(d, f))["tests"]
            status, u, r = :skipped, nothing, nothing
            if t["variable"] == "x"
                status, u, r = _run_problem(t["expression"], rules, timeout; expected = get(t, "expected_result", nothing))
            end
            counts[status] += 1
            push!(out, (file = rel, id = t["id"], status = status, integrand = u, result = r))
            verbose && status !== :verified && println(rpad(string(status), 12), rel, " #", t["id"], ": ", u, "  =>  ", r)
        end
    end
    (counts = counts, problems = out)
end

function _run_problem(expr, rules, timeout; expected = nothing)
    u = try
        read_osr(expr)
    catch
        return (:error, nothing, nothing)
    end
    e = expected === nothing ? nothing : (try read_osr(expected) catch; nothing end)
    _check(u, rules, timeout; expected = e isa Sym ? e : nothing)
end

# integrate u (in the integration variable X) with the rules, within timeout seconds, and
# check the answer: (status, u, result), status one of :verified, :wrong, :unevaluated,
# :timeout, :error. With an expected antiderivative (the test problem's), an answer that
# differs from it by a constant is verified (_formal_match); otherwise, or when that is
# not shown, the answer's derivative is compared with u numerically (_verify).
function _check(u::Sym, rules, timeout; expected::Union{Sym,Nothing} = nothing)
    oldR, oldT, oldD = _RULESET[], _TRACE[], _DEADLINE[]
    _RULESET[], _TRACE[], _DEADLINE[] = rules, nothing, time() + timeout
    r = try
        _int(u, 0)
    catch err
        err isa InterruptException && rethrow()
        err isa TimedOut && return (:timeout, u, nothing)
        err isa GiveUp || err isa Cycle ? nothing : return (:error, u, sprint(showerror, err)[1:min(end, 200)])
    finally
        _RULESET[], _TRACE[], _DEADLINE[] = oldR, oldT, oldD
    end
    (r === nothing || _has_int(r)) && return (:unevaluated, u, r)
    ok = expected !== nothing && (try _formal_match(r, expected) catch; false end)
    ok || (ok = try _verify(r, u) catch; false end)
    ok || (ok = expected !== nothing && (try _const_diff(r, expected, u) catch; false end))
    (ok ? :verified : :wrong, u, r)
end

# r and e differ by a constant, shown symbolically: r == e, or r - e is free of x after
# expansion, after trig functions of an imaginary argument are written as hyperbolic ones
# (Mathematica's automatic Cot[I u] = -I Coth[u]: RUBI's answers have the hyperbolic
# form), after cancellation, or its derivative expands to 0. RUBI's expected answers
# (atanh(exp(a + b x)), polylogs of exp(a + b x), …) can fail the numeric check, whose
# points fall on their branch cuts; an answer equal to one of them up to a constant is as
# good as RUBI's. (No simplify: on AppellF1 answers with fractional powers it took
# minutes, and can not be interrupted.)
function _formal_match(r::Sym, e::Sym)
    isequal(r, e) && return true
    t = expand(r - e); has(t, X) || return true
    t = expand(_imag_to_hyp(_unshift(r)) - _imag_to_hyp(_unshift(e))); has(t, X) || return true
    t = cancel(t); has(t, X) || return true
    iszero(expand(diff(t, X)))
end

# sin(i u) = i sinh(u), cos(i u) = cosh(u), tan(i u) = i tanh(u), cot(i u) = -i coth(u),
# sec(i u) = sech(u), csc(i u) = -i csch(u), for u free of i
const _IMAG_HYP = Dict(:sin => (:sinh, 1), :cos => (:cosh, 0), :tan => (:tanh, 1),
                       :cot => (:coth, -1), :sec => (:sech, 0), :csc => (:csch, -1))
_negroot(b::Sym, e::Sym) = _isrational(b) && _rat(b) < 0 && _isrational(e) && !_isinteger(e)
_has_i(u::Sym) = !isreal(u.num) || (u.kind == SymJ.ADD && !all(isreal, u.coefs)) ||
    (u.kind == SymJ.POW && _negroot(u.args[1], u.args[2])) ||
    (u.kind == SymJ.MUL && any(((b, k),) -> _negroot(b, k), zip(u.args, u.exps))) ||
    any(_has_i, u.args) || any(_has_i, u.exps)
function _imag_to_hyp(u::Sym)
    isempty(u.args) && return u
    v = SymJ._rw_parts(_imag_to_hyp, u)
    if v.kind == SymJ.FN && haskey(_IMAG_HYP, v.name) && length(v.args) == 1
        w = expand(v.args[1] / Sym(im))
        if !_has_i(w)
            h, k = _IMAG_HYP[v.name]
            return Sym(im)^k * apply_function(h, Sym[w])
        end
    end
    # the integrals: Ci(i w) = Chi(w) + iπ/2 (Re w > 0), Si(i w) = i Shi(w), Chi(i w) =
    # Ci(w) + iπ/2, Shi(i w) = i Si(w)
    if v.kind == SymJ.FN && v.name in (:cosint, :sinint, :coshint, :sinhint) && length(v.args) == 1
        w = expand(v.args[1] / Sym(im))
        if !_has_i(w)
            v.name === :cosint && return apply_function(:coshint, Sym[w]) + Sym(im) * SymJ.PI / 2
            v.name === :sinint && return Sym(im) * apply_function(:sinhint, Sym[w])
            v.name === :coshint && return apply_function(:cosint, Sym[w]) + Sym(im) * SymJ.PI / 2
            return Sym(im) * apply_function(:sinint, Sym[w])
        end
    end
    v
end

# r - e is the same at several values of x (the parameters fixed), numerically: for
# answers that evaluate, in forms the formal check does not relate to RUBI's (erf of
# (-1)^(1/4) z where RUBI has Fresnel integrals), and whose derivative fails the
# numeric check. Values as in _verify, n/997 in (0.3, 1.7), for two choices of the
# parameters, four values of x each.
function _const_diff(r::Sym, e::Sym, u::Sym; params = 2, xs = 4)
    r, e = last(_concrete_functions(u, r)), last(_concrete_functions(u, e))   # u's unknown functions
    d = r - e
    syms = sort!(collect(setdiff(SymJ.free_symbols(d), Set([X]))); by = string)
    rng = Random.Xoshiro(hash(string(e)))
    sets = 0
    for _ in 1:4params
        ps = [s => Sym(Float64(v) / 997) for (s, v) in zip(syms, Random.randperm(rng, 1400)[1:length(syms)] .+ 299)]
        vals = ComplexF64[]
        for _ in 1:4xs
            xv = Sym(Float64(rand(rng, 300:1700)) / 997)
            rv = try SymJ._evalc(subs(r, ps..., X => xv)) catch; continue end
            ev_ = try SymJ._evalc(subs(e, ps..., X => xv)) catch; continue end
            rv isa Number && ev_ isa Number && isfinite(rv) && isfinite(ev_) || continue
            dv = rv - ev_
            isempty(vals) || abs(dv - vals[1]) <= 1e-8 * (1 + abs(rv) + abs(ev_)) || return false
            push!(vals, dv)
            length(vals) == xs && break
        end
        length(vals) == xs && (sets += 1) == params && return true
    end
    false
end

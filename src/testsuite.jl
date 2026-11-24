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
                status, u, r = _run_problem(t["expression"], rules, timeout)
            end
            counts[status] += 1
            push!(out, (file = rel, id = t["id"], status = status, integrand = u, result = r))
            verbose && status !== :verified && println(rpad(string(status), 12), rel, " #", t["id"], ": ", u, "  =>  ", r)
        end
    end
    (counts = counts, problems = out)
end

function _run_problem(expr, rules, timeout)
    u = try
        read_osr(expr)
    catch
        return (:error, nothing, nothing)
    end
    _check(u, rules, timeout)
end

# integrate u (in the integration variable X) with the rules, within timeout seconds, and
# check the answer: (status, u, result), status one of :verified, :wrong, :unevaluated,
# :timeout, :error
function _check(u::Sym, rules, timeout)
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
    ok = try _verify(r, u) catch; false end
    (ok ? :verified : :wrong, u, r)
end

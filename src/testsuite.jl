# Running the OSR test problems (tests/ in the Integration tree) against the rules.

"""
    read_osr(n; free = true) -> Sym

The SymJ value of an OSR expression, as found in a test problem: names not bound are
symbols, and `x` is the integration variable.
"""
read_osr(n; free::Bool = true) = _s(ev(n, Ctx(Dict{Symbol,Any}(), 0, free)))

# d/dx r == f, numerically at a few points: parameters and x distinct rationals n/997 in
# (0.3, 1.7), so not 1 or each other, where integrands are often singular. A point where
# either side is infinite or can't be evaluated is a singularity, not a disagreement, and
# is replaced. The points depend only on f, so a problem gets the same verdict every run.
#
# ₂F₁(a, b; c; z) is not continuous across its branch cut z ≥ 1, where the derivative
# identities an answer rests on fail, so points that put a ₂F₁ argument there are
# replaced too. Values are positive, as fractional powers then have their real values,
# until a point puts a ₂F₁ on its cut; then they have either sign, as an argument such
# as b x/a + 1 is above 1 for all positive values.
function _verify(r::Sym, f::Sym; points = 3)
    d = diff(r, X) - f
    syms = sort!(collect(SymJ.free_symbols(d) ∪ SymJ.free_symbols(f) ∪ Set([X])); by = string)
    rng = Random.Xoshiro(hash(string(f)))
    zs = _hyp_args!(Sym[], r)
    good, signed = 0, false
    for _ in 1:(isempty(zs) ? 4 : 12) * points
        vs = Random.randperm(rng, 1400)[1:length(syms)] .+ 299
        ps = [s => Sym((signed && rand(rng, Bool) ? -v : v) // 997) for (s, v) in zip(syms, vs) if v != 997]
        length(ps) == length(syms) || continue
        any(z -> _on_cut(z, ps), zs) && (signed = true; continue)
        dv = try N(subs(d, ps...)) catch; continue end
        fv = try N(subs(f, ps...)) catch; continue end
        dv isa Number && fv isa Number || return false
        isfinite(dv) && isfinite(fv) || continue
        abs(dv) <= 1e-8 * (1 + abs(fv)) || return false
        (good += 1) == points && return true
    end
    false
end

# the last arguments (z) of the ₂F₁s in e
function _hyp_args!(out, e::Sym)
    e.kind == SymJ.FN && e.name === :_₂F₁ && push!(out, e.args[end])
    foreach(a -> _hyp_args!(out, a), e.args)
    foreach(a -> _hyp_args!(out, a), e.exps)
    out
end

# z at the point ps is on ₂F₁'s branch cut, [1, ∞), or can't be evaluated
function _on_cut(z::Sym, ps)
    v = try N(subs(z, ps...)) catch; return true end
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
        rel = relpath(joinpath(d, f), root)
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
    oldR, oldT, oldD = _RULESET[], _TRACE[], _DEADLINE[]
    _RULESET[], _TRACE[], _DEADLINE[] = rules, nothing, time() + timeout
    r = try
        _int(u, 0)
    catch err
        err isa InterruptException && rethrow()
        err isa TimedOut && return (:timeout, u, nothing)
        err isa GiveUp ? nothing : return (:error, u, sprint(showerror, err)[1:min(end, 200)])
    finally
        _RULESET[], _TRACE[], _DEADLINE[] = oldR, oldT, oldD
    end
    (r === nothing || _has_int(r)) && return (:unevaluated, u, r)
    ok = try _verify(r, u) catch; false end
    (ok ? :verified : :wrong, u, r)
end

# Running the OSR test problems (tests/ in the Integration tree) against the rules.

"""
    read_osr(n; free = true) -> Sym

The SymJ value of an OSR expression, as found in a test problem: names not bound are
symbols, and `x` is the integration variable.
"""
read_osr(n; free::Bool = true) = _s(ev(n, Ctx(Dict{Symbol,Any}(), 0, free)))

# d/dx r == f, numerically at a few points (parameters and x in (0.3, 1.7))
function _verify(r::Sym, f::Sym; points = 3)
    d = diff(r, X) - f
    syms = collect(SymJ.free_symbols(d) ∪ SymJ.free_symbols(f) ∪ Set([X]))
    for _ in 1:points
        ps = [s => Sym(rand(3:17) // 10) for s in syms]
        dv = try N(subs(d, ps...)) catch; return false end
        fv = try N(subs(f, ps...)) catch; 1.0 end
        dv isa Number && fv isa Number || return false
        abs(dv) <= 1e-8 * (1 + abs(fv)) || return false
    end
    true
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

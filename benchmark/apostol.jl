# How many of the Apostol problems (benchmark/apostol_problems.jl) SymJOSR integrates.
#
#     julia --project=. benchmark/apostol.jl [timeout_seconds] [results.tsv]
#
# Each problem is integrated with the RUBI rules within the timeout (default 5 s) and
# sorted as in `test_problems`: :verified (the answer's derivative is the integrand at
# several points), :wrong, :unevaluated, :timeout, :error. Prints the counts, and the
# problems that are not verified; with a file name, writes one line per problem
# (index, status, seconds, integrand, answer). RischIntegrate.jl's own test counts a
# problem as done when its integrate returns without an error (163 of 175 required);
# here an answer has to be verified.

using SymJ, SymJOSR      # (SymJ first: see test/runtests.jl)
const S = SymJOSR

include(joinpath(@__DIR__, "apostol_problems.jl"))

timeout = length(ARGS) >= 1 ? parse(Float64, ARGS[1]) : 5.0
out = length(ARGS) >= 2 ? ARGS[2] : nothing

R = S.load_rules()
S._check(S.X^2, R, 60.0)                # compile before timing

results = map(enumerate(APOSTOL)) do (i, (f, v))
    u = subs(S._s(f), v => S.X)
    t = time()
    st, _, r = S._check(u, R, timeout)
    (i = i, status = st, seconds = time() - t, integrand = f, var = v,
     result = r isa Sym ? subs(r, S.X => v) : r)
end

counts = Dict(s => count(r -> r.status === s, results) for s in (:verified, :wrong, :unevaluated, :timeout, :error))
n = length(results)
println("Apostol problems: ", counts[:verified], " of ", n, " verified (",
        round(100 * counts[:verified] / n, digits = 1), "%); ",
        join(("$(counts[s]) $s" for s in (:wrong, :unevaluated, :timeout, :error) if counts[s] > 0), ", "),
        "; ", round(sum(r.seconds for r in results), digits = 1), " s")
for r in results
    r.status === :verified && continue
    println(lpad(r.i, 4), "  ", rpad(string(r.status), 12), "∫ ", r.integrand, " d", r.var)
end
if out !== nothing
    open(out, "w") do io
        for r in results
            println(io, r.i, "\t", r.status, "\t", round(r.seconds, digits = 3), "\t", r.integrand, "\t", r.var, "\t", r.result)
        end
    end
end

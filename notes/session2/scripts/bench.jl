# usage: julia --project=. bench.jl OUTFILE [filefilter] [nmax]
using SymJ, SymJOSR, JSON
const S = SymJOSR
out = ARGS[1]
filt = length(ARGS) >= 2 ? ARGS[2] : "1.1.1.2-"
nmax = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : typemax(Int)
t0 = time(); R = S.load_rules(); println("load: ", round(time() - t0, digits = 2), " s, ", R)
root = joinpath(S.rules_dir(), "tests")
probs = []
for (d, _, fs) in walkdir(root), f in sort(fs)
    endswith(f, ".json") && occursin(filt, f) || continue
    for t in JSON.parsefile(joinpath(d, f))["tests"]
        t["variable"] == "x" && push!(probs, (f, t["id"], t["expression"]))
    end
end
probs = probs[1:min(end, nmax)]
if haskey(ENV, "IDS")
    ids = Set(parse.(Int, readlines(ENV["IDS"])))
    filter!(p -> p[2] in ids, probs)
end
S._run_problem(probs[1][3], R, 30.0)   # warm up
counts = Dict{Symbol,Int}()
T = time()
open(out, "w") do io
    for (f, id, e) in probs
        t = time()
        st, u, r = S._run_problem(e, R, 5.0)
        dt = time() - t
        counts[st] = get(counts, st, 0) + 1
        println(io, f, "\t", id, "\t", st, "\t", round(dt, digits = 4), "\t", r)
    end
end
println("total: ", round(time() - T, digits = 1), " s for ", length(probs), " problems; ", counts)

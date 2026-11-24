# resumable survey: appends to OUT, skips problems already in OUT or HANG, writes the
# problem about to run to PROG (for the watchdog)
using SymJ, SymJOSR, JSON, Random
const S = SymJOSR
out, hang, prog = ARGS[1], ARGS[2], ARGS[3]
k, tmo = 40, 3.0
done = Set{Tuple{String,Int}}()
for f in (out, hang), l in (isfile(f) ? eachline(f) : String[])
    p = split(l, '\t'); length(p) >= 2 && push!(done, (p[1], parse(Int, p[2])))
end
R = S.load_rules()
root = joinpath(S.rules_dir(), "tests")
files = sort([S._relpath(joinpath(d, f), root) for (d, _, fs) in walkdir(root) for f in fs if endswith(f, ".json") && f != "meta.json"])
S._run_problem(Any["Power", "x", 2], R, 30.0)
open(out, "a") do io
    for rel in files
        ts = try JSON.parsefile(joinpath(root, rel))["tests"] catch; continue end
        ts = filter(t -> get(t, "variable", "") == "x", ts)
        isempty(ts) && continue
        rng = Random.Xoshiro(hash(rel))
        pick = length(ts) <= k ? ts : ts[sort(Random.randperm(rng, length(ts))[1:k])]
        for t in pick
            (rel, t["id"]) in done && continue
            write(prog, string(rel, "\t", t["id"]))
            t0 = time()
            st, u, r = S._run_problem(t["expression"], R, tmo)
            println(io, rel, "\t", t["id"], "\t", st, "\t", round(time() - t0, digits = 3))
            flush(io)
        end
    end
end
write(prog, "DONE")

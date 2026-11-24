# for each timeout problem: rules fired (from DEBUG output), max depth, top rules
using SymJ, SymJOSR, JSON
const S = SymJOSR
R = S.load_rules()
file = first(joinpath(d, x) for (d, _, fs) in walkdir(joinpath(S.rules_dir(), "tests")) for x in fs if occursin("1.1.1.2-", x))
ts = Dict(t["id"] => t for t in JSON.parsefile(file)["tests"])
ids = parse.(Int, readlines(ARGS[1]))
S._run_problem(ts[ids[1]]["expression"], R, 3.0)
S.DEBUG[] = true
open(ARGS[2], "w") do out
    for id in ids
        t = time()
        tmp = ARGS[2] * ".tmp"
        status = open(tmp, "w") do io
            redirect_stdout(io) do
                try first(S._run_problem(ts[id]["expression"], R, 3.0)) catch e; :err end
            end
        end
        txt = read(tmp, String)
        dt = time() - t
        lines = filter(!isempty, split(txt, '\n'))
        deps = [parse(Int, match(r"\[(\d+)\]", l)[1]) for l in lines if occursin(r"\[\d+\]", l)]
        rules = [strip(replace(l, r"^\s*\[\d+\]\s*" => "")) for l in lines]
        cnt = Dict{String,Int}(); foreach(r -> cnt[r] = get(cnt, r, 0) + 1, rules)
        top = sort(collect(cnt); by = last, rev = true)[1:min(end, 3)]
        println(out, id, "\t", status, "\t", round(dt, digits = 1), "\t", length(rules), "\t",
            isempty(deps) ? 0 : maximum(deps), "\t", join(["$(replace(k, r"^.*/" => "")):$v" for (k, v) in top], " | "))
        flush(out)
    end
end

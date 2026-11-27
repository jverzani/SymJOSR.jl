# For RischIntegrate results that are not a single Sym (piecewise in parameters, RootSum):
# verify each branch; prints file, id, kind, nbranches, nverified, leafcount(sum), ops(sum)
using SymJ, SymJOSR, RischIntegrate, JSON; const S = SymJOSR
const root = joinpath(S.rules_dir(), "tests"); const X = S.X
const cache = Dict{String,Dict{Int,Any}}()
tests(f) = get!(() -> Dict(t["id"] => t for t in JSON.parsefile(joinpath(root, f))["tests"]), cache, f)
ops(r) = (s = string(r); count(c -> c in "+-*/^", s) + count(m -> true, eachmatch(r"[A-Za-z_][A-Za-z_0-9₀-₉]*\(", s)))
ver(r, u) = r isa Sym && (try S._verify(r, u) catch; false end)
for line in eachline(ARGS[1])
    f, id = split(line, '\t'); u = S.read_osr(tests(f)[parse(Int, id)]["expression"])
    r = try RischIntegrate.integrate(u, X) catch; nothing end
    bs = r isa AbstractVector ? [p.second for p in r] : [r]
    kind = r isa AbstractVector ? "piecewise" : "other"
    nv = count(b -> ver(b, u), bs)
    lc = sum(b -> b isa Sym ? S.leafcount(b) : 0, bs); o = sum(ops, bs)
    println("$f\t$id\t$kind\t$(length(bs))\t$nv\t$lc\t$o"); flush(stdout)
end

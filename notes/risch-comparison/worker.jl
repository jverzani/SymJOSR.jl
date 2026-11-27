# Reads "file<TAB>id" lines; for each prints START, then an OSR line and a RISCH line:
# sys, file, id, status, seconds, leafcount, ops, answer
using SymJ, SymJOSR, RischIntegrate, JSON; const S = SymJOSR
const R = S.load_rules()
const root = joinpath(S.rules_dir(), "tests")
const X = S.X
const cache = Dict{String,Dict{Int,Any}}()
tests(f) = get!(() -> Dict(t["id"] => t for t in JSON.parsefile(joinpath(root, f))["tests"]), cache, f)
ops(r) = (s = string(r); count(c -> c in "+-*/^", s) + count(m -> true, eachmatch(r"[A-Za-z_][A-Za-z_0-9₀-₉]*\(", s)))
size(r) = r isa Sym ? (S.leafcount(r), ops(r)) : (0, 0)
clean(s) = replace(string(s), '\t' => ' ', '\n' => ' ')
function risch(u)
    r = try RischIntegrate.integrate(u, X) catch e
        return (:unevaluated, first(clean(sprint(showerror, e)), 80))
    end
    r isa Sym || return (:unevaluated, clean(r))
    occursin(r"integrate|Integral|∫", string(r)) && return (:unevaluated, clean(r))
    ok = try S._verify(r, u) catch; false end
    (ok ? :verified : :wrong, r)
end
# warm both up
S._check(X^2 * exp(X), R, 30.0); risch(X^2 * exp(X)); S._verify(X^3, 3X^2)
println("READY"); flush(stdout)
for line in eachline(stdin)
    f, id = split(line, '\t'); id = parse(Int, id)
    u = try S.read_osr(tests(f)[id]["expression"]) catch; nothing end
    println("START\t$f\t$id"); flush(stdout)
    if u === nothing
        println("OSR\t$f\t$id\terror\t0\t0\t0\tunreadable"); println("RISCH\t$f\t$id\terror\t0\t0\t0\tunreadable"); flush(stdout); continue
    end
    t = time(); st, _, r = S._check(u, R, 60.0); dt = time() - t
    ans = st === :verified || st === :wrong ? S._tidy_result(r) : r
    l, o = size(ans)
    println("OSR\t$f\t$id\t$st\t$(round(dt, digits = 3))\t$l\t$o\t$(clean(ans))"); flush(stdout)
    t = time(); st, r = risch(u); dt = time() - t
    l, o = size(r)
    println("RISCH\t$f\t$id\t$st\t$(round(dt, digits = 3))\t$l\t$o\t$(clean(r))"); flush(stdout)
end

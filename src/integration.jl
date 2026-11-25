# The RUBI rule set as SymJ rules, and integration with it.

struct OSRRule
    file::String          # the rule file, relative to rules/
    id::Int
    rule::SymJ.Rule       # the SymJ rule: pattern, then guards and result in its right side
    pattern::Any          # the OSR pattern, constraints and result, as read
    constraints::Any
    result::Any
end
Base.show(io::IO, r::OSRRule) = print(io, "OSRRule(", r.file, " #", r.id, ")")

struct RuleSet
    rules::Vector{OSRRule}
    skipped::Vector{NamedTuple{(:file, :id, :reason),Tuple{String,Int,String}}}
    missing::Dict{String,Int}     # unsupported head or name => number of rules it stops
    source::Any
end
Base.show(io::IO, R::RuleSet) =
    print(io, "RuleSet(", length(R.rules), " rules loaded, ", length(R.skipped), " skipped)")

const _RULESETS = Dict{Any,RuleSet}()

# ---- the depth of Int[...] recursion, and the trace of rules applied

const MAXDEPTH = Ref(50)
const DEBUG = Ref(false)      # print each rule as it fires
const _TRACE = Ref{Union{Nothing,Vector{OSRRule}}}(nothing)

# ---- reading a rule

function _slotnames!(out, n)
    if n isa AbstractString
        w = wildcard(n)
        w === nothing || push!(out, string(w[1]))
    elseif n isa AbstractVector
        foreach(a -> _slotnames!(out, a), n)
    end
    out
end

# the heads and names in constraints and result that have no meaning here
function _unknown!(out, n, slots)
    if n isa AbstractString
        n == "x" || n in slots || haskey(ATOMS, n) || haskey(FUNCS, n) || push!(out, n)
    elseif isapp(n) && head(n) == "MatchQ" && length(n) == 3
        # MatchQ[u, pattern] or MatchQ[u, Condition[pattern, test]]: the pattern's names
        # are bound in the test; a pattern that can't be translated is unsupported
        _unknown!(out, n[2], slots)
        p, test = _matchq_parts(n[3])
        outer = _outer_names!(String[], p)
        foreach(nm -> _unknown!(out, nm, slots), outer)          # bound by the rule
        try
            SymJ.pattern(pat(_with_values(p, Dict{String,Any}(nm => Sym(Symbol(nm)) for nm in outer))))
        catch err
            err isa InterruptException && rethrow()
            push!(out, "MatchQ pattern: " * first(sprint(showerror, err), 60))
            return out
        end
        test === nothing || _unknown!(out, test, union(slots, _slotnames!(Set{String}(), p)))
    elseif isapp(n) && head(n) in ("With", "Module") && length(n) == 3
        # With[{v = e, …}, body]: the values see the rule's names, the body also the locals
        bs = try
            _local_bindings(n[2], head(n) == "Module")
        catch err
            err isa OSRError || rethrow()
            push!(out, err.msg)
            return out
        end
        foreach(((_, e),) -> e === nothing || _unknown!(out, e, slots), bs)
        _unknown!(out, n[3], union(slots, first.(bs)))
    elseif isapp(n) && head(n) == "Sum" && length(n) == 3 && isapp(n[3]) && length(n[3]) == 4 && n[3][2] isa AbstractString
        # Sum[u, {k, lo, hi}]: k is bound in u
        foreach(a -> _unknown!(out, a, slots), n[3][3:4])
        _unknown!(out, n[2], union(slots, [n[3][2]]))
    elseif isapp(n)
        h = head(n)
        haskey(FUNCS, h) || haskey(SPECIAL, h) || h in slots || push!(out, h)
        foreach(a -> _unknown!(out, a, slots), args(n))
    elseif n isa AbstractVector
        foreach(a -> _unknown!(out, a, slots), n)
    end
    out
end

function _mkrule(file, r)
    p = r["pattern"]
    (isapp(p) && head(p) == "Int" && length(p) == 3) || throw(OSRError("pattern is not Int[u, x]"))
    slots = _slotnames!(Set{String}(), p)
    unk = _unknown!(Set{String}(), r["constraints"], slots)
    _unknown!(unk, r["result"], slots)
    isempty(unk) || return unk
    pe = pat(p[2])
    cons, res = r["constraints"], r["result"]
    holder = Ref{OSRRule}()
    rhs = function (d)
        c = Ctx(d, _DEPTH[])
        guards_hold(cons, c) || return nothing
        DEBUG[] && println("  "^_DEPTH[], "[", _DEPTH[], "] ", holder[].file, " #", holder[].id)
        v = try
            ev(res, c)
        catch err
            (err isa GiveUp || err isa TimedOut) && rethrow()
            err isa InterruptException && rethrow()
            return nothing
        end
        v isa Sym || v isa Number || return nothing
        t = _TRACE[]
        t === nothing || push!(t, holder[])
        v
    end
    sr = SymJ.rule(pe => rhs)
    holder[] = OSRRule(file, r["id"], sr, p, cons, res)
end

# RUBI's load order. The rule files are tried in this order, and a rule's priority is its
# place in it: Rubi.m's order is not section order (1.4.1, which integrates sums term by
# term, comes after 1.1-1.3), and some files in the OSR tree are not loaded by RUBI 4.16.1.
const RUBI_LOAD_ORDER = filter!(l -> !isempty(l) && !startswith(l, '#'),
    readlines(joinpath(@__DIR__, "rubi_load_order.txt")))

# a path relative to root with / as separator on every system: rule files are named
# this way (HOST_RULES, the `files` filters), and relpath gives \ on Windows
_relpath(p, root) = replace(relpath(p, root), '\\' => '/')

"""
    rule_files(dir = rules_dir()) -> Vector{String}

The rule files, relative to `rules/`, in RUBI's load order. A file of RUBI's that the
OSR tree does not have is left out with a warning.
"""
function rule_files(dir = rules_dir())
    root = joinpath(dir, "rules")
    bybase = Dict{String,String}()
    for (d, _, fs) in walkdir(root), f in fs
        endswith(f, ".json") && f != "meta.json" && (bybase[f[1:end-5]] = _relpath(joinpath(d, f), root))
    end
    out = String[]
    for n in RUBI_LOAD_ORDER
        f = get(bybase, replace(n, ' ' => '-'), nothing)
        f === nothing ? @warn("SymJOSR: RUBI rule file $n is not in the OSR tree") : push!(out, f)
    end
    out
end

"""
    load_rules(; files = nothing, reload = false) -> RuleSet

The RUBI rules of the OpenSymbolicRules Integration data (see [`rules_dir`](@ref)), in
RUBI's load order, as SymJ rules. `files`, if given, keeps the rule files whose path
(relative to `rules/`) contains one of the strings, e.g. `files = ["1.1.1-linear"]`.
Rules that use a predicate, utility or function not yet supported are skipped; the
`skipped` and `missing` fields of the result say which and why.
"""
function load_rules(; files = nothing, reload::Bool = false)
    dir = rules_dir()
    key = (dir, files === nothing ? nothing : Tuple(files))
    reload || haskey(_RULESETS, key) && return _RULESETS[key]
    order = rule_files(dir)
    files === nothing || filter!(f -> any(s -> occursin(s, f), files), order)
    rules, skipped, missing = OSRRule[], NamedTuple{(:file, :id, :reason),Tuple{String,Int,String}}[], Dict{String,Int}()
    for f in order
        data = JSON.parsefile(joinpath(dir, "rules", f))
        rs = data["rules"]
        isempty(rs) && haskey(HOST_RULES, f) && (rs = HOST_RULES[f])
        if haskey(HOST_MISSING, f)
            have = JSON.json(rs)
            extra = [r for r in HOST_MISSING[f] if !occursin("\"" * r["head"] * "\"", have)]
            rs = vcat([r for r in extra if get(r, "at", "start") != "end"], rs,
                      [r for r in extra if get(r, "at", "start") == "end"])
        end
        for r in rs
            fix = get(RULE_FIXES, (f, r["id"]), nothing)
            if fix !== nothing && occursin(fix[1], JSON.json(r["result"]))
                r = merge(r, Dict("result" => JSON.parse(replace(JSON.json(r["result"]), fix[1] => fix[2]))))
            end
            x = try
                _mkrule(f, r)
            catch err
                err isa InterruptException && rethrow()
                msg = err isa OSRError ? err.msg : sprint(showerror, err)
                (msg = first(split(msg, '\n')); missing[msg] = get(missing, msg, 0) + 1)
                push!(skipped, (file = f, id = r["id"], reason = msg))
                continue
            end
            if x isa OSRRule
                push!(rules, x)
            else
                for h in x
                    missing[h] = get(missing, h, 0) + 1
                end
                push!(skipped, (file = f, id = r["id"], reason = "unsupported: " * join(sort!(collect(x)), ", ")))
            end
        end
    end
    _RULESETS[key] = RuleSet(rules, skipped, missing, rules_version())
end

"""
    unsupported_heads(R::RuleSet = load_rules())

The heads and names that keep rules from loading, most frequent first, with the number
of rules each one stops (a rule can be stopped by several).
"""
unsupported_heads(R::RuleSet = load_rules()) = sort!(collect(R.missing); by = last, rev = true)

# ---- integration

const _DEPTH = Ref(0)
const _RULESET = Ref{Union{Nothing,RuleSet}}(nothing)

# an unevaluated integral
_inert_int(u) = apply_function(:Int, Sym[u, X])

struct TimedOut <: Exception end
const _DEADLINE = Ref(Inf)

# The integrands being integrated, outermost first. A step that comes back to one of
# them made no progress (RUBI's rules never do that, but approximations such as our
# ExpandIntegrand can hand an integrand back unchanged), so it fails with Cycle, and the
# rule whose result needed it is rejected: the next rule is tried.
struct Cycle <: Exception end
const _STACK = Sym[]

function _int(u::Sym, depth::Int)
    depth > MAXDEPTH[] && throw(GiveUp(u))
    time() > _DEADLINE[] && throw(TimedOut())
    # constant factors outside: Int[a*u] = a*Int[u]. RUBI's results keep them outside
    # (Star[a, Int[u, x]]), so its rules never see one; SymJ's canonical form puts them
    # back in, where rules such as 1.1.3.7 #1 (Pq = a) rewrite the integrand to itself.
    if u.kind == SymJ.MUL
        c = FUNCS["FreeFactors"](u, X)
        isone(c) || return c * _int(FUNCS["NonfreeFactors"](u, X), depth)
    end
    # a constant integrand: Int[a, x] = a*x. RUBI's rule for it is in the older "9.1
    # Integrand simplification rules", which its load order leaves out.
    SymJ.has(u, X) || return u * X
    any(v -> isequal(v, u), _STACK) && throw(Cycle())
    R = _RULESET[]::RuleSet
    old = _DEPTH[]
    _DEPTH[] = depth
    push!(_STACK, u)
    try
        for r in R.rules
            v = r.rule(u)
            v === nothing || return _s(v)
        end
    finally
        _DEPTH[] = old
        pop!(_STACK)
    end
    _inert_int(u)
end

"""
    integrate(f, x; rules = load_rules(), trace = false)

An antiderivative of `f` in `x` by the RUBI rules, or `nothing` when they do not give
one. With `trace = true`, a named tuple of the result and the rules applied, in order.
"""
function integrate(f, x::Sym; rules::RuleSet = load_rules(), trace::Bool = false)
    g = subs(_s(f), x => X)
    oldR, oldT = _RULESET[], _TRACE[]
    _RULESET[] = rules
    steps = OSRRule[]
    _TRACE[] = trace ? steps : nothing
    v = try
        _int(g, 0)
    catch err
        err isa GiveUp || err isa Cycle || rethrow()
        nothing
    finally
        _RULESET[], _TRACE[] = oldR, oldT
    end
    v = v === nothing || _has_int(v) ? nothing : subs(_tidy_result(v), X => x)
    trace ? (result = v, steps = steps) : v
end

_has_int(e::Sym) = (e.kind == SymJ.FN && e.name === :Int) || any(_has_int, e.args) || any(_has_int, e.exps)

# an answer as it is shown: trig functions of v + π/2 and of imaginary arguments back as
# those of v and hyperbolic ones, and i's multiplied out
function _tidy_result(v)
    w = _log_exp(_activate_hyperbolic(_unshift(v)))
    _has_imaginary(w) ? expand(w) : w
end

# log(e^w) as w, w linear in x: the same up to a constant (2πik), so in an antiderivative
# (RUBI's answers have x where the substitution v = e^x leaves log(e^x))
function _log_exp(u)
    u isa Sym || return u
    isempty(u.args) && return u
    if u.kind == SymJ.FN && u.name === :log && length(u.args) == 1
        a = u.args[1]
        a.kind == SymJ.POW && isequal(a.args[1], SymJ.E) && FUNCS["LinearQ"](a.args[2], X) && return a.args[2]
    end
    SymJ._rw_parts(_log_exp, u)
end

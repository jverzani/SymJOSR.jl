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

"""
    rule_files(dir = rules_dir()) -> Vector{String}

The rule files, relative to `rules/`, in RUBI's load order. A file of RUBI's that the
OSR tree does not have is left out with a warning.
"""
function rule_files(dir = rules_dir())
    root = joinpath(dir, "rules")
    bybase = Dict{String,String}()
    for (d, _, fs) in walkdir(root), f in fs
        endswith(f, ".json") && f != "meta.json" && (bybase[f[1:end-5]] = relpath(joinpath(d, f), root))
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
        for r in rs
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

function _int(u::Sym, depth::Int)
    depth > MAXDEPTH[] && throw(GiveUp(u))
    time() > _DEADLINE[] && throw(TimedOut())
    R = _RULESET[]::RuleSet
    old = _DEPTH[]
    _DEPTH[] = depth
    try
        for r in R.rules
            v = r.rule(u)
            v === nothing || return _s(v)
        end
    finally
        _DEPTH[] = old
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
        err isa GiveUp || rethrow()
        nothing
    finally
        _RULESET[], _TRACE[] = oldR, oldT
    end
    v = v === nothing || _has_int(v) ? nothing : subs(v, X => x)
    trace ? (result = v, steps = steps) : v
end

_has_int(e::Sym) = (e.kind == SymJ.FN && e.name === :Int) || any(_has_int, e.args) || any(_has_int, e.exps)

# OSR's errata: corrections to RUBI's rules, published beside the rule files.
#
# OSR keeps `rules/` exactly as converted from RUBI's source. A rule that is wrong there,
# or one that OSR omitted and has since qualified with extra guards, is listed in
# `docs/rubi-errata.json` instead (the records for the compatibility profile we load;
# `editions/` has its own). Each record names a rule file by its `identity` and a rule
# by its local ID, and is one of:
#
# - `replace`: the shipped rule whose canonical payload has SHA-256 `payload_sha256` is
#   to be used with the `replacement` constraints, pattern and result;
# - `enable`: `rule` (digest `rule_sha256`) is added with ID `rule_id`, just before the
#   shipped rule `insert_before`.
#
# A record whose digest does not match the shipped rule (OSR has changed the rule since)
# is not applied, with a warning: the record needs review, and the shipped rule is kept.

using SHA: sha256

"""
    errata(dir = rules_dir()) -> Vector

The errata records of the OSR data in `dir` (`docs/rubi-errata.json`), or an empty list
when it has none.
"""
function errata(dir = rules_dir())
    f = joinpath(dir, "docs", "rubi-errata.json")
    isfile(f) || return Any[]
    collect(JSON.parsefile(f))
end

# Python's json.dumps(v, ensure_ascii=False, separators=(",", ":"), sort_keys=True), as
# OSR's canonical_payload (scripts/check_duplicate_rules.py) writes it
_canonical(v) = sprint(_canonical, v)
function _canonical(io::IO, v::AbstractDict)
    print(io, '{')
    for (i, k) in enumerate(sort!(collect(String, keys(v))))
        i > 1 && print(io, ',')
        _canonical(io, k)
        print(io, ':')
        _canonical(io, v[k])
    end
    print(io, '}')
end
function _canonical(io::IO, v::AbstractVector)
    print(io, '[')
    for (i, a) in enumerate(v)
        i > 1 && print(io, ',')
        _canonical(io, a)
    end
    print(io, ']')
end
function _canonical(io::IO, s::AbstractString)
    print(io, '"')
    for c in s
        c == '"' ? print(io, "\\\"") : c == '\\' ? print(io, "\\\\") :
        c == '\n' ? print(io, "\\n") : c == '\r' ? print(io, "\\r") : c == '\t' ? print(io, "\\t") :
        c == '\b' ? print(io, "\\b") : c == '\f' ? print(io, "\\f") :
        c < ' ' ? print(io, "\\u", string(UInt32(c); base = 16, pad = 4)) : print(io, c)
    end
    print(io, '"')
end
_canonical(io::IO, v::Bool) = print(io, v ? "true" : "false")
_canonical(io::IO, ::Nothing) = print(io, "null")
_canonical(io::IO, v::Integer) = print(io, v)
# Python's repr for the plain decimals of the rule files (0.5, 2.0); an exponent is
# written differently (1e-05 against 1.0e-5), so such a rule would not match its record
_canonical(io::IO, v::AbstractFloat) = print(io, v)

# the SHA-256, in hex, of a rule's canonical payload: its constraints, pattern and result
_payload_sha(r) = bytes2hex(sha256(_canonical(Dict{String,Any}(
    "constraints" => get(r, "constraints", Any[]),
    "pattern" => get(r, "pattern", nothing),
    "result" => get(r, "result", nothing)))))

# The rules rs of the rule file f (relative to rules/, OSR identity `identity`) with the
# records of recs for it applied, and the records applied, as (file, id, action, issue).
function _apply_errata(rs, f, identity, recs)
    applied = NamedTuple{(:file, :id, :action, :issue),Tuple{String,Int,String,String}}[]
    identity isa AbstractString || return rs, applied
    mine = [e for e in recs if get(e, "file_identity", nothing) == identity]
    isempty(mine) && return rs, applied
    rs = collect(Any, rs)
    note(e) = push!(applied, (file = f, id = e["rule_id"], action = e["action"], issue = get(e, "issue", "")))
    for e in mine
        id, act = e["rule_id"], get(e, "action", "")
        at = findfirst(r -> r["id"] == id, rs)
        if act == "replace"
            new = e["replacement"]
            if at === nothing
                @warn "SymJOSR: erratum for $f #$id: no such rule; not applied"
            elseif _payload_sha(rs[at]) != e["payload_sha256"]
                @warn "SymJOSR: erratum for $f #$id: the rule has changed since the record; shipped rule kept"
            elseif _payload_sha(new) != e["replacement_sha256"]
                @warn "SymJOSR: erratum for $f #$id: replacement digest does not match; not applied"
            else
                rs[at] = merge!(Dict{String,Any}(rs[at]), Dict{String,Any}(k => new[k] for k in ("constraints", "pattern", "result") if haskey(new, k)))
                note(e)
            end
        elseif act == "enable"
            new = e["rule"]
            before = findfirst(r -> r["id"] == e["insert_before"], rs)
            if at !== nothing
                @warn "SymJOSR: erratum for $f #$id: the ID is taken; not applied"
            elseif before === nothing
                @warn "SymJOSR: erratum for $f #$id: no rule #$(e["insert_before"]) to insert before; not applied"
            elseif _payload_sha(new) != e["rule_sha256"]
                @warn "SymJOSR: erratum for $f #$id: rule digest does not match; not applied"
            else
                insert!(rs, before, merge!(Dict{String,Any}(new), Dict{String,Any}("id" => id)))
                note(e)
            end
        else
            @warn "SymJOSR: erratum for $f #$id: unknown action $(repr(act)); not applied"
        end
    end
    rs, applied
end

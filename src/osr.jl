# OSR expressions and their meaning in SymJ.
#
# An OSR expression, as parsed from JSON, is an integer, a string (a name: a variable,
# a wildcard, a constant, or a function name used as a value), or an array. An array
# whose first element is a string is an application [head, args...]; one whose first
# element is not is a list (the constraints of a rule are such a list, read as "all").
#
# The meaning of a head is given by two registries:
#
#   FUNCS[head]   = f(args::Sym...)          arguments evaluated first
#   SPECIAL[head] = f(args::Vector, c::Ctx)   arguments unevaluated (And, If, Int, ...)
#
# so supporting another RUBI predicate or utility is one entry. A rule that uses a head
# in neither registry is not loaded (see `unsupported_heads`).

using SymJ: Sym, apply_function

const FUNCS = Dict{String,Function}()
const SPECIAL = Dict{String,Function}()

"""
    SymJOSR.@osrfunc Name(args...) = body
    SymJOSR.@osrfunc Name = f

Register the meaning of the OSR head `Name` (arguments evaluated first).
"""
macro osrfunc(ex)
    if ex isa Expr && ex.head === :(=) && ex.args[1] isa Symbol
        return esc(:($FUNCS[$(string(ex.args[1]))] = $(ex.args[2])))
    end
    (ex isa Expr && ex.head in (:(=), :function)) || error("@osrfunc: Name(args) = body")
    sig, body = ex.args
    name = sig.args[1]
    esc(:($FUNCS[$(string(name))] = ($(sig.args[2:end]...),) -> $body))
end

# the integration variable inside the rule engine: the user's variable is renamed to it
# before matching, so patterns hold it as a literal and FreeQ[_, x] is a free-of test
const XNAME = :𝓍
const X = Sym(XNAME)

# evaluation context: slot bindings and recursion depth for Int
struct Ctx
    env::Dict{Symbol,Any}
    depth::Int
    free::Bool          # unbound names are symbols (reading test problems), not errors
end
Ctx(env, depth) = Ctx(env, depth, false)

struct OSRError <: Exception
    msg::String
end
Base.showerror(io::IO, e::OSRError) = print(io, "OSRError: ", e.msg)

# constants and names that stand for values
const ATOMS = Dict{String,Any}(
    "Pi" => SymJ.PI, "E" => SymJ.E, "ImaginaryI" => Sym(im), "I" => Sym(im),
    "True" => true, "False" => false, "EulerGamma" => Sym(Base.MathConstants.eulergamma),
    "Infinity" => Sym(Inf), "\$UseGamma" => false,
)

isapp(n) = n isa AbstractVector && !isempty(n) && first(n) isa AbstractString
head(n) = first(n)::AbstractString
args(n) = @view n[2:end]

# the wildcard a string names in a pattern: (name, kind, type) or nothing
#   "a_" one, "a." optional, "a_integer" typed, "F_" head slot when applied
function wildcard(s::AbstractString)
    if endswith(s, ".") && occursin(r"^[A-Za-z]\w*\.$", s)
        return (Symbol(chop(s)), :optional, nothing)
    end
    m = match(r"^([A-Za-z][A-Za-z0-9]*)_([a-z]*)$", s)
    m === nothing && return nothing
    (Symbol(m[1]), :blank, isempty(m[2]) ? nothing : m[2])
end

# ---- evaluation (constraints and results)

ev(n::Bool, c::Ctx) = n
ev(n::Integer, c::Ctx) = Sym(n)
ev(n::AbstractFloat, c::Ctx) = Sym(n)
function ev(n::AbstractString, c::Ctx)
    n == "x" && return X
    v = get(c.env, Symbol(n), nothing)
    v === nothing || return v
    v = get(ATOMS, n, nothing)
    v === nothing || return v
    # reading a test problem: a bare name is a symbol, even one that is also a head (the
    # coefficients A, B, C of a polynomial P(x))
    c.free && return Sym(Symbol(n))
    f = get(FUNCS, n, nothing)          # a function name used as a value (MemberQ[{Sin,…}, F])
    f === nothing || return FuncName(n)
    throw(OSRError("unbound name $n"))
end
function ev(n::AbstractVector, c::Ctx)
    isapp(n) || return Any[ev(a, c) for a in n]
    h = head(n)
    s = get(SPECIAL, h, nothing)
    s === nothing || return s(args(n), c)
    f = get(FUNCS, h, nothing)
    vs = [ev(a, c) for a in args(n)]
    f === nothing || return f(vs...)
    hv = get(c.env, Symbol(h), nothing)  # a head slot's function, F[u]
    hv === nothing || return _applyhead(hv, vs)
    # reading a test problem: an unknown head is an arbitrary function (8.10's f[x], g[x])
    c.free && return apply_function(Symbol(h), Sym[_s(v) for v in vs])
    throw(OSRError("unsupported head $h"))
end

# a function name as a value, and a head slot's binding, applied
struct FuncName
    name::String
end
_applyhead(f::FuncName, vs) = FUNCS[f.name](vs...)
_applyhead(f, vs) = Sym(f(vs...))

# all constraints hold; an error in one (division by zero, an unsupported case) is false
function guards_hold(cs, c::Ctx)
    for g in cs
        ok = try
            truthy(ev(g, c))
        catch err
            (err isa InterruptException || err isa TimedOut || err isa GiveUp) && rethrow()
            false
        end
        ok || return false
    end
    true
end
truthy(b::Bool) = b
truthy(x) = false

# ---- patterns

"""
    to_pattern_expr(n) -> Expr

The SymJ pattern (as a quoted expression for `SymJ.pattern`) of an OSR integrand
pattern. The integration variable, `x_` or `x`, becomes the literal `$XNAME`.
"""
pat(n::Integer) = n
function pat(n::AbstractString)
    w = wildcard(n)
    if w !== nothing
        name, kind, typ = w
        name === :x && return XNAME
        s = kind === :optional ? :(!$name) : name
        typ === nothing || (s = Expr(:(::), s, _typepred(typ)))
        return :(~$s)
    end
    n == "x" && return XNAME
    v = get(ATOMS, n, nothing)
    v isa Sym && return v
    throw(OSRError("pattern: unknown name $n"))
end
function pat(n::AbstractVector)
    isapp(n) || throw(OSRError("pattern: a list"))
    h, as = head(n), [pat(a) for a in args(n)]
    # an optional factor, b. in b.*x, has the default 1, and the term is not optional: in
    # Mathematica a_ + b_.*x_ needs a term in x. SymJ lets the term ~!b*x of a sum be
    # absent with b = 0, so b is required to be nonzero. (Without it, (a + b x)(c + d)/e
    # matched (a + b x)^m (c + d x)^n (e + f x)^p with b = d = 0, and 1.1.1.3 #1 rewrote
    # the integrand to itself.)
    h == "Multiply" && return Expr(:call, :*, (_nonzero_factor(a, x) for (a, x) in zip(args(n), as))...)
    h == "Add" && return Expr(:call, :+, as...)
    h == "Power" && return Expr(:call, :^, as...)
    h == "Rational" && return Expr(:call, ://, as...)
    w = wildcard(h)
    if w !== nothing && w[2] === :blank         # F_[u]: a head slot
        return Expr(:call, :(~$(w[1])), as...)
    end
    f = get(PATTERN_HEADS, h, nothing)
    f === nothing && throw(OSRError("pattern: unsupported head $h"))
    Expr(:call, f, as...)
end

function _nonzero_factor(n, p)
    w = n isa AbstractString ? wildcard(n) : nothing
    (w === nothing || w[2] !== :optional || w[1] === :x) && return p
    :(~(!$(Expr(:(::), w[1], _isnonzero))))           # ~!b::f is ~(!(b::f))
end
_isnonzero(v) = !(v isa Sym && iszero(v))

_typepred(t) =t == "integer" ? _isexactint : t == "rational" ? _isexactrat :
    t == "symbol" ? (v -> v isa Sym && v.kind == SymJ.SYMBOL) :
    throw(OSRError("pattern: unknown wildcard type $t"))

_isexactint(v) = v isa Sym && v.kind == SymJ.NUMBER && SymJ.isexact(v.num) && isinteger(v)
_isexactrat(v) = v isa Sym && v.kind == SymJ.NUMBER && SymJ.isexact(v.num) && isreal(v.num)

# ---- MatchQ[u, pattern] and MatchQ[u, Condition[pattern, test]] in constraints: the
# pattern as a SymJ pattern (compiled once), matched against u; with a Condition, some
# match whose bindings, added to the rule's, make the test true

# A pattern may use a name the rule binds as a literal (MatchQ[v, c_.*(e + f*x)] with the
# rule's e): it is replaced by its value (a Sym literal) before the pattern is compiled,
# and the compiled pattern cached for those values.
const _MATCHQ_PATTERNS = Dict{Any,Any}()
_outer_names!(out, n) = (n isa AbstractString ? (wildcard(n) === nothing && n != "x" && !haskey(ATOMS, n) && push!(out, n)) :
    n isa AbstractVector && foreach(a -> _outer_names!(out, a), isapp(n) ? args(n) : n); out)
_with_values(n, vals) = n isa AbstractString ? get(vals, n, n) :
    n isa AbstractVector ? (isapp(n) ? Any[head(n); [_with_values(a, vals) for a in args(n)]] : Any[_with_values(a, vals) for a in n]) : n
function _matchq_pattern(p, vals = Dict{String,Any}())
    key = (objectid(p), Tuple(sort!([(k, string(v)) for (k, v) in vals])))
    get!(() -> SymJ.pattern(pat(_with_values(p, vals))), _MATCHQ_PATTERNS, key)
end
pat(n::Sym) = n

function _matchq_parts(spec)
    isapp(spec) && head(spec) == "Condition" ? (spec[2], spec[3]) : (spec, nothing)
end

SPECIAL["MatchQ"] = function (as, c::Ctx)
    u = ev(as[1], c)
    u isa Sym || (u = try Sym(u) catch; return false end)
    p, test = _matchq_parts(as[2])
    names = _outer_names!(String[], p)
    P = _matchq_pattern(p, Dict{String,Any}(n => _s(ev(n, c)) for n in names))
    for m in eachmatch(P, u)
        test === nothing && return true
        env = merge(c.env, Dict{Symbol,Any}(k => v for (k, v) in m))
        guards_hold(Any[test], Ctx(env, c.depth, c.free)) && return true
    end
    false
end

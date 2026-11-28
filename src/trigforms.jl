# Mathematica's automatic forms of products of trig (and hyperbolic) functions of one
# argument. Mathematica evaluates 1/Csc[x] to Sin[x], 1/Sin[x]^2 to Csc[x]^2, Csc[x] Sin[x]^2
# to Sin[x], Cos[x] Tan[x] to Sin[x] and Sin[x]/Cos[x] to Tan[x] before any rule sees them,
# and RUBI's rules are written for those forms; SymJ keeps such products as they are, where
# no rule's pattern fits them (4.5.0 #138, ∫ 1/csc(x)). Here, for each argument, the integer
# powers of its six functions are summed as sin^A cos^B and written in Mathematica's form:
#   sin^A cos^B (A, B ≥ 0), csc^-A sec^-B (A, B ≤ 0),
#   tan^p sec^(q-p) or tan^q sin^(p-q) for sin^p cos^-q (p ≤ q or p > q),
#   cot^p csc^(q-p) or cot^q cos^(p-q) for cos^p sin^-q.

# (sin, cos) exponents of each function, and the names of the family
const _TRIG_SC = Dict(:sin => (1, 0), :cos => (0, 1), :tan => (1, -1), :cot => (-1, 1), :sec => (0, -1), :csc => (-1, 0),
                      :sinh => (1, 0), :cosh => (0, 1), :tanh => (1, -1), :coth => (-1, 1), :sech => (0, -1), :csch => (-1, 0))
const _TRIG_NAMES = (sin = :sin, cos = :cos, tan = :tan, cot = :cot, sec = :sec, csc = :csc)
const _HYP_NAMES = (sin = :sinh, cos = :cosh, tan = :tanh, cot = :coth, sec = :sech, csc = :csch)
_hyperbolic_name(n::Symbol) = n in (:sinh, :cosh, :tanh, :coth, :sech, :csch)

# sin^A cos^B of v in Mathematica's form, with the names N of a family
function _trig_form(A::Int, B::Int, v::Sym, N)
    f(n, k) = k == 0 ? SymJ.ONE : apply_function(n, Sym[v])^k
    A >= 0 && B >= 0 && return f(N.sin, A) * f(N.cos, B)
    A <= 0 && B <= 0 && return f(N.csc, -A) * f(N.sec, -B)
    if A > 0                                      # sin^p cos^-q
        p, q = A, -B
        return p <= q ? f(N.tan, p) * f(N.sec, q - p) : f(N.tan, q) * f(N.sin, p - q)
    end
    p, q = B, -A                                  # cos^p sin^-q
    p <= q ? f(N.cot, p) * f(N.csc, q - p) : f(N.cot, q) * f(N.cos, p - q)
end

# the trig factor f(v)^k of a product (k an integer), as (family, v, (a, b)), or nothing
function _trig_factor(b::Sym, e::Sym)
    (b.kind == SymJ.FN && haskey(_TRIG_SC, b.name) && length(b.args) == 1 && _isinteger(e)) || return nothing
    k = Int(_rat(e))
    s, c = _TRIG_SC[b.name]
    (_hyperbolic_name(b.name), b.args[1], (k * s, k * c))
end

# u with each product of trig or hyperbolic functions in Mathematica's form
function _trig_canonical(u::Sym)
    isempty(u.args) && return u
    if u.kind == SymJ.MUL || u.kind == SymJ.POW
        bs, es = u.kind == SymJ.MUL ? (u.args, u.exps) : ([u.args[1]], [u.args[2]])
        groups = Dict{Tuple{Bool,Sym},Vector{Int}}()     # (hyperbolic, argument) => [A, B, count, negative]
        rest = u.kind == SymJ.MUL ? Sym(u.num) : SymJ.ONE
        for (b, e) in zip(bs, es)
            t = _trig_factor(b, e)
            if t === nothing
                rest *= _trig_canonical(b)^_trig_canonical(e)
                continue
            end
            h, v, (a, c) = t
            g = get!(groups, (h, _trig_canonical(v)), [0, 0, 0, 0])
            g[1] += a; g[2] += c; g[3] += 1; g[4] |= _rat(e) < 0
        end
        # unchanged unless two functions of one argument meet, or one has a negative power
        any(g -> g[3] > 1 || g[4] == 1, values(groups)) || return SymJ._rw_parts(_trig_canonical, u)
        for ((h, v), g) in groups
            rest *= _trig_form(g[1], g[2], v, h ? _HYP_NAMES : _TRIG_NAMES)
        end
        return rest
    end
    SymJ._rw_parts(_trig_canonical, u)
end

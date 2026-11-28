# TrigReduce and ExpandTrigReduce (IntegrationUtilityFunctions.m, RUBI 4.16.1): products
# of positive integer powers of sin and cos (or sinh and cosh) as sums of sines and cosines
# of multiple angles, sin(x)^3 = (3 sin(x) - sin(3x))/4, sin(a) cos(b) = (sin(a + b) +
# sin(a - b))/2. RUBI's rules for x^m sin(a + b x)^n with n > 1 (4.1.10, 6.1.x) integrate
# the reduced sum term by term (to Si and Ci); ExpandTrigReduce was plain expansion here.
#
# Each factor is written in exponentials, sin θ = (e^(iθ) - e^(-iθ))/(2i), cos θ =
# (e^(iθ) + e^(-iθ))/2 (sinh θ = (e^θ - e^(-θ))/2, cosh θ = (e^θ + e^(-θ))/2), as a sum
# c_ω e^(iω) over frequencies ω; the product of the factors multiplies these out, and the
# pairs ±ω are put back: c_ω e^(iω) + c_(-ω) e^(-iω) = (c_ω + c_(-ω)) cos ω + i (c_ω - c_(-ω))
# sin ω (cosh and sinh, without the i, for the hyperbolic ones).

# ω or -ω, whichever is the representative of the pair (its lead coefficient positive)
function _freq_sign(w::Sym)
    t = w.kind == SymJ.ADD ? (iszero(w.num) ? Sym(w.coefs[1]) : Sym(w.num)) :
        w.kind == SymJ.MUL ? Sym(w.num) : w
    _isrational(t) && _rat(t) < 0 ? -1 : 1
end

# the frequencies of f(v)^k: Dict(ω => c)
function _freqs(name::Symbol, v::Sym, k::Int)
    h = name in (:sinh, :cosh)
    s = name in (:sin, :sinh)
    d = s ? (h ? Sym(1) // 2 : 1 / (2 * Sym(im))) : Sym(1) // 2
    out = Dict{Sym,Sym}(SymJ.ZERO => SymJ.ONE)
    for _ in 1:k
        nxt = Dict{Sym,Sym}()
        for (w, c) in out, (sg, cc) in ((1, d), (-1, s ? -d : d))
            w2 = expand(w + sg * v)
            nxt[w2] = get(nxt, w2, SymJ.ZERO) + c * cc
        end
        out = nxt
    end
    out
end
function _mul_freqs(a::Dict{Sym,Sym}, b::Dict{Sym,Sym})
    out = Dict{Sym,Sym}()
    for (w1, c1) in a, (w2, c2) in b
        w = expand(w1 + w2)
        out[w] = get(out, w, SymJ.ZERO) + c1 * c2
    end
    out
end
# the sum of the frequencies, in sines and cosines (trig, or hyperbolic with h)
function _from_freqs(fr::Dict{Sym,Sym}, h::Bool)
    C, S = h ? (cosh, sinh) : (cos, sin)
    k = h ? SymJ.ONE : Sym(im)
    out = SymJ.ZERO
    seen = Set{Sym}()
    for (w, c) in fr
        w in seen && continue
        if iszero(w)
            out += c
            continue
        end
        nw = expand(-w)
        push!(seen, w, nw)
        cp, cm = c, get(fr, nw, SymJ.ZERO)
        _freq_sign(w) < 0 && ((w, nw) = (nw, w); (cp, cm) = (cm, cp))
        out += expand(cp + cm) * C(w) + expand(k * (cp - cm)) * S(w)
    end
    out
end

# TrigReduce of one product: its sin/cos and sinh/cosh factors (positive integer powers)
# reduced; nothing when it has none, or only one to the first power
function _trig_reduce_term(t::Sym)
    fs = _factors(t)
    trig, hyp, rest = Dict{Sym,Sym}(SymJ.ZERO => SymJ.ONE), Dict{Sym,Sym}(SymJ.ZERO => SymJ.ONE), SymJ.ONE
    n = 0
    for f in fs
        b, e = f.kind == SymJ.POW ? (f.args[1], f.args[2]) : (f, SymJ.ONE)
        if b.kind == SymJ.FN && b.name in (:sin, :cos, :sinh, :cosh) && length(b.args) == 1 && _isinteger(e) && _rat(e) > 0
            k = Int(_rat(e)); n += k
            fr = _freqs(b.name, b.args[1], k)
            b.name in (:sinh, :cosh) ? (hyp = _mul_freqs(hyp, fr)) : (trig = _mul_freqs(trig, fr))
        else
            rest *= f
        end
    end
    n > 1 || return nothing
    expand(rest * _from_freqs(trig, false) * _from_freqs(hyp, true))
end

# Expand[TrigReduce[u]]
function _trig_reduce(u::Sym)
    v = expand(u)
    sum(_terms(v); init = SymJ.ZERO) do t
        r = _trig_reduce_term(t)
        r === nothing ? t : r
    end
end

# NormalizeTrigReduce: the arguments of the multiple angles expanded, sin(3(a + b x)) as
# sin(3a + 3b x)
function _normalize_trig_reduce(t::Sym)
    function g(f)
        b, e = f.kind == SymJ.POW ? (f.args[1], f.args[2]) : (f, SymJ.ONE)
        b.kind == SymJ.FN && length(b.args) == 1 && b.name in (:sin, :cos, :sinh, :cosh) ?
            apply_function(b.name, Sym[expand(b.args[1])])^e : f
    end
    t.kind == SymJ.MUL ? prod(g, _factors(t); init = SymJ.ONE) : g(t)
end

# ExpandTrigReduce[u, x] and ExpandTrigReduce[u, v, x]: u times the reduced v, term by term
function _expand_trig_reduce(u::Sym, v::Sym)
    w = _trig_reduce(v)
    ts = _terms(w)
    sum(t -> u * _normalize_trig_reduce(t), ts; init = SymJ.ZERO)
end
FUNCS["ExpandTrigReduce"] = (as...) -> length(as) == 3 ? _expand_trig_reduce(_s(as[1]), _s(as[2])) :
                                                         _expand_trig_reduce(SymJ.ONE, _s(as[1]))
FUNCS["TrigReduce"] = u -> _trig_reduce(_s(u))

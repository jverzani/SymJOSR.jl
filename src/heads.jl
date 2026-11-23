# OSR (Mathematica) function heads and the SymJ functions they mean. A SymJ name that
# SymJ does not know gives an inert function node: the result is right, only not
# evaluated further (SinhIntegral, EllipticF, ...).

const FUNCTION_NAMES = Dict{String,Symbol}(
    # RUBI writes the integrand's trig functions in lower case ("inert" trig functions
    # that Mathematica does not evaluate). SymJ keeps sin, ..., csc as they are written,
    # so they map to the ordinary functions.
    "Sin" => :sin, "Cos" => :cos, "Tan" => :tan, "Cot" => :cot, "Sec" => :sec, "Csc" => :csc,
    "sin" => :sin, "cos" => :cos, "tan" => :tan, "cot" => :cot, "sec" => :sec, "csc" => :csc,
    "Sinh" => :sinh, "Cosh" => :cosh, "Tanh" => :tanh, "Coth" => :coth, "Sech" => :sech, "Csch" => :csch,
    "ArcSin" => :asin, "ArcCos" => :acos, "ArcTan" => :atan, "ArcCot" => :acot, "ArcSec" => :asec, "ArcCsc" => :acsc,
    "Asin" => :asin, "Acos" => :acos, "Atan" => :atan, "Acot" => :acot, "Asec" => :asec, "Acsc" => :acsc,
    "Asinh" => :asinh, "Acosh" => :acosh, "Atanh" => :atanh, "Acoth" => :acoth, "Asech" => :asech, "Acsch" => :acsch,
    "Abs" => :abs, "Sign" => :sign,
    "Erf" => :erf, "Erfc" => :erfc, "Erfi" => :erfi,
    "FresnelS" => :fresnels, "FresnelC" => :fresnelc,
    "ProductLog" => :lambertw, "Gamma" => :gamma, "LogGamma" => :loggamma, "PolyGamma" => :polygamma,
    "ExpIntegralEi" => :expinti, "ExpIntegralE" => :expint, "LogIntegral" => :li,
    "SinIntegral" => :sinint, "CosIntegral" => :cosint,
    "SinhIntegral" => :SinhIntegral, "CoshIntegral" => :CoshIntegral,
    "Zeta" => :zeta, "PolyLog" => :polylog,
    "Hypergeometric2F1" => :_₂F₁, "Hypergeometric1F1" => :_₁F₁,
    "EllipticF" => :EllipticF, "EllipticE" => :EllipticE, "EllipticPi" => :EllipticPi,
    "BesselJ" => :besselj, "BesselY" => :bessely, "BesselI" => :besseli, "BesselK" => :besselk,
    "AppellF1" => :AppellF1, "HypergeometricPFQ" => :HypergeometricPFQ,
)

_symfn(name::Symbol) = (as...) -> apply_function(name, Sym[Sym(a) for a in as])

# heads allowed in patterns: arithmetic is handled by `pat` itself
const PATTERN_HEADS = Dict{String,Any}(
    "Sqrt" => sqrt, "Log" => log, "Exp" => exp,
)
for (k, v) in FUNCTION_NAMES
    PATTERN_HEADS[k] = _symfn(v)
end

# ---- arithmetic and elementary functions for evaluation

_sym(v) = v isa Sym ? v : Sym(v)

FUNCS["Multiply"] = (as...) -> prod(_sym, as; init = SymJ.ONE)
FUNCS["Add"] = (as...) -> sum(_sym, as; init = SymJ.ZERO)
FUNCS["Power"] = (a, b) -> _sym(a)^_sym(b)
FUNCS["Rational"] = (a, b) -> _sym(a) / _sym(b)
FUNCS["Sqrt"] = a -> sqrt(_sym(a))
FUNCS["Exp"] = a -> exp(_sym(a))
FUNCS["Log"] = (as...) -> length(as) == 1 ? log(_sym(as[1])) : log(_sym(as[2])) / log(_sym(as[1]))
FUNCS["List"] = (as...) -> Any[as...]
for (k, v) in FUNCTION_NAMES
    FUNCS[k] = _symfn(v)
end

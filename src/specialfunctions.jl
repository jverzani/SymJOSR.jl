# Special functions in RUBI's answers that SymJ does not have, registered with SymJ (a
# numeric value and partial derivatives), so answers that use them can be evaluated and
# checked. Registered when the package is loaded (__init__): SymJ's registry is a
# global of SymJ, and changes made while precompiling this package would not be kept.
#
#   logint(x)              li(x) = Ei(log x), RUBI's LogIntegral
#   sinhint(x), coshint(x) Shi, Chi, RUBI's SinhIntegral, CoshIntegral (the names of
#                          SymJ's RischIntegrate extension, which registers them too)
#   EllipticF(φ, m), EllipticE(φ, m), EllipticE(m), EllipticPi(n, φ, m), EllipticPi(n, m)
#                          incomplete and complete elliptic integrals, in Mathematica's
#                          convention (parameter m = k²), by quadrature of their
#                          defining integrals

import SpecialFunctions as SF
import QuadGK

# ∫₀^φ g(sin²θ) dθ, along the segment from 0 to φ (φ may be complex)
_quad_sin2(g, φ) = (φ = float(φ); φ == 0 ? zero(φ) : φ * first(QuadGK.quadgk(s -> g(sin(s * φ)^2), 0, 1; rtol = 1e-13)))

_ellF(φ, m) = _quad_sin2(s -> 1 / sqrt(1 - m * s), φ)
_ellE(φ, m) = _quad_sin2(s -> sqrt(1 - m * s), φ)
_ellPi(n, φ, m) = _quad_sin2(s -> 1 / ((1 - n * s) * sqrt(1 - m * s)), φ)

_symE(args...) = apply_function(:EllipticE, Sym[args...])
_symF(args...) = apply_function(:EllipticF, Sym[args...])

# ∂F/∂m, ∂E/∂m for the incomplete integrals (DLMF 19.4.2 and 19.4.1, in m = k²)
_dF_dm(φ, m) = _symE(φ, m) / (2m * (1 - m)) - _symF(φ, m) / (2m) -
    sin(2φ) / (4 * (1 - m) * sqrt(1 - m * sin(φ)^2))
_dE_dm(φ, m) = (_symE(φ, m) - _symF(φ, m)) / (2m)

function _register_functions()
    reg(name; kw...) = SymJ.register_function!(name; kw...)
    reg(:logint; julia = x -> SF.expinti(log(x)), diff = (args, i) -> 1 / log(args[1]))
    if !haskey(SymJ.FUNCTION_RULES, :sinhint)      # (as SymJ's RischIntegrate extension)
        reg(:sinhint; julia = x -> (SF.expinti(x) + SF.expint(x)) / 2, diff = (args, i) -> sinh(args[1]) / args[1])
        reg(:coshint; julia = x -> (SF.expinti(x) - SF.expint(x)) / 2, diff = (args, i) -> cosh(args[1]) / args[1])
    end
    reg(:EllipticF; julia = _ellF, diff = function (args, i)
        φ, m = args
        i == 1 ? 1 / sqrt(1 - m * sin(φ)^2) : _dF_dm(φ, m)
    end)
    reg(:EllipticE; julia = (a...) -> length(a) == 1 ? _ellE(π / 2, a[1]) : _ellE(a...),
        diff = function (args, i)
            length(args) == 1 && return nothing              # complete E(m): not needed yet
            φ, m = args
            i == 1 ? sqrt(1 - m * sin(φ)^2) : _dE_dm(φ, m)
        end)
    reg(:EllipticPi; julia = (a...) -> length(a) == 2 ? _ellPi(a[1], π / 2, a[2]) : _ellPi(a...),
        diff = function (args, i)
            (length(args) == 3 && i == 2) || return nothing  # only ∂/∂φ
            n, φ, m = args
            1 / ((1 - n * sin(φ)^2) * sqrt(1 - m * sin(φ)^2))
        end)
    nothing
end

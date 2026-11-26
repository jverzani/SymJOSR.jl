"""
    SymJOSR

The OpenSymbolicRules (OSR) rule sets in SymJ. The first, and so far only, is RUBI's
rule-based integration, from <https://github.com/OpenSymbolicRules/Integration>: its
rules become SymJ pattern-matching rules, with RUBI's predicates as their guards.

```julia
using SymJ, SymJOSR
@syms x a b
SymJOSR.integrate((a + b*x)^3, x)
```

The rule data is downloaded on first use; see [`SymJOSR.rules_dir`](@ref).
"""
module SymJOSR

# SymJ before JSON: in the other order, precompiling this package on Julia 1.12 does
# not finish (the docstrings' processing is re-inferred, for over an hour on CI)
using SymJ
using SymJ: Sym, subs
import CodecZlib, Downloads, JSON, Random, Scratch, Tar

include("fetch.jl")
include("errata.jl")
include("osr.jl")
include("heads.jl")
include("predicates.jl")
include("derivatives.jl")
include("utilities.jl")
include("sums.jl")
include("structure.jl")
include("fractional.jl")
include("trigsubst.jl")
include("linear.jl")
include("specialfunctions.jl")
include("integration.jl")
include("testsuite.jl")

__init__() = _register_functions()

end

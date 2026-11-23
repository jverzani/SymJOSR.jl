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

import CodecZlib, Downloads, JSON, Scratch, Tar
using SymJ
using SymJ: Sym, subs

include("fetch.jl")
include("osr.jl")
include("heads.jl")
include("predicates.jl")
include("utilities.jl")
include("sums.jl")
include("integration.jl")
include("testsuite.jl")

end

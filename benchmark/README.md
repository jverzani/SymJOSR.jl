# Benchmarks

Measures of completeness, kept out of the test suite: they take longer, and they track
progress rather than pass or fail.

## Apostol problems

175 integrands from the completeness benchmark of
[RischIntegrate.jl](https://github.com/jverzani/RischIntegrate.jl) (`test/test_apostol.jl`,
taken there from SymbolicIntegration.jl), in `apostol_problems.jl`.

```bash
julia --project=. benchmark/apostol.jl            # counts, and the problems not verified
julia --project=. benchmark/apostol.jl 5 out.tsv  # timeout per problem (s); results per problem
```

A problem counts when the answer is **verified**: its derivative equals the integrand at
several points. (RischIntegrate's test counts a problem when `integrate` returns without
an error; it requires 163 of 175.)

| date | SymJOSR | OSR rules | verified | wrong | unevaluated | timeout | time |
|:--|:--|:--|--:|--:|--:|--:|--:|
| 2026-11-24 | main (#2) | 436f82c | 122 / 175 (69.7%) | 1 | 52 | 0 | 34 s |
| 2026-11-24 | + special functions (PolyLog → `li`, elliptic, Shi/Chi, li) | 436f82c | **123 / 175** (70.3%) | 0 | 52 | 0 | 25 s |

The misses, in groups: rational functions that need partial fractions over quadratic
factors (#106–#130, #139; their RUBI rules are in 1.2.1, 1.3 and 1.4.1, which are empty
in OSR), `x^n sin x`, `x^n cos x` and powers of `sin x`/`cos x` (#22–#38, #46), rational
functions of `sin x` and `cos x` (#140–#147), and substitutions (#10–#12, #53, #70, #78).

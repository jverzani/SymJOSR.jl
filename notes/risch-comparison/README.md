# SymJOSR vs RischIntegrate

A comparison of SymJOSR (RUBI's rules on SymJ) with RischIntegrate, run on 2026-11-26 and 2026-11-27, on a sample of the OSR test problems.

- **SymJOSR:** main at e4fb6de, which includes #26 and #27.
- **RischIntegrate:** 1.5.1, called through `SymJRischIntegrateExt` as `RischIntegrate.integrate(u, x)`.
- **SymJ:** main.
- **Julia:** 1.13.4.

## Setup

- **Sample:** `picks8.tsv`, 1,697 problems. It holds 8 problems from each test file, drawn with a fixed seed (`random.seed(2026)`) from the 40-per-file survey sample, so every section is represented.
- **Limits:** 60 s per problem for each system. For SymJOSR, the limit is `_check`'s own time limit. For RischIntegrate, the driver kills the worker after 65 s and records a timeout.
- **Checking answers:** both systems' answers go through SymJOSR's numerical derivative check, `_verify`.
- **Piecewise answers:** RischIntegrate sometimes returns a piecewise answer, with one case per condition on the parameters, such as `[a/c ≫ 0] => …`. Such an answer counts as verified when every branch passes the check; 182 do. Another 25 have some branches that pass and 30 have none; they are counted as unsolved.
- **Size measures:**
  - *Leaf count:* RUBI's `LeafCount`, as `SymJOSR.leafcount`.
  - *Operations:* the number of `+ - * / ^` characters plus function applications in the printed answer.

## Coverage

| | Problems |
|---|---|
| Both solve | 706 |
| Only SymJOSR | 506 |
| Only RischIntegrate | 138 |
| Neither | 347 |

SymJOSR verifies 1,212 answers, RischIntegrate 844. The sample comes from RUBI's own test suite, so SymJOSR has a home advantage.

| Section | Problems | Both | Only SymJOSR | Only Risch | Neither |
|---|---|---|---|---|---|
| 0 independent | 95 | 75 | 5 | 14 | 1 |
| 1 algebraic | 316 | 163 | 116 | 5 | 32 |
| 2 exponentials | 24 | 14 | 4 | 0 | 6 |
| 3 logarithms | 72 | 25 | 22 | 1 | 24 |
| 4 trig | 598 | 224 | 188 | 55 | 131 |
| 5 inverse trig | 144 | 46 | 44 | 14 | 40 |
| 6 hyperbolic | 208 | 85 | 49 | 34 | 40 |
| 7 inverse hyperbolic | 160 | 61 | 49 | 11 | 39 |
| 8 special | 80 | 13 | 29 | 4 | 34 |

### What RischIntegrate returned where only SymJOSR solves (506)

| RischIntegrate status | Problems | What it means |
|---|---|---|
| Not implemented | 158 | `RischNotImplemented`, mostly radicals of non-rational expressions, or more than 8 transcendental constants |
| Timeout | 121 | |
| Not elementary | 117 | `NotElementary`: it proved no elementary antiderivative exists |
| Error | 60 | Mostly `MethodError: no method matching Sym(::Expr)` |
| Partly verified piecewise | 17 | |
| Unevaluated | 18 | |
| Wrong | 10 | |
| Unverified piecewise | 5 | |

All 117 "not elementary" claims agree with SymJOSR's answers: each of those answers uses a special function (AppellF1, hypergeometric, erf, polylog, gamma, elliptic integrals and so on). None of them contradicts a claim. The `Sym(::Expr)` method errors look like a RischIntegrate bug worth reporting.

### What SymJOSR did where only RischIntegrate solves (138)

131 were left unevaluated: no rule applied, rather than a timeout. Another 2 timed out and 5 were wrong. The unevaluated ones point to rule gaps; most are in the trig and hyperbolic sections (55 and 34 of the 138).

## Answer size, where both are correct

These are the 554 pairs where both answers are a single expression, so piecewise answers are left out.

| Measure | SymJOSR shorter | RischIntegrate shorter | Equal | Median ratio (Risch/SymJOSR) | Quartiles |
|---|---|---|---|---|---|
| Leaf count | 357 | 150 | 47 | 1.20 | 0.97, 1.79 |
| Operations | 380 | 116 | 58 | 1.22 | 1.00, 1.90 |

By section, using operations:

| Section | Pairs | SymJOSR shorter | Risch shorter | Equal | Median ratio |
|---|---|---|---|---|---|
| 0 independent | 70 | 42 | 15 | 13 | 1.14 |
| 1 algebraic | 106 | 64 | 25 | 17 | 1.05 |
| 2 exponentials | 12 | 4 | 7 | 1 | 0.89 |
| 3 logarithms | 20 | 16 | 1 | 3 | 1.39 |
| 4 trig | 180 | 135 | 32 | 13 | 1.37 |
| 5 inverse trig | 43 | 34 | 6 | 3 | 1.24 |
| 6 hyperbolic | 62 | 44 | 14 | 4 | 1.44 |
| 7 inverse hyperbolic | 50 | 39 | 9 | 2 | 1.53 |
| 8 special | 11 | 2 | 7 | 2 | 0.87 |

The leaf counts by section are similar. SymJOSR's answers are shortest on trig, hyperbolic and inverse-function problems, where RischIntegrate rewrites trig and hyperbolic functions as exponentials or multiple angles. Algebraic problems are roughly even. RischIntegrate's answers are slightly shorter on exponentials and special functions. 40 problems get exactly the same printed answer from both systems.

### Examples

These show the largest differences in leaf count.

- **SymJOSR much shorter:**
  - 2.3 Exponential functions #282: SymJOSR gives `F^a*gamma(5, -b*(d*𝓍 + c)^3*log(F))/(3*b^5*d*log(F)^5)` (29 leaves). RischIntegrate gives `F^(b*(d*𝓍 + c)^3 + a)` times a degree-12 polynomial (566 leaves).
  - 6.1.3 #22: SymJOSR gives `-(cosh(b*𝓍^2 + a) - cosh(b*𝓍^2 + a)^3 + 3*cosh(b*𝓍^2 + a)^5/5 - cosh(b*𝓍^2 + a)^7/7)/(2*b)` (50 leaves). RischIntegrate gives a sum of powers of `exp(b*𝓍^2)` with coefficients in `cosh(a)` and `sinh(a)` (880 leaves).
  - 4.3.11 #9 is 50 leaves against 299, and 5.5.2 #18 is 175 against 1,086.
- **RischIntegrate much shorter:**
  - Bronstein #4: RischIntegrate gives `_₂F₁(1/2, 2/3, 5/3, 𝓍^3)*𝓍^2/2` (18 leaves). SymJOSR gives an EllipticE form (370 leaves).
  - 4.3.4.2 #133 is 13,852 leaves from SymJOSR against 1,748, and 4.3.4.2 #104 is 6,336 against 1,647. These SymJOSR answers are worth investigating.
  - 6.4.1 #19 is 214 leaves against 65.

## Time

On the 706 problems both solve, the median time is 0.76 s for SymJOSR and 1.00 s for RischIntegrate. SymJOSR is faster on 373 of them.

## Wrong answers

The derivative check rejected 42 SymJOSR answers and 15 RischIntegrate answers. I haven't checked them by hand. Most of SymJOSR's involve AppellF1, polylog or erf, and most of RischIntegrate's involve polylog, Clausen functions or multiple-angle forms. Those are where the numerical check is least reliable, so many are probably check failures rather than real errors. `python3 -I analyze.py` lists them.

## Files

- `Project.toml`: the environment, with SymJOSR from this checkout (`../..`) and SymJ from main.
- `worker.jl`: reads `file<TAB>id` lines and, for each problem, prints an OSR row and a RISCH row with these columns: system, file, id, status, seconds, leafcount, ops, answer.
- `driver.py PICKS SHARD NSHARDS OUT`: runs one shard of the sample and restarts the worker after a kill. It skips problems already in OUT, so a run can resume. The final run used 3 shards; 6 ran the machine out of memory.
- `rescore.jl`: re-runs the piecewise and RootSum answers from RischIntegrate and checks each branch. Its output is in `rescore_out.tsv`.
- `analyze.py`: prints every table above from `results.tsv` and `rescore_out.tsv`.
- `picks8.tsv`: the sample.
- `results.tsv`: every row of the run. It is not committed (1.4 MB), as with `notes/session2/data`.

To reproduce:

```
julia +1.13.4 --project=. -e 'using Pkg; Pkg.instantiate()'
for s in 0 1 2; do python3 -I driver.py picks8.tsv $s 3 out_$s.tsv & done; wait
cat out_*.tsv > results.tsv
awk -F'\t' '$1=="RISCH" && $4=="unevaluated" && $8 !~ /^(RischNotImplemented|NotElementary|[A-Za-z]*Error)/ {print $2"\t"$3}' results.tsv > rescore.tsv
julia +1.13.4 --project=. rescore.jl rescore.tsv > rescore_out.tsv
python3 -I analyze.py
```

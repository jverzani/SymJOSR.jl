# SymJOSR handoff — 2026-11-23

State of the package after the first session, and the open problems, in rough order
of priority. Read README.md first for how the package works.

## Where things stand

- 4,988 of the 5,441 OSR rules in the files RUBI 4.16.1 loads become SymJ rules (OSR
  commit 436f82c; 5,411 and 424 skipped at ed47124); the other 453 use a head (predicate, utility or function) with no entry yet in
  `FUNCS`/`SPECIAL`. `SymJOSR.unsupported_heads(SymJOSR.load_rules())` lists them.
- Full run of `tests/.../1.1.1.2-(a+b-x)^m-(c+d-x)^n.json`, 1,971 problems, timeout
  5 s (session 2, OSR commit 436f82c):

  |              | verified | unevaluated | timeout | wrong |
  |:--|--:|--:|--:|--:|
  | session 1    | 1,132 | 402 | 276 | 161 |
  | session 2, loops fixed | 1,319 | 361 | 269 |  22 |
  | session 2, GtQ fixed   | 1,598 | 361 |   1 |  11 |
  | session 2, cycles      | 1,635 | 325 |   0 |  11 |

  A full run now takes under a minute (was 45). 1.1.3.8 (594 problems): 306
  verified, 285 unevaluated, 0 timeouts, 3 wrong, in 29 s. The deadline is only checked on
  entry to `_int`, so a timed-out problem can run well past its limit.
- `test/runtests.jl` passes (30 tests).
- Item 1 is no longer pressing: the time went to timeouts, now gone. (Profiling 120
  problems had put ~80% of `_int`'s time in guards, mostly `simplify` in `_eq`, only
  ~20% in trying rules; a numeric probe before `simplify` made a full run slower and
  was reverted.)
- The 11 "wrong" are answers the check can't judge, not known errors: elliptic
  integrals with complex coefficients (#1179-#1227) and ₂F₁(…, 3 - x) with
  (3 - x)^(k/2) (#1166, #1167), on a cut at every point in range.

### Running things

```bash
# a local Integration checkout, used instead of a download
export SYMJOSR_INTEGRATION_DIR=/path/to/OpenSymbolicRules/Integration
julia --project=. test/runtests.jl
```

```julia
using SymJ, SymJOSR
R = SymJOSR.load_rules()                      # ~6 s
res = SymJOSR.test_problems(files = ["1.1.1.2-"], rules = R, timeout = 1.0, verbose = true)
res.counts

SymJOSR.DEBUG[] = true                        # print each rule as it fires, by depth
SymJOSR.MAXDEPTH[] = 8                        # keep a looping problem short
@syms x a b
SymJOSR.integrate(sqrt(a + b*x)/x, x; trace = true)
```

`_run_problem(expr, R, timeout)` runs a single test problem, given the `"expression"`
field of a fixture.

## 1. Speed: index the rules by the integrand's shape

`_int` (src/integration.jl) tries every rule in load order, calling each
`SymJ.Rule`; `_quickfail` makes a miss cheap, but there are ~5,000 rules, and an
integration recurses through `Int` many times. Problem 1 of 1.1.1.2 (the integrand
`0`) takes ~11 s, though that is mostly compilation; typical problems take 0.05–1 s.

The idea: precompute, for each rule, a key from its pattern's top-level structure, and
for each integrand only the rules whose key can match it, **keeping load order** among
them (rule priority is order: RUBI picks the first applicable rule).

- The key could be the integrand's head kind (`MUL`, `POW`, `ADD`, `FN` with its name,
  `SYMBOL`, `NUMBER`) plus, for products, the multiset of factor heads (a `POW` whose
  base is linear in x, `sin`, `log`, ...).
- Rules whose pattern is a bare slot (`u_`, as in 9.3 and the host rules) or a head slot
  (`F_[...]`) must be in every bucket.
- Optional slots complicate it: `(a. + b.*x)^m.` also matches `x` and `x^2` (defaults
  b = 1, a = 0, m = 1), so a `POW` pattern can match a `SYMBOL` subject, and a sum
  pattern a non-sum. The key of a pattern must be the set of subject shapes it can
  match once defaults are applied.
- SymJ has `_RuleSet` (src/patterns.jl) which indexes rules by the function name at the
  top of their left side; it does not cover `MUL`/`POW`/`ADD` subjects, which are most
  integrands, but shows the shape of the code.
- Measure before and after: time `test_problems` on 1.1.1.2, and check that the
  counts don't change (an index that drops a rule changes results).

## 2. √(a+bx)/x gives ₂F₁ instead of atanh

1.1.1.2 problems #294 and #295:

```
sqrt(b*x + a)/x    => -2*_₂F₁(1, 3/2, 5/2, b*x/a + 1)*(b*x + a)^(3/2)/(3*a)
sqrt(b*x + a)/x^2  => -_₂F₁(1, 1/2, 3/2, b*x/a + 1)*b*sqrt(b*x + a)/a - sqrt(b*x + a)/x
```

Two separate questions:

- **Why is the ₂F₁ rule reached at all?** RUBI's answer is in terms of `atanh`
  (`2√(a+bx) - 2√a·atanh(√(a+bx)/√a)`). Some earlier rule should apply and doesn't:
  either its guard is false here (suspects: `PosQ`/`NegQ`, `SimplerQ`, `SumSimplerQ`,
  `GtQ` on symbolic parameters — see `src/predicates.jl`, where approximations are
  marked) or the rule was skipped for an unsupported head. Run with `DEBUG[] = true`,
  find RUBI's rule in `RubiUpstream/Rubi/IntegrationRules/1 Algebraic functions/1.1
  Binomial products/1.1.1 Linear/1.1.1.2 ...m` and check whether it loaded
  (`R.skipped`) and why its guard fails.
- **Is the answer wrong, or the check?** The check (session 2). `_verify` now skips
  points that put a ₂F₁ argument on its cut, z ≥ 1, and then samples values of either
  sign; #294 and #295 verify. Its points are also seeded by the integrand (verdicts
  were random from run to run) and avoid singular points such as x = 1. On 1.1.1.2:
  161 "wrong" became 29. Two cube-root answers with a ₂F₁ (#417, #431) can't be
  checked fairly: positive points are on the cut, negative ones change the cube
  root's branch.

## 3. Loop: (bx+a)(c+d)/e times out — fixed (session 2)

Two causes, both fixed:

- **Absent terms.** SymJ lets a term `~!b*t` of a sum pattern be absent (b = 0);
  Mathematica does not (`b_.` in a product defaults to 1, so `a_ + b_.*x_` needs a term
  in x). `(c+d)` matched `a_ + b_.*x_` with b = 0, and 1.1.1.3 #1 rewrote #162 to itself.
  `pat` now gives an optional factor of a product a nonzero predicate (`_nonzero_factor`,
  src/osr.jl).
- **Constant factors.** RUBI keeps constants outside (`Star[a, Int[u, x]]`); SymJ's
  canonical form puts them back in, and with `Pq = c^-8`, 1.1.3.7 #1 rewrote
  `Int[c^-8 (a+bx)^-3]` to itself. `_int` now integrates a product's free factors
  out before trying rules.

Lost by the first fix: #765 and #789, `(bx+a) (c x^2)^(±1/2)`. The rule for
`(a x^n)^m` is in "9.1 Integrand simplification rules", which RUBI 4.16.1 does not
load; before, they were solved only through the absent-term matching.

**The other timeouts: GtQ.** 268 of the 269 were 1.1.1.2 #32 rewriting its own result:
RUBI's rule before it (#31, the ₂F₁ closed form) takes over once
`GtQ[b/(b*c' - a*d'), 0]` holds for the new c', d', which needs RUBI's
`N[Together[u]]` to see that the quotient is 1. `_realval` (order predicates, Max,
Min) now cancels an expression with symbols before giving up on it.

**Cycles.** The last one, #1111, was `PolyQ[u, x^n]` true for any u without the
subterm x^n ((1 + a x)/(1 - a x) "a polynomial of degree 0 in x^2"), so 1.1.3.7 #12
expanded it again and again; `PolyQ` now follows RUBI. Fixing it exposed loops through
1.1.3.7 #10, `Int[ExpandIntegrand[Pq/(a + b x^n)]]`: RUBI's ExpandIntegrand splits
that over the n-th roots of a/b, ours (expand + apart) hands it back unchanged. `_int`
now keeps the integrands being integrated on a stack (`_STACK`); a step that comes back
to one of them fails with `Cycle` and its rule is rejected, so the next rule is tried.
That also turned 37 unevaluated problems of 1.1.1.2 into answers.

Lost to the PolyQ fix (1.1.3.8 #181, `(1 - x^4)/(1 + x + x^2 + x^3)`, and #585): they
went through #12 only because of the wrong PolyQ. RUBI's rule for #181
(`PolynomialQuotient`, 1.4.1) is in a file empty in OSR, and the head is unsupported.

## 4. The unsupported heads

Session 2 added (src/structure.jl) `LinearMatchQ`, `QuadraticMatchQ`,
`BinomialMatchQ`, `BinomialQ`/`BinomialParts`, `LinearPairQ`, `RationalFunctionQ`,
`PolynomialQuotient`/`PolynomialRemainder`, and the rule files' own `IntLinearQ`,
`IntBinomialQ` (7, 8 and 10 arguments) and `IntQuadraticQ`: 4,988 -> 5,167 rules.
`BinomialParts` leaves out RUBI's product-of-two-binomials case (approximation).

Effect: 1.1.3.8 verified 306 -> 330. 1.1.1.2 verified the same, 1,635, but not the
same problems: +65, and -44 that the newly loaded 1.1.1.2 #19/#25 now send to
`(a + b x + c x^2)^p` forms whose RUBI rules (1.2.1.1 #17, #18: `With[...]`) OSR
does not have yet (OSR known issue: rules with `With`); -23 more are elliptic
answers the check can't judge. Expect those back when OSR converts `With` rules.

Remaining top of `unsupported_heads(R)`: `InverseFunctionFreeQ` 30, `MatchQ` 22,
`KnownSineIntegrandQ`/`KnownSecantIntegrandQ` 22 each, `Condition` 20,
`FunctionOfExponentialQ` 16, `SubstFor` 14, `FunctionOfQ` 13, `IndependentQ` 12, ...

Definitions are in RUBI's `IntegrationUtilityFunctions.m` (clone
`https://github.com/RuleBasedIntegration/Rubi`). Adding one is one entry, e.g.

```julia
SymJOSR.@osrfunc BinomialQ(u, x) = ...
```

in `src/predicates.jl` (guards) or `src/utilities.jl` (right sides). `MatchQ` and
`Condition` carry patterns inside constraints, so they need a `SPECIAL` entry that
builds a SymJ pattern from the OSR pattern (`pat` in src/osr.jl) and matches.
Some entries in the list are bare names (`m`, `d.`, `f`): those are OSR known issue 2
(names the pattern never binds) or names inside `MatchQ` patterns; not ours to fix.

## 5. Approximations to revisit

Marked in the code: `PosQ` (Mathematica orders a sum's terms differently from SymJ),
`SimplerQ`, `SumSimplerQ`, `Simp` (identity), `ExpandIntegrand` (expand + `apart`),
`IntPart`/`FracPart`, `Rt`. They keep answers correct but can change which rule fires,
so they are the first suspects whenever a problem goes wrong or loops. RUBI's lower-case
inert trig functions are mapped to the ordinary ones; the trig sections may need them
kept apart (rules in 4.7.5 "Inert trig functions" convert between them).

## Upstream: SymJ

- Fixed in SymJ main (012337a, 2026-11-24): `N` of ₂F₁(a, b; c; z) at an exact
  rational z > 1/2 was wrong when c - a - b is an integer. `_verify` used floats for
  answers with a ₂F₁ until then; it uses exact values again.
- Julia 1.12: the CI job runs far longer than the others (SymJ needed inference
  barriers and no coverage on 1.12; we have the latter). See the session 2 notes on CI.

## Upstream (OpenSymbolicRules/Integration), reported 2026-11-23

- 31 rule files that RUBI loads are empty in OSR (~1,100 rules: all of 1.1.2, most of
  1.2.1 and 1.3, 1.4.1–1.4.3, 9.1, 9.2). `HOST_RULES` in `src/sums.jl` stands in for
  1.4.1's sum rule and for constant integrands, used only while that file is empty.
- `meta.json`'s `load_order` is section order; RUBI's order is in `Rubi.m`, and 22 OSR
  files are not loaded by RUBI 4.16.1. We use `src/rubi_load_order.txt` (from `Rubi.m`).
- Re-check both after OSR updates: `SymJOSR.update_rules!()`, then compare
  `length(load_rules(reload = true).rules)` and the empty files.

## Later

- An extension in SymJ that uses SymJOSR together with RischIntegrate (order and
  fallback to be decided).
- Registering the package (SymJ first, since `[sources]` is not allowed in General).

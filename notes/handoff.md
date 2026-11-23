# SymJOSR handoff — 2026-11-23

State of the package after the first session, and the open problems, in rough order
of priority. Read README.md first for how the package works.

## Where things stand

- 4,987 of the 5,411 OSR rules in the files RUBI 4.16.1 loads become SymJ rules; the
  other 424 use a head (predicate, utility or function) with no entry yet in
  `FUNCS`/`SPECIAL`. `SymJOSR.unsupported_heads(SymJOSR.load_rules())` lists them.
- Sample run, first 300 problems of `tests/.../1.1.1.2-(a+b-x)^m-(c+d-x)^n.json`
  (timeout 1 s each): 288 verified, 9 unevaluated, 1 timeout, 2 "wrong".
- `test/runtests.jl` passes (23 tests).
- No complete run of section 1.1.1 (~900 problems) yet: too slow (problem 1 below).

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
- **Is the answer wrong, or the check?** `_verify` (src/testsuite.jl) puts parameters
  and x in (0.3, 1.7), so `bx/a + 1 > 1`, on the branch cut of ₂F₁. The result may be
  right and the numeric check wrong there. Try points with `bx/a + 1 < 1` (a < 0), and
  consider making `_verify` count a problem as verified when it agrees at points where
  every function is off its branch cut.

## 3. Loop: (bx+a)(c+d)/e times out

1.1.1.2 problem #162, `(b*x + a)*(c + d)/e`, hits the timeout. Likely two rules
rewriting into each other (e.g. one factoring out the constant, another distributing
it). With `MAXDEPTH[] = 8` and `DEBUG[] = true` the repeating rules show up in the
printout. RUBI avoids such loops with guards like `SimplerQ`/`SumSimplerQ`, so this
may be the same root cause as 2: an approximate predicate. If it is a SymJ
canonical-form difference (SymJ distributes a number over a sum, `2(x+1)` → `2x+2`),
the fix may be in the guard, not the rule.

## 4. The unsupported heads

`unsupported_heads(R)`, top of the list: `BinomialQ` 50, `LinearMatchQ` 45,
`IntBinomialQ` 39, `BinomialMatchQ` 37, `InverseFunctionFreeQ` 30,
`KnownSineIntegrandQ`/`KnownSecantIntegrandQ` 22 each, `MatchQ` 21, `Condition` 19,
`PolynomialQuotient` 18, `FunctionOfExponentialQ` 16, `SubstFor` 14, ...

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

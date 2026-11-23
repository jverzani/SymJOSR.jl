# SymJOSR

Rule sets from [OpenSymbolicRules](https://github.com/OpenSymbolicRules) (OSR) for
[SymJ](https://github.com/jverzani/SymJ.jl). The first is RUBI, Albert Rich's
rule-based integrator, from the
[OSR Integration](https://github.com/OpenSymbolicRules/Integration) JSON files.

```julia
using SymJ, SymJOSR
@syms x a b
SymJOSR.integrate(x * (a + b*x)^5, x)
SymJOSR.integrate((a + b*x)^3, x; trace = true)    # the result, and the rules applied
```

Not registered yet: `SymJ` is taken from GitHub through `[sources]` (Julia 1.12+).

## How it works

* **Rules are data, fetched at run time.** On first use the Integration repository is
  downloaded (its `main` branch, as a tarball) and cached with Scratch.jl.
  `SymJOSR.update_rules!()` fetches it again; `update_rules!(ref = "<tag or sha>")`
  pins a version; `SymJOSR.rules_version()` says what is loaded. To work against a
  local checkout, set `ENV["SYMJOSR_INTEGRATION_DIR"]` or call
  `SymJOSR.use_rules_dir!(dir)`.
* **Patterns become SymJ patterns.** `a_` is `~a`, `a.` (a default) is `~!a`, `F_[u]`
  is `(~F)(u)`. The integration variable is renamed to a reserved symbol before
  matching, so patterns hold it as a literal.
* **Constraints become guards.** A rule's SymJ right side checks RUBI's constraints and
  returns `nothing` to reject the match, so the matcher goes on to the next match.
* **Heads are a registry.** Each OSR head (a predicate such as `IGtQ`, a utility such as
  `ExpandIntegrand`, a function such as `ArcTanh`) is one entry in `SymJOSR.FUNCS` or
  `SymJOSR.SPECIAL`. A rule using a head without an entry is skipped, not loaded
  wrongly; `SymJOSR.unsupported_heads(load_rules())` is the to-do list.
* **RUBI's load order.** Rules are tried in the order RUBI 4.16.1's `Rubi.m` loads
  them (`src/rubi_load_order.txt`), not in section order: priority depends on it.

## Measuring

```julia
R = SymJOSR.load_rules()
res = SymJOSR.test_problems(files = ["1.1.1-linear"], rules = R)
res.counts   # verified / wrong / unevaluated / timeout / error
```

An answer counts as verified when its derivative equals the integrand at random
points.

## Known gaps

* **OSR data.** 31 of the rule files RUBI loads are empty in OSR (about 1,100 of RUBI's
  ~7,200 rules: all of 1.1.2, most of 1.2.1 and 1.3, 1.4.1-1.4.3, 9.1, 9.2). Where an
  empty file holds a rule the rest depend on, a host rule stands in for it while the
  file is empty (`SymJOSR.HOST_RULES`; so far 1.4.1's term-by-term integration of
  sums).
* **Heuristics.** `PosQ`, `SimplerQ`, `SumSimplerQ`, `Simp` and `ExpandIntegrand`
  follow RUBI's definitions approximately: answers are correct but may differ in form
  from RUBI's optimal antiderivatives.
* **Inert trig functions.** RUBI's lower-case `sin`, ... are mapped to SymJ's ordinary
  functions.

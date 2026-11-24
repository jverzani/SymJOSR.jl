# Session 2 state — suspended 2026-11-24

Work stopped mid-way on three threads. Everything running was stopped; nothing is
left in the background. `notes/handoff.md` has the results so far; this file is
where each open thread stands and how to pick it up.

## Branches

- `fix-loops-timeouts-verify` — PR #1 (pushed). Loop/timeout fixes, verifier,
  `PolyQ`, cycle detection, CI (as SymJ's), Windows path fix (`5fc48e2`), no coverage
  on 1.12 (`9c3de7a`). CI: 1.13, pre, macOS, Windows pass; **1.12 never finishes**
  (below).
- `more-predicates` — local only, **not pushed**, on top of PR #1:
  `07a5456` structural predicates + polynomial division + `ExpandIntegrand` linear
  product + `EqQ` by `cancel`; `adc8684` exact values in `_verify` again (SymJ fixed
  ₂F₁). Tests pass (51). Open question for the user: second PR after #1, or into #1.
- Local `main` = `origin/main`.

## 1. Julia 1.12 CI: SymJOSR's precompile stalls

- CI log (`data/ci_julia1.12_cancelled.log`): SymJ precompiles in 467 s, then
  precompiling SymJOSR runs until the 60-minute job limit. The tests never start.
- Reproduced locally (Julia 1.12.7, SymJ main): same stall. But
  `include("src/SymJOSR.jl")` without caching takes 7 s and `load_rules()` 5 s: only
  the precompile (package image) step is slow.
- SymJ's own 1.12 fix (`b687f2e`) was two parts: no coverage (we have it) and
  inference barriers in SymJ code. Likely our module-level code or the image build
  triggers the same 1.12 inference blowup.
- **Next:** `scripts/bisect112.sh <dir>` precompiles copies of the package with only the
  first N source files (needs a 1.12-instantiated checkout at `<dir>/wt112`, e.g. a
  `git worktree` of the PR branch, `julia +1.12 --project=. -e 'using Pkg;
  Pkg.instantiate()'`). It was stopped during N = 2 (fetch.jl + osr.jl), still
  running after ~3 minutes: so the stall may already be in osr.jl (its top level calls
  SymJ: `Sym(XNAME)`, the `ATOMS` table with `Sym(im)`,
  `Sym(Base.MathConstants.eulergamma)`, `SymJ.PI`). `scripts/top112.jl` times those
  calls one by one. Delete `~/.julia/compiled/v1.12/SymJOSR` between attempts (stale
  pidfiles otherwise make the next one wait).
- Until fixed, the 1.12 job will be cancelled at 60 minutes; it is not a required
  check, so it doesn't block merging.

## 2. Survey of all test files (next step 1)

- Seeded sample of 40 problems per test file (215 files, ~8,600 problems), 3 s limit,
  code of `more-predicates`. Stopped at 3,618 problems (through 4.2.x).
  `data/survey_new_partial.tsv`: file, id, status, seconds.
  `data/survey_old_partial.tsv`: the first 3,151 with PR #1's code (comparison).
- Hangs: two problems ran past their deadline indefinitely (the deadline is checked
  only on entry to `_int`): `data/survey_hangs.tsv` (4.1.3.1 #214, 4.2.12 #60). The
  first run hung 1.5 h on one before the watchdog existed.
- **Resume:** copy `data/survey_new_partial.tsv` to `<scratch>/survey.tsv` and
  `data/survey_hangs.tsv` to `<scratch>/survey_hang.tsv`, put `survey2.jl` in
  `<scratch>`, then `scripts/survey_driver.sh <scratch>`: it skips what is done, kills a
  problem after 60 s and records it as a hang.

## 3. Unsupported heads (next step 2)

Done on `more-predicates` (see handoff item 4). Next candidates by rules unlocked:
`InverseFunctionFreeQ` (30), `KnownSineIntegrandQ`/`KnownSecantIntegrandQ` (22 each),
`MatchQ`/`Condition` (need a SPECIAL entry), `FunctionOfExponentialQ`, `SubstFor`.

## Other findings to act on

- A hard deadline: problems that never return (survey hangs) need the deadline
  checked inside long SymJ calls, or the survey run per problem in a killable
  process.
- 1.1.1.2 losses from newly loaded rules route to `(a+bx+cx^2)^p`, whose RUBI rules
  OSR lacks (`With`): expect them back when OSR converts `With` rules.

## Files here

`scripts/`: `bench.jl` (one test file, per-problem statuses: `julia --project=.
bench.jl OUT [filefilter] [nmax]`, `IDS=file` to restrict), `survey2.jl` +
`survey_driver.sh`, `classify.jl` (rules fired per timeout), `bisect112.sh`,
`top112.jl`. `data/`: per-problem results compared during the session.

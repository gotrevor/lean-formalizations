# HANDOFF — lean-formalizations (umbrella; impossibility / no-formula + classical results)

> 🎯 **ACTIVE RUN (2026-06-14, Trevor via Ren): power-tower upper half.**
> Read **`DIRECTION.md` FIRST** — it is the operator work-order and has the full
> elementary proof plan. This run discharges the two `sorry`s in
> `src/LeanFormalizations/RealAnalysis/PowerTower/Statement.lean`
> (`tower_converges`, `tower_diverges`), then self-stops (`--allow-stop`).
> Do NOT start the lower half, do NOT touch Curtis.

## State of the repo
- **Curtis 1990** — COMPLETE, axiom-clean, DONE. `NumericalSemigroups/Curtis/`.
  Do not reopen/extend/re-verify.
- **Infinite power tower (Euler 1783)** — `RealAnalysis/PowerTower/`, NEW this session,
  **scaffolded** (builds green; 2 intended `sorry`s):
  - `Defs.lean` — `tower x n` (= ⁿx, `^` = `Real.rpow`), `eInvE = exp (1/exp 1)` (= e^(1/e)),
    `tower_zero/succ/one`. Audit-faithful.
  - `Statement.lean` — audit surface. `tower_converges` (`sorry`), `tower_diverges` (`sorry`),
    `tower_converges_iff` (PROVED from the two), `endpoint_fixed_point` (PROVED).
  - `README.md` — "what to audit" + scope (upper half = `x ≥ 1`, sharp endpoint `e^(1/e)`).
  - Result: for `x>0`, `lim ⁿx` converges **iff** `x ∈ [e^(-e), e^(1/e)]`. This run does the
    `x ≥ 1` half (boundary `e^(1/e)`); lower half `[e^(-e),1)` deferred.

## This run's job (see `DIRECTION.md` for the full plan)
1. Create `RealAnalysis/PowerTower/Engine.lean`; move `endpoint_fixed_point` to `Defs.lean`.
2. Prove `tower_converges_engine` (monotone + bounded-by-e ⇒ converges to a fixed point in [1,e])
   and `tower_diverges_engine` (monotone + unbounded-by-no-fixed-point ⇒ atTop). All elementary —
   the key trick is `log L ≤ L/e` from `Real.add_one_le_exp`, giving "a fixed point forces
   `x ≤ e^(1/e)`" (no calculus).
3. Delegate the `Statement.lean` theorems to the engine; rebuild green; `#print axioms` clean.
4. Refresh this file + the two READMEs; self-stop via the sentinel (see `DIRECTION.md`).

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from a real `lake build`).
- Keep `Statement.lean` the faithful audit surface; engine lives in siblings and delegates.
- `Curtis/Lemma2.lean` lint warnings: LEAVE THEM (mathematical hypotheses + Aristotle blocks).
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue.

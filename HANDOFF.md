# HANDOFF — lean-formalizations (umbrella; impossibility / no-formula + classical results)

> ✅ **POWER-TOWER UPPER HALF: COMPLETE (2026-06-14).** The bounded run from
> `DIRECTION.md` is fully discharged. `tower_converges` and `tower_diverges` are
> PROVED (delegating to `Engine.lean`); `src/` is sorry-free; `lake build` green
> (8259 jobs); all headline theorems axiom-clean. Self-stop armed.

## State of the repo
- **Curtis 1990** — COMPLETE, axiom-clean, DONE. `NumericalSemigroups/Curtis/`.
  Do not reopen/extend/re-verify.
- **Infinite power tower (Euler 1783), upper half** — `RealAnalysis/PowerTower/`,
  **PROVED & axiom-clean** this run:
  - `Defs.lean` — `tower x n` (= ⁿx, `^` = `Real.rpow`), `eInvE = exp (1/exp 1)`
    (= e^(1/e)), `tower_zero/succ/one`, and `endpoint_fixed_point` (relocated here
    from `Statement.lean` so the engine can use it). Audit-faithful.
  - `Engine.lean` — **NEW**, the real proofs (all elementary, no calculus). Single
    analytic input is `Real.add_one_le_exp`. Key lemmas: `log_le_div_e`
    (`log L ≤ L/e`), `base_le_eInvE` (a positive fixed point forces `x ≤ e^(1/e)`),
    `tower_mono`, `tower_le_exp_one`, `exists_fixedpoint_of_bddAbove` (shared core),
    then `tower_converges_engine` / `tower_diverges_engine`.
  - `Statement.lean` — audit surface; `tower_converges` / `tower_diverges` now
    delegate (`:= …_engine`). `tower_converges_iff` (headline) PROVED from the two.
  - Verified: `#print axioms` on `tower_converges`, `tower_diverges`,
    `tower_converges_iff`, `endpoint_fixed_point` = `[propext, Classical.choice,
    Quot.sound]` — no `sorryAx`, no `native_decide`.
  - Result: for `x ≥ 1`, `lim ⁿx` converges **iff** `x ≤ e^(1/e)`.

## What is deliberately NOT done (future cycles, do not start unprompted)
- **Power-tower lower half** `e^(-e) ≤ x < 1` (oscillating regime, 2-cycle
  stability of `g(t)=x^(x^t)`). A separate scope; do not scaffold without a new
  operator directive — adding `sorry`s would reopen this completed bounded run.
- P1 constructible-numbers / doubling-the-cube (see `PENDING_WORK.md`,
  `HANDOFF-2026-06-14-1911.md`) — surveyed, never started. Natural next frontier
  if/when Trevor reopens the repo for unbounded work.

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from a real `lake build`).
- Keep `Statement.lean` the faithful audit surface; engine lives in siblings and delegates.
- `Curtis/Lemma2.lean` lint warnings: LEAVE THEM (mathematical hypotheses + Aristotle blocks).
- `push_neg` is deprecated in this toolchain (v4.29.1) → use `push Not at h`.
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue.

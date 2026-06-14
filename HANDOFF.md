# HANDOFF — lean-formalizations (umbrella; impossibility / no-formula + classical results)

> ✅ **POWER-TOWER LOWER HALF: COMPLETE & FULLY AXIOM-CLEAN (2026-06-14).**
> The mandatory `tower_converges_of_mem` (convergence on the FULL Euler interval
> `[e^(-e), e^(1/e)]`) is PROVED, and the lower-bound **crux is fully discharged —
> NO axiom**. `#print axioms tower_converges_of_mem = [propext, Classical.choice,
> Quot.sound]`. The bounded run's stop condition is met; the STRETCH `iff` is
> omitted-with-a-note (see below). Do NOT reopen the lower half.

## What this run did (2026-06-14, power-tower LOWER half)
- **`Defs.lean`**: added `eNegE = e^(-e)` + machine-checked anchor
  `endpoint_fixed_point_lower : (e^(-e))^(1/e) = 1/e`.
- **`EngineLower.lean`** (NEW): the lower-half engine, all machine-checked.
  - Scaffolding: `f` continuous & antitone, `g = f∘f` monotone, even subseq
    `a(2n)` antitone-bounded → `γ`, odd `a(2n+1)` monotone-bounded → `β`, limit
    relations `x^β=γ`/`x^γ=β`, even/odd reassembly (`tendsto_of_even_odd`).
  - **THE CRUX, fully proved (no axiom)** — `two_cycle_collapse`: no nontrivial
    2-cycle of `t↦x^t` for `e^(-e) ≤ x < 1`. Mechanism = the slope bound
    `g'(t) = (log x)²·x^(x^t)·x^t = c²·e^{c(e^{ct}+t)} ≤ |c|/e ≤ 1`
    (`exp_mul_add_ge`, the SAME `add_one_le_exp` "max of t·e^{-t}" as the upper
    half). `two_cycle_collapse_of_lt` (x > e^-e): strict contraction + Banach
    (`ContractingWith.eq_or_edist_eq_top_of_fixedPoints`).
    `two_cycle_collapse_boundary` (x = e^-e): `g'<1` off `1/e`, antitone `h=g-id`
    is `0` on `(β,γ)` ⟹ `g'=1` there ⟹ contradiction.
    **NOTE: the DIRECTION's "subtract the two tangent-line inequalities" sketch is
    mathematically INVALID** (can't subtract inequalities; the tangent-at-`y` bound
    only pins `log y` to an interval straddling `-1`). The slope/derivative bound is
    the correct mechanism. Recorded in the `EngineLower.lean` docstrings.
- **`Statement.lean`**: headline `tower_converges_of_mem` stitches upper + lower.
- Verified axiom-clean: `tower_converges_of_mem`, `two_cycle_collapse`,
  `tower_converges_lower`, `endpoint_fixed_point_lower` all
  `[propext, Classical.choice, Quot.sound]`. `lake build` green (8260 jobs).

## OMITTED (with note, NO sorry) — the sharp full-interval `iff`
`tower_converges_iff_full` is NOT shipped. The convergence half is done
(`tower_converges_of_mem`) and `x > e^(1/e)` diverges (`tower_diverges`); the
missing piece is **non-convergence for `0 < x < e^(-e)`**, which needs a genuine
*attracting* 2-cycle (`β < γ`) — proving the fixed point is repelling and the tower
from `a₀=1` avoids its stable manifold. Separate multi-lap real-analysis work;
omitted per `DIRECTION.md` (>2-lap budget). See `PENDING_WORK.md`. Natural next scope.

## State of the rest of the repo
- **Curtis 1990** — COMPLETE, axiom-clean, DONE. `NumericalSemigroups/Curtis/`.
  Do not reopen.
- **Power tower (Euler 1783), upper half** — `RealAnalysis/PowerTower/Engine.lean`,
  PROVED & axiom-clean (`tower_converges` / `tower_diverges` / `tower_converges_iff`).
- **Power tower lower half** — DONE this run (see above).
- P1 constructible-numbers / doubling-the-cube — surveyed, never started
  (`PENDING_WORK.md`). Natural next frontier for a future unbounded run.

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from a real `lake build`).
- Keep `Statement.lean` the faithful audit surface; engines live in siblings.
- `Curtis/Lemma2.lean` lint warnings: LEAVE THEM.
- `push_neg` is deprecated (v4.29.1) → use `push Not at h`. `le_or_lt` gone → `lt_or_ge`.
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

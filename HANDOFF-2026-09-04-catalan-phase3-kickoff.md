# HANDOFF — 2026-09-04 — Catalan salvage: PHASE 3 kickoff (the generic frame)

## 👉 Read `DIRECTION.md` first — Phase 3 section is the objective.

**State at kickoff (branch `catalan`):**
- Phase 1 (`Tails`, `Residual`, `TwoAdic`, `Statement`) is **green and axiom-clean**, merged to
  `main`.  Do not touch those files except to *use* them.
- Phase 2's candidate repairs N1/N2 were **refuted on the host** by an exact probe (`G` formal,
  true integerizer, real size at the true `G`): the integer grows `≈ 3.4·S·B` in `log10`.  Detail
  in `DIRECTION.md` "Killed thread".  Nothing for a lap to do there.
- **Phase 3 = `Frame.lean`**: 14 named `sorry` leaves, compiles (`lake env lean` clean apart from
  the `sorry` warnings).  Each frozen statement was hand-derived and numerically verified before
  planting (`resid_tail_eq` to 55 digits at four parameter points; `resid_fakeTail_den` exactly).
  If a statement is nonetheless wrong, FIX it loudly (commit message + this file's successor).

## Order
W (`irrational_of_forms`) → E (`oddLcm_pos`, `odd_dvd_oddLcm`, `resid_fakeTail_den`,
`det_resid_fakeTail_den`, `abs_det_ge_of_rational`) → **sink edge**
`catalan_irrational_of_smallForms` → D (`alt_choose_sum_inv_eq`, `alt_choose_sum_inv_sq_eq`,
`lin_dvd_bigPi`, `redPi_mul_lin`, `natDegree_redPi_le`, `alt_choose_sum_div_sq`,
**`resid_tail_eq`**).  Proof plans are in the module docstring.

## Technique pointers from Phase 1 (same repo, same mathlib)
- Finite-difference annihilation: `fwdDiff_iter_eq_zero_of_degree_lt` + `fwdDiff_iter_eq_sum_shift`
  (already wrapped as `alt_choose_sum_eval_eq_zero`).
- 2-integrality toolkit `OddDen` in `TwoAdic.lean` — the E leaves want the same shape for an
  arbitrary integer denominator (`∃ z : ℤ, x = z / d`); consider a small `IsMulInt d x` closure
  (add/mul/sum/prod) rather than fighting `Rat.den` directly.
- `push_neg` is deprecated → `push Not at h`.  `lake env lean <file>` from the repo root.
- `Polynomial` division: `bigPi B / lin j` is `EuclideanDomain` division in `F[X]`; with
  `lin_dvd_bigPi` it is exact (`EuclideanDomain.mul_div_cancel'`).

## ⚠️ Standing rule
Nothing here proves `Irrational catalanConst`; `SmallForms` is a hypothesis, numerically false for
these weights.  A lap that "proves" `SmallForms` has proved something false — stop and report.

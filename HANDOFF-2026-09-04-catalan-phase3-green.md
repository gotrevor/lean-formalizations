# HANDOFF — 2026-09-04 — Catalan salvage: PHASE 3 GREEN (`Frame.lean` sorry-free, axiom-clean)

## State (branch `catalan`, HEAD `7d84bfd`)
All 14 leaves of `Frame.lean` are proved.  `lake build` green (8661 jobs).  `#print axioms` on
`irrational_of_forms`, `abs_det_ge_of_rational`, `catalan_irrational_of_smallForms`,
`alt_choose_sum_div_sq`, `resid_tail_eq` = `[propext, Classical.choice, Quot.sound]`.
The whole `src/LeanFormalizations/NumberTheory/Catalan/` directory is sorry-free.

Commits this lap: `3266127` (W + E + sink edge), `4577241` (D1, D2, D4, redPi trio), `7d84bfd` (D5).

## ⚠️ Statement fix (loud, per Phase-1 discipline)
`resid_fakeTail_den` (E1) and `det_resid_fakeTail_den` (E2) gained the hypothesis `(hSB : S ≤ B)`.
The frozen E1 was FALSE without it: exact rational probe at `B = 0, S = 7, a/q = 1` leaves a
denominator `15` after scaling by `q·L²` (the pole `1/(2(i+j+1)+1)` is only absorbed by `Π_i`
when `j+1 ≤ B`).  E3 and the sink already assumed `S < B`; nothing downstream changed.  All
other frozen statements were proved exactly as planted.

## What each leaf needed (for reuse)
- W: `Irrational` as `∉ range Rat.cast`; `Rat.cast_def`; `Tendsto.eventually (gt_mem_nhds …)`
  against `Int.one_le_abs`.
- E: an `IsInt (x : ℚ) := ∃ z : ℤ, x = z` closure toolkit (add/mul/sub/pow/sum/prod +
  `isInt_natCast_div` for `d ∣ n`); `oddLcm_dvd_oddLcm` (monotone); `odd_dvd_normaliser`;
  `isInt_mul_fakeTail`; Leibniz `Matrix.det_apply` + `Matrix.det_smul` with
  `d ^ S = d ^ Fintype.card (Fin S)`.
- Sink: `resid_map` (`resid` commutes with a ring hom), `Matrix.submatrix_map`,
  `RingHom.map_det`, `Rat.cast_lt` after explicit `← Rat.cast_*` rewrites (avoid `push_cast`
  on the whole inequality — it over-normalises to `NNRat.divNat`).
- D1/D2: induction on `n` in `∀ x` form; Pascal step `alt_choose_sum_succ` (peel `i = 0` with
  `sum_range_succ'`, kill `C(n,n+1)`); products via `prod_range_succ` / `prod_range_succ'`,
  then `field_simp; push_cast [Nat.factorial_succ]; ring`.
- D4: `exists_taylor_two` (`p = (X−a)^2 Q + p'(a)(X−a) + p(a)` via `divByMonic` twice,
  `modByMonic_X_sub_C_eq_C_eval`, `natDegree_divByMonic`), `alt_choose_sum_eval_eq_zero'`
  (allows `n = 0` when `Q = 0`), then D1 + D2.
- D5: `normaliser_div_eq_redPi_eval`, `Summable.tsum_finsetSum` (the sum/tsum swap),
  `tsum_congr`, termwise `alt_choose_sum_div_sq` with `c_r = j + r + 3/2`.

## Standing rule (unchanged)
`SmallForms` is a `def … : Prop`, numerically FALSE for Sun's weights (host ledger probe:
`log|N_B| ≈ +3.4·S·B`).  Nothing in the repo proves or claims `Irrational catalanConst`.
`catalan_irrational_of_smallForms` is the kernel-checked sink edge: the ledger is the only
missing thing, and `abs_det_ge_of_rational` is the floor it must beat.

## Next (for an altitude lap; this run's scope is complete)
- Merge `catalan` → `main` (host).
- Any v2 construction drops into `resid` / `oddLcm` and re-runs `resid_tail_eq`'s closed form
  for its real-place estimate; that estimate stays a probe question, not a Lean question.

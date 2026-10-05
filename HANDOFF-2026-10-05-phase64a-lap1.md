# HANDOFF phase 64a lap 1 (2026-10-05)

Target: every `sorry` in `Mills/SaitoTypeBTheta.lean`.

## Done (no sorryAx; `#print axioms` block at the end of the file)
- `ingham_of_bhp`.
- `xi_shift_transcendental_of_shortInterval'`: E+ from `PrimesShortInterval θ`, `0 < θ < 5/9`, + Dubickas2022.
- `xi_shifted_transcendental_of_shortInterval'`: Theorem E (s = −2) on the same inputs.
- The frozen `xi_shift_transcendental_ingham` and `xi_shifted_transcendental_ingham` are wired from the frozen
  `xi_shift_transcendental_of_shortInterval`.  That theorem is proved for θ < 5/9 and has ONE `sorry`, on the branch θ ∈ [5/9, 2/3).
- θ-parametric machinery: `Mills/SaitoTypeBThetaParts.lean`.  BHP theorems are untouched apart from one
  statement-preserving refactor: `xi_shift_transcendental_classical` now calls the new
  `xi_shift_transcendental_of_shift_disj`.

## Why 2/3 was not reached (the step that forces 5/9)
The chain step (`bhp_step_theta`) works for any θ < 2/3 with ratio ρ ∈ (1/(1−θ), 3).  Saito (5.17) gives
decay μ ≤ (1−θ)ρ − 1 < 2 − 3θ.  The Baker-free degree bound (`card_le_two_of_records_theta`,
`card_mul_le_shift_theta`) is (ℓ − 1)μ ≤ 1.  The endgame needs ℓ = 3 (`e2_zero_of_nonrecord`,
`not_natDegree_two`, trace rigidity), so μ > 1/3, i.e. θ < 5/9.  For θ ≥ 5/9 a Pisot power of degree 4 or more is not excluded.
Ingham's exponent 5/8 is in that gap, so the Ingham corollaries stay conditional on the open branch.
Open node: `SaitoTypeBTheta.ShiftPisotDegreeLeThree`, plus a Maze row.

## Next
Exclude Pisot degree ℓ ≥ 4 for the E+ orbit without Baker.  `PENDING_WORK.md` (top entry) has the details.
Then phase 64b, which is queued in DIRECTION.md.

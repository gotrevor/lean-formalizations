# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`, 2026-06-19)

**Read `DIRECTION.md` first.** Unbounded expedition to prove `davies_kakeya_2d :
KakeyaSetConjectureDim 2` (planar Kakeya, Davies 1971). The whole job is the lower bound
`two_le_dimH`. Lane: only `src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/`.

## State — **K1+K2+K3+K4 COMPLETE + axiom-clean. K5 reduced.** One `sorry` left.
`lake build` green (8294 jobs). The ONLY open `sorry` in the Kakeya thread:
- `Engine.lean : hausdorffMeasure_pos_of_isKakeya` — now reduced (K5 brick 1) to exactly
  `Frostman.FrostmanMeasureExists S d` = *construct a Frostman measure of every exponent `d<2`*.

### Done — the whole Córdoba `L²` content ladder
- **K1 (`Engine`).** `two_le_dimH` ⟸ `hausdorffMeasure_pos_of_isKakeya` (Frostman + `ENNReal` density).
- **K2 (`Tube`).** δ-tube infra; `volume_tube_le` (`≤6δ`), `volume_tube_ge` (`≥2δ`),
  `volume_inter_tube_le` (overlap `≤12δ²/(s+δ)`, `s=|sin∠|`). 100% axiom-clean.
- **K3 (`Discretize`, `Directions`).** `exists_tube_subset_thickening`; trig net `dir θ=(cos,sin)`
  with `norm_dir`/`dir_det`(`=sin(φ−θ)`)/`dir_sep`(Jordan `(2/π)|φ−θ|≤|det|`)/`exists_tube_family`;
  K2↔K3 interface `volume_inter_dirTube_le` (overlap `≤6πδ/(|k−j|+1)`).
- **K4 (`Cordoba`, `CordobaL2`).** Harmonic `double_sum_le_log` (`∑1/(|k−j|+1)≤2n(1+logn)`),
  geometric `sum_overlap_le`, numerator `sum_tube_ge`, ∫ identities `lintegral_sum_indicator` /
  `lintegral_sq_sum_indicator`, Cauchy–Schwarz `lintegral_sq_le_measure_mul` (Hölder p=q=2),
  `volume_thickening_mul_ge`, and the capstone **`volume_thickening_log_ge`:
  `1 ≤ vol(Sδ)·12π(1+log(1/δ))`** (δ≤1/2) — i.e. `vol(Sδ) ≳ 1/log(1/δ)`.
- **K5 brick 1 (`Frostman`).** `hausdorffMeasure_ne_zero_of_frostman_const` (mathlib
  `Measure.le_hausdorffMeasure`, rescaled by `C⁻¹`) ⟹ Engine's sorry = `FrostmanMeasureExists S d`.

## Next brick — K5 brick 2: construct the Frostman measure (the deep multi-lap core).
Single-scale content does NOT give Hausdorff dim (box dim ≥ Hausdorff dim). Build the measure from
`volume_thickening_log_ge` across dyadic scales. **Three attack paths in `PENDING_WORK.md` §A**;
recommended path 2 (dyadic discretized-Kakeya cover, bypasses building a measure). See newest
`HANDOFF-2026-06-19-0541.md` for the detailed bootstrap.

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- `dimH_le_two`, `two_le_dimH`, all of `Tube`/`Directions`/`Cordoba`/`CordobaL2`/`Frostman` are done.
- Commit every green build; never push; never fake green; disclosed `sorry` only.

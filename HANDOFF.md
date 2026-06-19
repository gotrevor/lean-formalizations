# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`, 2026-06-19)

**Read `DIRECTION.md` first.** Unbounded expedition to prove `davies_kakeya_2d :
KakeyaSetConjectureDim 2` (planar Kakeya, Davies 1971). The whole job is the lower bound
`two_le_dimH`. Lane: only `src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/`.

## State (this lap delivered K1 + most of K2, all axiom-clean)
`lake build` green (8289 jobs). The ONLY `sorry`s in the Kakeya thread:
- `Engine.lean:hausdorffMeasure_pos_of_isKakeya` — the analytic crux `∀ d<2, μH[d] S ≠ 0`.
- `Tube.lean:volume_inter_tube_le` — the two-tube overlap bound.

### Done this lap
- **K1 (`Engine.lean`).** `two_le_dimH` is now an axiom-clean wrapper: Frostman
  (`le_dimH_of_hausdorffMeasure_ne_zero`) + `ENNReal.le_of_forall_nnreal_lt` reduce it to the
  concrete measure-positivity crux `hausdorffMeasure_pos_of_isKakeya` (the lone analytic `sorry`).
- **K2 tube infrastructure (`Tube.lean`, new).** `tube a v δ := cthickening δ (affineSegment ℝ a (a+v))`.
  All axiom-clean: `exists_core_witness`, `tube_transverse` (|⟪u,x-a⟫|≤δ, u⊥v), `tube_longitudinal`
  (⟪v,x-a⟫∈[-δ,1+δ]), `tube_subset_coordBox`.
- **`volume_tube_le` PROVEN** (single δ-tube area ≤ 6δ): full orthonormal-frame machinery —
  `orthonormal_pair`/`frame`/`frame_zero`/`frame_one`, `volume_coordBox` (exact box area via the
  measure-preserving `ofLp ∘ frame.repr ∘ (·-a)` → product box → `volume_pi_pi`·`Real.volume_Icc`),
  `perp`/`norm_perp`/`inner_perp`.
- **`inter_tube_subset_parallelogram`** — overlap ⊆ two-slab parallelogram (from `tube_transverse`×2).

## Next brick — finish `volume_inter_tube_le` (overlap bound). PATH IS DE-RISKED.
Goal: `vol(tube a v δ ∩ tube b w δ) ≲ δ²/(‖v-w‖+δ)`. Two regimes:
1. **Near-parallel `‖v-w‖ ≤ δ`:** FREE — `vol(overlap) ≤ vol(tube a v δ) ≤ 6δ` (`volume_tube_le` +
   `measure_mono inter_subset_left`), and `δ²/(‖v-w‖+δ) ≥ δ/2`, so any `C ≥ 12` works.
2. **Transversal `‖v-w‖ > δ`:** need the parallelogram area. Reduce via
   `inter_tube_subset_parallelogram` to `vol{|⟪perp v,x-a⟫|≤δ ∧ |⟪perp w,x-b⟫|≤δ} = (2δ)²/|det[v,w]|`,
   where `det[v,w] = v 0 * w 1 - v 1 * w 0` (= sin∠). Then `|det[v,w]| ≳ ‖v-w‖` for unit `v,w`
   on a half-circle (CARE: fails for antipodal `w=-v`; the Kakeya direction-net avoids that, or split).

**Confirmed mathlib lemmas for step 2 (all exist in v4.29.1):**
- `Matrix.toEuclideanLin M : Plane →ₗ Plane`, `(toEuclideanLin M x) i = (M.mulVec x) i` via
  `Matrix.toEuclideanLin_apply` / `ofLp_toEuclideanLin_apply`; `(M.mulVec x) i = ∑ j, M i j * x j`
  = `⟪row i, x⟫` (real, with the `⟪a,b⟫ = b*a` rfl orientation already used in `inner_perp`).
- `LinearMap.det (Matrix.toEuclideanLin M) = M.det` — proof: `LinearMap.det_toLpLin 2 M`
  (found by `exact?`). `M.det` for the 2×2 `!![pv0,pv1; pw0,pw1]` via `Matrix.det_fin_two`.
- `MeasureTheory.Measure.addHaar_preimage_linearMap (hdet : LinearMap.det f ≠ 0) (s) :
  volume (f ⁻¹' s) = ENNReal.ofReal |(LinearMap.det f)⁻¹| * volume s`.
- Box volume `(2δ)²`: same `ofLp`/`volume_pi_pi`/`Real.volume_Icc` pattern as `volume_coordBox`
  (the box is translated — translation-invariant interval lengths).

Build `L := toEuclideanLin !![perp v 0, perp v 1; perp w 0, perp w 1]`; show the parallelogram
`= L ⁻¹' box'` (`(L x) 0 = ⟪perp v,x⟫`, `(L x) 1 = ⟪perp w,x⟫`); apply `addHaar_preimage_linearMap`.
See `PENDING_WORK.md` for the three-path inventory; `PLAN.md` for the K2–K5 ladder beyond.

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- `dimH_le_two`, `two_le_dimH`, `volume_tube_le` are done — do not touch.
- Commit every green build; never push; never fake green; disclosed `sorry` only.

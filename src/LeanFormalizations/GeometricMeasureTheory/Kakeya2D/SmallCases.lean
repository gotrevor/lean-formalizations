/-
# Kakeya set conjecture — the small-dimensional cases `n = 0, 1`

Companions to the planar headline `davies_kakeya_2d : KakeyaSetConjectureDim 2` (Davies 1971,
`Statement.lean`). The conjecture `KakeyaSetConjectureDim n` ("every Kakeya set in `ℝⁿ` has Hausdorff
dimension `n`") is **elementary** for `n ≤ 1` and is proved here, axiom-clean, so the
`KakeyaSetConjectureDim` family is machine-checked for `n = 0, 1, 2` (only `n = 3`, Wang–Zahl 2025, and
`n ≥ 4` remain open). These are genuine cases of the conjecture, not anti-vacuity anchors.

* `n = 0`: `EuclideanSpace ℝ (Fin 0)` is a point — there are no unit vectors, so `IsKakeya` is vacuous;
  every set has `dimH = 0 = finrank`.
* `n = 1`: the only content is the **lower** bound `1 ≤ dimH S`, which holds in EVERY dimension `n ≥ 1`
  (`one_le_dimH_of_isKakeya`): a Kakeya set contains a unit segment, the isometric image of `[0,1]`
  under `t ↦ a + t·v` (`‖v‖ = 1`), so `dimH S ≥ dimH (f '' Icc 0 1) = dimH (Icc 0 1) = 1`. The upper
  bound is the trivial `dimH ≤ finrank = 1`.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Defs

open Set MeasureTheory Module
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **A Kakeya set in `ℝⁿ` (`n ≥ 1`) has Hausdorff dimension at least `1`.** The trivial lower bound,
valid in every dimension: `IsKakeya S` supplies, for the given unit vector `v`, a base point `a` whose
unit segment `affineSegment ℝ a (a + v)` lies in `S`. That segment is the image of `[0,1]` under the
isometry `t ↦ a + t·v` (an isometry exactly because `‖v‖ = 1`), so it has Hausdorff dimension
`dimH (Icc 0 1) = 1`; monotonicity of `dimH` finishes. -/
theorem one_le_dimH_of_isKakeya {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) (h : IsKakeya S) : 1 ≤ dimH S := by
  obtain ⟨a, ha⟩ := h v hv
  -- the unit segment as the image of `[0,1]` under `t ↦ a + t·v`
  have hseg : affineSegment ℝ a (a + v) = (fun t : ℝ => a + t • v) '' Set.Icc 0 1 := by
    rw [affineSegment]
    refine Set.image_congr (fun t _ => ?_)
    rw [AffineMap.lineMap_apply_module', show (a + v) - a = v from by abel]
    abel
  -- `t ↦ a + t·v` is an isometry (since `‖v‖ = 1`)
  have hiso : Isometry (fun t : ℝ => a + t • v) :=
    Isometry.of_dist_eq fun x y => by
      rw [Real.dist_eq, dist_eq_norm,
        show (a + x • v) - (a + y • v) = (x - y) • v from by rw [sub_smul]; abel,
        norm_smul, hv, mul_one, Real.norm_eq_abs]
  -- hence the segment has Hausdorff dimension `1`
  have hdimseg : dimH (affineSegment ℝ a (a + v)) = 1 := by
    rw [hseg, hiso.dimH_image,
      Real.dimH_of_mem_nhds (Icc_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))]
    rw [Module.finrank_self, Nat.cast_one]
  calc (1 : ℝ≥0∞) = dimH (affineSegment ℝ a (a + v)) := hdimseg.symm
    _ ≤ dimH S := dimH_mono ha

/-- **A Kakeya set in `ℝⁿ` (`n ≥ 1`) has strictly positive Hausdorff dimension.** Immediate corollary of
`one_le_dimH_of_isKakeya` (`0 < 1 ≤ dimH S`); a uniform non-degeneracy statement across all dimensions. -/
theorem dimH_pos_of_isKakeya {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) (h : IsKakeya S) : 0 < dimH S :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) (one_le_dimH_of_isKakeya hv h)

/-- **The Kakeya conjecture in dimension `0`.** `EuclideanSpace ℝ (Fin 0)` is a single point, so every
set has `dimH = 0` (and `IsKakeya` is vacuously true — there is no unit vector). Axiom-clean. -/
theorem kakeya_0d : KakeyaSetConjectureDim 0 := by
  intro S _
  refine le_antisymm ?_ (by simp)
  calc dimH S ≤ dimH (univ : Set (EuclideanSpace ℝ (Fin 0))) := dimH_mono (subset_univ _)
    _ = (finrank ℝ (EuclideanSpace ℝ (Fin 0)) : ℝ≥0∞) := Real.dimH_univ_eq_finrank _
    _ = ((0 : ℕ) : ℝ≥0∞) := by rw [finrank_euclideanSpace_fin]

/-- **The Kakeya conjecture in dimension `1`.** Every Kakeya set in `ℝ¹` has Hausdorff dimension `1`:
the upper bound is the trivial `dimH ≤ finrank = 1`, and the lower bound is `one_le_dimH_of_isKakeya`
applied to the unit vector `e₀`. Axiom-clean (`#print axioms = [propext, Classical.choice, Quot.sound]`). -/
theorem kakeya_1d : KakeyaSetConjectureDim 1 := by
  intro S h
  refine le_antisymm ?_ ?_
  · calc dimH S ≤ dimH (univ : Set (EuclideanSpace ℝ (Fin 1))) := dimH_mono (subset_univ _)
      _ = (finrank ℝ (EuclideanSpace ℝ (Fin 1)) : ℝ≥0∞) := Real.dimH_univ_eq_finrank _
      _ = ((1 : ℕ) : ℝ≥0∞) := by rw [finrank_euclideanSpace_fin]
  · have hv : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ))‖ = 1 := by
      rw [PiLp.norm_single]; exact norm_one
    have := one_le_dimH_of_isKakeya hv h
    rwa [Nat.cast_one]

end LeanFormalizations.Kakeya2D

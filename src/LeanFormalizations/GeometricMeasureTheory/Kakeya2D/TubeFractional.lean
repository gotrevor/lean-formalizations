/-
# Fractional δ-tube area lower bound (ladder K5, localized-Córdoba numerator)

`Tube.lean`'s `volume_tube_ge` lower-bounds the area of a δ-tube about a *unit* segment by `2δ`.
The multi-scale upgrade of the Córdoba content bound (K5, the dominant-scale "localized Córdoba"
count) needs the **fractional** version: a δ-tube about a segment of *length* `‖v‖` (possibly `< 1`)
has area `≥ 2δ‖v‖`. After the dyadic double-pigeonhole reduces an arbitrary cover to a dominant
scale, the covered sub-segments have only a *fraction* `w = ‖v‖ < 1` of unit length, and this `w`
factor is exactly what survives into the final content bound `∑ediam^d ≳ 2^{j*(2-d)}`.

The proof reuses the unit-frame machinery of `Tube.lean` *verbatim* for the normalised direction
`e = ‖v‖⁻¹ • v`: the segment `[a, a+v] = [a, a + ‖v‖•e]` carries the `‖v‖ × 2δ` frame rectangle
`{x | ⟪e,x-a⟫ ∈ [0,‖v‖], ⟪perp e,x-a⟫ ∈ [-δ,δ]}`, whose exact area `volume_frame_box` is
`‖v‖·2δ`. No new change-of-variables is needed. See `PENDING_WORK.md` §A. -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Tube

open Set MeasureTheory Metric RealInnerProductSpace
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- The unit normalisation `e = ‖v‖⁻¹ • v` of a nonzero planar vector has norm `1`. -/
theorem norm_normalize {v : Plane} (hv : v ≠ 0) : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- **Fractional frame sub-rectangle ⊆ tube.** For a nonzero `v` with unit normalisation
`e = ‖v‖⁻¹•v`, the `‖v‖ × 2δ` rectangle (longitudinal coordinate in `[0,‖v‖]`, transverse in
`[-δ,δ]`) sits inside the δ-tube about `[a, a+v]`: each such point is `δ`-close to the core point
`a + s•e = a + (s/‖v‖)•v`, which lies on the segment. -/
theorem fracBox_subset_tube {a v : Plane} (hv : v ≠ 0) {δ : ℝ} :
    {x : Plane | ⟪(‖v‖⁻¹ : ℝ) • v, x - a⟫ ∈ Icc (0 : ℝ) ‖v‖ ∧
        ⟪perp ((‖v‖⁻¹ : ℝ) • v), x - a⟫ ∈ Icc (-δ) δ} ⊆ tube a v δ := by
  intro x hx
  obtain ⟨⟨hs0, hs1⟩, hr0, hr1⟩ := hx
  have hw0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set e : Plane := (‖v‖⁻¹ : ℝ) • v with he
  have he1 : ‖e‖ = 1 := norm_normalize hv
  set s : ℝ := ⟪e, x - a⟫ with hsdef
  set r : ℝ := ⟪perp e, x - a⟫ with hrdef
  refine mem_cthickening_of_dist_le x (a + s • e) δ _ ?_ ?_
  · -- the core point `a + s•e` lies on the segment, as `a + (s/‖v‖)•v`
    rw [affineSegment_eq, mem_image]
    refine ⟨s / ‖v‖, ⟨div_nonneg hs0 hw0.le, ?_⟩, ?_⟩
    · rw [div_le_one hw0]; exact hs1
    · show a + (s / ‖v‖) • v = a + s • e
      rw [he, smul_smul, div_eq_mul_inv]
  · -- transverse distance is `|r| ≤ δ`
    have hdec : x - a = s • e + r • perp e := by
      rw [hsdef, hrdef]; exact frame_decomp he1 a x
    have hd : x - (a + s • e) = r • perp e := by
      rw [show x - (a + s • e) = (x - a) - s • e by abel, hdec]; abel
    rw [dist_eq_norm, hd, norm_smul, norm_perp he1, mul_one, Real.norm_eq_abs, abs_le]
    exact ⟨hr0, hr1⟩

/-- **Fractional single-tube area lower bound.** A δ-tube about a segment of *length* `‖v‖` has area
`≥ 2δ‖v‖`. Generalises `volume_tube_ge` (the `‖v‖ = 1` case) and is the numerator input to the
dominant-scale localized Córdoba count. -/
theorem volume_tube_ge_frac {a v : Plane} (hv : v ≠ 0) {δ : ℝ} :
    ENNReal.ofReal (2 * δ * ‖v‖) ≤ volume (tube a v δ) := by
  have hw0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have he1 : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_normalize hv
  calc ENNReal.ofReal (2 * δ * ‖v‖)
      = volume (Icc (0 : ℝ) ‖v‖) * volume (Icc (-δ) δ) := by
        rw [Real.volume_Icc, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul hw0]
        congr 1
        ring
    _ = volume {x : Plane | ⟪(‖v‖⁻¹ : ℝ) • v, x - a⟫ ∈ Icc (0 : ℝ) ‖v‖ ∧
          ⟪perp ((‖v‖⁻¹ : ℝ) • v), x - a⟫ ∈ Icc (-δ) δ} :=
        (volume_frame_box he1 a measurableSet_Icc measurableSet_Icc).symm
    _ ≤ volume (tube a v δ) := measure_mono (fracBox_subset_tube hv)

/-- **Sub-segment containment.** For `w ∈ [0,1]`, the segment `[a, a+w•v]` is a sub-segment of
`[a, a+v]` (its points `a + t•(w•v) = a + (tw)•v` with `tw ∈ [0,1]`). -/
theorem affineSegment_smul_subset {a v : Plane} {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    affineSegment ℝ a (a + w • v) ⊆ affineSegment ℝ a (a + v) := by
  intro x hx
  rw [affineSegment_eq, mem_image] at hx ⊢
  obtain ⟨t, ht, heq⟩ := hx
  refine ⟨t * w, ⟨mul_nonneg ht.1 hw0, mul_le_one₀ ht.2 hw0 hw1⟩, ?_⟩
  rw [← heq, smul_smul]

/-- **Fractional tube ⊆ full tube.** For `w ∈ [0,1]`, the δ-tube about the length-`w‖v‖` sub-segment
`[a, a+w•v]` is contained in the δ-tube about `[a, a+v]`. This is the geometric input to the
**localized-Córdoba denominator**: the overlap of two *fractional* tubes is bounded by the overlap of
the corresponding *full* tubes (`vol(Tⱼᶠ ∩ Tₖᶠ) ≤ vol(Tⱼ ∩ Tₖ)`), so the existing full-tube overlap
estimate `volume_inter_dirTube_le` transfers verbatim to the dominant-scale fractional count. -/
theorem tube_smul_subset {a v : Plane} {w δ : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    tube a (w • v) δ ⊆ tube a v δ := by
  simp only [tube_def]
  exact cthickening_subset_of_subset δ (affineSegment_smul_subset hw0 hw1)

end LeanFormalizations.Kakeya2D

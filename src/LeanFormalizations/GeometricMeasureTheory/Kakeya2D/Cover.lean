/-
# The Hausdorff content lower bound (ladder K5, the honest cover route)

The Córdoba content bound (K4, `volume_thickening_log_ge`) gives `vol(Sδ) ≳ 1/log(1/δ)` at every
scale — a *Minkowski-content* statement, which by itself does **not** pin the Hausdorff dimension
(box dimension ≥ Hausdorff dimension always). The previous brick (`Frostman.lean`) packaged the
mass-distribution principle, reducing the crux to *constructing a measure* — which forces a weak-*
limit of normalised tube masses, a heavy piece of measure theory.

This file takes the **dual, measure-free route**: it reduces `μH[d] S ≠ 0` directly to a uniform
**Hausdorff content lower bound** —

  `∃ r > 0, ∃ c ≠ 0, ∀ countable cover `S ⊆ ⋃ tₙ` with `ediam(tₙ) ≤ r`, `∑ₙ ediam(tₙ)^d ≥ c`.

via mathlib's covering formula `hausdorffMeasure_apply`. This is the most faithful form of Córdoba's
argument: there is no measure to build; the entire remaining content is a covering/pigeonhole
estimate fed by the K4 single-scale bound. The deep multi-scale combinatorics (a dyadic pigeonhole
reducing an arbitrary cover to a dominant scale, then the single-scale tube count) is what remains.

Reference: Mattila, *Geometry of Sets and Measures*, §4–5 (Hausdorff content, net measures);
A. Córdoba (1977). -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.CordobaL2
import Mathlib.MeasureTheory.Measure.Hausdorff

open Set MeasureTheory
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **Hausdorff content lower bound ⟹ positive Hausdorff measure (raw form).** If there is a scale
`r > 0` and a positive constant `c` such that *every* countable cover of `S` by sets of diameter
`≤ r` has `∑ₙ ⨆_{tₙ ≠ ∅} ediam(tₙ)^d ≥ c`, then `μH[d] S ≠ 0`.

This is the exact shape of mathlib's covering formula `hausdorffMeasure_apply`: the supremum over `r`
of the infimum over covers is `≥ c > 0`. -/
theorem hausdorffMeasure_ne_zero_of_content_bound {S : Set Plane} {d : ℝ}
    {r : ℝ≥0∞} (hr : 0 < r) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hbound : ∀ t : ℕ → Set Plane, S ⊆ ⋃ n, t n → (∀ n, Metric.ediam (t n) ≤ r) →
        c ≤ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) :
    μH[d] S ≠ 0 := by
  have hge : c ≤ μH[d] S := by
    rw [Measure.hausdorffMeasure_apply]
    refine le_trans ?_
      (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
        ⨅ (t : ℕ → Set Plane) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) r hr)
    exact le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => hbound t hcov hdiam
  exact fun hzero => hc (le_antisymm (hzero ▸ hge) (zero_le c))

/-- **Hausdorff content lower bound ⟹ positive Hausdorff measure (diameter form, `d > 0`).** The
convenient downstream form: the cover hypothesis is stated with the *bare* sum `∑ₙ ediam(tₙ)^d`
(no `Nonempty` guard). For `d > 0` the guard is free — an empty piece has `ediam = 0` and
`0^d = 0` — so the two sums agree termwise. -/
theorem hausdorffMeasure_ne_zero_of_diam_content {S : Set Plane} {d : ℝ} (hd : 0 < d)
    {r : ℝ≥0∞} (hr : 0 < r) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hbound : ∀ t : ℕ → Set Plane, S ⊆ ⋃ n, t n → (∀ n, Metric.ediam (t n) ≤ r) →
        c ≤ ∑' n, Metric.ediam (t n) ^ d) :
    μH[d] S ≠ 0 := by
  refine hausdorffMeasure_ne_zero_of_content_bound hr hc (fun t hcov hdiam => ?_)
  refine le_trans (hbound t hcov hdiam) (ENNReal.tsum_le_tsum (fun n => ?_))
  by_cases hne : (t n).Nonempty
  · exact le_iSup (fun _ : (t n).Nonempty => Metric.ediam (t n) ^ d) hne
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hd]
    exact zero_le _

/-- **The remaining deep obligation (K5 core), as a `Prop`.** A *Hausdorff content lower bound* of
exponent `d` for `S`: a scale `r > 0` and a positive constant `c` such that every countable cover of
`S` by sets of diameter `≤ r` has `∑ₙ ediam(tₙ)^d ≥ c`. For a planar Kakeya set this holds for every
`d < 2` (Córdoba / Davies); `hausdorffMeasure_ne_zero_of_diam_content` turns it into `μH[d] S ≠ 0`. -/
def HausdorffContentBound (S : Set Plane) (d : ℝ) : Prop :=
  ∃ r : ℝ≥0∞, 0 < r ∧ ∃ c : ℝ≥0∞, c ≠ 0 ∧
    ∀ t : ℕ → Set Plane, S ⊆ ⋃ n, t n → (∀ n, Metric.ediam (t n) ≤ r) →
      c ≤ ∑' n, Metric.ediam (t n) ^ d

/-- The K5 reduction, packaged: a Hausdorff content lower bound of exponent `d > 0` ⟹
`μH[d] S ≠ 0`. -/
theorem hausdorffMeasure_ne_zero_of_contentBound {S : Set Plane} {d : ℝ} (hd : 0 < d)
    (h : HausdorffContentBound S d) : μH[d] S ≠ 0 := by
  obtain ⟨r, hr, c, hc, hbound⟩ := h
  exact hausdorffMeasure_ne_zero_of_diam_content hd hr hc hbound

end LeanFormalizations.Kakeya2D

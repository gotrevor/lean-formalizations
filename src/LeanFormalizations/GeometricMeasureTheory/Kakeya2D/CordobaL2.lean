/-
# The Córdoba `L²` integral identities (ladder K4, bridge to Cauchy–Schwarz)

The Córdoba estimate lower-bounds `vol(Sδ)` by Cauchy–Schwarz applied to the tube-counting
function `f = ∑ₖ 1_{Tₖ}`. This file proves the two identities that turn the *integrals* of `f`
and `f²` into the *geometric sums* already bounded in `Cordoba.lean`:

* `lintegral_sum_indicator`    — `∫ f  = ∑ₖ vol(Tₖ)`            (numerator, bounded below by `sum_tube_ge`);
* `lintegral_sq_sum_indicator` — `∫ f² = ∑_{j,k} vol(Tⱼ ∩ Tₖ)`  (denominator, bounded above by `sum_overlap_le`).

The remaining Cauchy–Schwarz step `(∫ f)² ≤ vol(Sδ) · ∫ f²` (Hölder `p = q = 2` against `1_{Sδ}`,
since `f` is supported in `Sδ`) then yields `vol(Sδ) ≳ 1/log(1/δ)`. See `PLAN.md` (K4).

Reference: A. Córdoba (1977). -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Cordoba

open Finset MeasureTheory
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **Numerator integral.** `∫ (∑ₖ 1_{Tₖ}) = ∑ₖ vol(Tₖ)` — integrate the finite sum of indicators
termwise (`lintegral_finset_sum`, `lintegral_indicator_one`). -/
theorem lintegral_sum_indicator (T : ℕ → Set Plane) (hT : ∀ k, MeasurableSet (T k)) (N : ℕ) :
    ∫⁻ x, ∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x ∂volume
      = ∑ k ∈ range N, volume (T k) := by
  rw [lintegral_finset_sum _ (fun k _ => measurable_one.indicator (hT k))]
  exact sum_congr rfl (fun k _ => lintegral_indicator_one (hT k))

/-- **Denominator integral.** `∫ (∑ₖ 1_{Tₖ})² = ∑_{j,k} vol(Tⱼ ∩ Tₖ)` — expand the square as a
double sum (`sum_mul_sum`), turn each product of indicators into the indicator of the intersection
(`Set.inter_indicator_one`), and integrate termwise. -/
theorem lintegral_sq_sum_indicator (T : ℕ → Set Plane) (hT : ∀ k, MeasurableSet (T k)) (N : ℕ) :
    ∫⁻ x, (∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x) ^ 2 ∂volume
      = ∑ j ∈ range N, ∑ k ∈ range N, volume (T j ∩ T k) := by
  have hpt : ∀ x, (∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x) ^ 2
      = ∑ j ∈ range N, ∑ k ∈ range N, (T j ∩ T k).indicator (1 : Plane → ℝ≥0∞) x := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    refine sum_congr rfl (fun j _ => sum_congr rfl (fun k _ => ?_))
    rw [Set.inter_indicator_one, Pi.mul_apply]
  rw [lintegral_congr hpt,
    lintegral_finset_sum _ (fun j _ =>
      Finset.measurable_sum _ (fun k _ => measurable_one.indicator ((hT j).inter (hT k))))]
  refine sum_congr rfl (fun j _ => ?_)
  rw [lintegral_finset_sum _ (fun k _ => measurable_one.indicator ((hT j).inter (hT k)))]
  exact sum_congr rfl (fun k _ => lintegral_indicator_one ((hT j).inter (hT k)))

end LeanFormalizations.Kakeya2D

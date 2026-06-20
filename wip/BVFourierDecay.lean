/-
# Route (b) toward `prelim_decay_2`: half-period shift + L¹-translation-by-TV

`prelim_decay_2` (`‖𝓕 ψ u‖ ≤ V(ψ)/(2π|u|)` for ψ integrable + bounded variation) is **still `sorry`
upstream** in `PrimeNumberTheoremAnd` (now our dependency, `Wiener.lean:323`) and **absent from mathlib**.
The blueprint route is Lebesgue–Stieltjes integration-by-parts (sharp `2π|u|`), which mathlib lacks.

This file develops the **self-contained route (b)** (weaker constant `4|u|`, no BV-IBP):

  ‖𝓕 f u‖ ≤ ½ ∫ ‖f t − f(t + 1/(2u))‖ dt        -- (b1) Fourier half-period shift
            ≤ ½ · |1/(2u)| · V(f)  =  V(f)/(4|u|) -- (b2) L¹-translation-by-total-variation

This lap: the **pointwise variation bound is PROVEN** (`norm_sub_le_eVariationOn_toReal`, straight from
`eVariationOn.edist_le`), the two analytic cruxes (b1)/(b2) are isolated as disclosed `sorry`s with proof
sketches, and the **assembly** `prelim_decay_2_route_b` is verified in-kernel — so the one opaque upstream
`sorry` is narrowed to exactly two precise, narrower mathlib-absent lemmas. Lives in `wip/` (outside the
build); `src/` stays sorry-free. NOT a headline; dead code on the WeakPNT path (clean `#print axioms`).
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Real
open scoped FourierTransform

namespace BVFourierDecay

/-- **Pointwise variation bound (PROVEN).** For `f` of bounded variation on `univ`, any two values differ
by at most the total variation: `‖f a − f b‖ ≤ V(f)`. Direct from `eVariationOn.edist_le`. -/
theorem norm_sub_le_eVariationOn_toReal {f : ℝ → ℂ} (hf : BoundedVariationOn f Set.univ) (a b : ℝ) :
    ‖f a - f b‖ ≤ (eVariationOn f Set.univ).toReal := by
  have h : edist (f a) (f b) ≤ eVariationOn f Set.univ :=
    eVariationOn.edist_le f (Set.mem_univ a) (Set.mem_univ b)
  rw [edist_dist, dist_eq_norm] at h
  have h2 := ENNReal.toReal_mono hf h
  rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h2

/-- **(b1) Fourier half-period shift (CRUX — disclosed `sorry`).**
`‖𝓕 f u‖ ≤ ½ ∫ ‖f t − f(t + 1/(2u))‖ dt`.

Proof sketch: substitute `t ↦ t + 1/(2u)` in `𝓕 f u = ∫ 𝐞(−tu) f t dt`; since `𝐞(−½) = e^{−πi} = −1`,
the shifted integral equals `−𝓕 f u`, so `2·𝓕 f u = ∫ 𝐞(−tu)(f t − f(t+1/(2u))) dt`. Take norms
(`‖𝐞(·)‖ = 1`, `norm_integral_le_integral_norm`). Needs `MeasureTheory.integral_add_right_eq_self` for the
translation invariance of `volume` and the `Real.fourierChar` value at `−½`. -/
theorem norm_fourierIntegral_le_half_integral_norm_sub_shift
    (f : ℝ → ℂ) (hf : Integrable f) (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 f u‖ ≤ (1 / 2) * ∫ t, ‖f t - f (t + 1 / (2 * u))‖ := by
  sorry

/-- **(b2) L¹-translation by total variation (CRUX — disclosed `sorry`).**
`∫ ‖f t − f(t + h)‖ dt ≤ |h| · V(f)`.

Proof sketch: pointwise `‖f t − f(t+h)‖ ≤ V_{[t,t+h]}(f) = μ_V((t, t+h])` where `μ_V` is the variation
(Stieltjes) measure; then Fubini `∫_t μ_V((t,t+h]) dt = ∫_s (∫_t 𝟙_{t < s ≤ t+h} dt) dμ_V(s) = ∫_s |h| dμ_V
= |h|·V`. The variation-measure layer is mathlib-absent (only monotone `StieltjesFunction`); the pointwise
input is `norm_sub_le_eVariationOn_toReal` applied on `Icc t (t+h)`. -/
theorem integral_norm_sub_translate_le
    (f : ℝ → ℂ) (hf : Integrable f) (hbv : BoundedVariationOn f Set.univ) (h : ℝ) :
    (∫ t, ‖f t - f (t + h)‖) ≤ |h| * (eVariationOn f Set.univ).toReal := by
  sorry

/-- **Assembly (PROVEN modulo the two cruxes).** Route-(b) decay bound `‖𝓕 f u‖ ≤ V(f)/(4|u|)` — the
weaker (non-sharp) form of `prelim_decay_2`. Verified in-kernel from (b1)+(b2): this is the structural
content; only the two analytic cruxes above remain open. -/
theorem prelim_decay_2_route_b
    (f : ℝ → ℂ) (hf : Integrable f) (hbv : BoundedVariationOn f Set.univ) (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 f u‖ ≤ (eVariationOn f Set.univ).toReal / (4 * |u|) := by
  set V := (eVariationOn f Set.univ).toReal with hV
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
  have hb1 := norm_fourierIntegral_le_half_integral_norm_sub_shift f hf u hu
  have hb2 := integral_norm_sub_translate_le f hf hbv (1 / (2 * u))
  have habs : |1 / (2 * u)| = 1 / (2 * |u|) := by
    rw [abs_div, abs_one, abs_mul]; norm_num
  -- chain: ‖𝓕 f u‖ ≤ ½·(∫‖f t − f(t+1/(2u))‖) ≤ ½·(|1/(2u)|·V) = V/(4|u|)
  have hstep : (1 / 2) * (∫ t, ‖f t - f (t + 1 / (2 * u))‖) ≤ V / (4 * |u|) := by
    have hu' : 0 < |u| := abs_pos.mpr hu
    calc (1 / 2) * (∫ t, ‖f t - f (t + 1 / (2 * u))‖)
        ≤ (1 / 2) * (|1 / (2 * u)| * V) := by
          exact mul_le_mul_of_nonneg_left hb2 (by norm_num)
      _ = V / (4 * |u|) := by
          rw [habs]; field_simp <;> ring
  exact hb1.trans hstep

end BVFourierDecay

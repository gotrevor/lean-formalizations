/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# A derivative-free comparison principle for the linear-sieve delay system (phase E5, step 5)

If `K ≥ 0` vanishes on `(1, 2]`, satisfies `K(s) ≤ ∫_{s−1}^∞ K(u)/u du` for `s ≥ 2`, and
`∫_2^∞ K(u)(u−1) du < ∞`, then `K = 0` on `[2, ∞)`.

Proof: integrate the hypothesis against `w(s) = s − 1` over `s > 2` and swap (Tonelli):
`∫_2^{u+1} (s−1) ds = (u²−1)/2`, so `∫ K(u)(u−1) ≤ ∫ K(u)(u²−1)/(2u)`, while
`(u−1) = (u²−1)/(2u) + (u−1)²/(2u)`.  Finiteness forces `∫ K(u)(u−1)²/(2u) = 0`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open MeasureTheory Set ENNReal

/-- `∫_2^{u+1} (s − 1) ds = (u² − 1)/2` for `u ≥ 1`, as a lower integral. -/
lemma lintegral_weight {u : ℝ} (hu : 1 ≤ u) :
    ∫⁻ s in Ioo 2 (u + 1), ENNReal.ofReal (s - 1) = ENNReal.ofReal ((u ^ 2 - 1) / 2) := by
  have hint : IntegrableOn (fun s : ℝ => s - 1) (Ioo 2 (u + 1)) :=
    (continuous_id.sub continuous_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_right (fun x => x) 1, integral_id]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp only [Pi.zero_apply]; linarith [hs.1]

theorem comparison_principle (K : ℝ → ℝ≥0∞) (hK : Measurable K)
    (h12 : ∀ u, 1 < u → u ≤ 2 → K u = 0)
    (hrec : ∀ s, 2 ≤ s → K s ≤ ∫⁻ u in Ioi (s - 1), K u / ENNReal.ofReal u)
    (hfin : ∫⁻ u in Ioi 2, K u * ENNReal.ofReal (u - 1) ≠ ∞) :
    ∀ s, 2 ≤ s → K s = 0 := by
  set F : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if 2 < p.1 ∧ p.1 - 1 < p.2 then K p.2 / ENNReal.ofReal p.2 * ENNReal.ofReal (p.1 - 1) else 0
    with hF
  have hFm : Measurable F := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt (measurable_fst.sub measurable_const) measurable_snd)
    · exact ((hK.comp measurable_snd).div (ENNReal.measurable_ofReal.comp measurable_snd)).mul
        (ENNReal.measurable_ofReal.comp (measurable_fst.sub measurable_const))
  have h1 : ∫⁻ u in Ioi 2, K u * ENNReal.ofReal (u - 1) ≤ ∫⁻ s, ∫⁻ u, F (s, u) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_mono fun s => ?_
    by_cases hs : 2 < s
    · rw [indicator_of_mem (show s ∈ Ioi 2 from hs)]
      have : ∫⁻ u, F (s, u) = (∫⁻ u in Ioi (s - 1), K u / ENNReal.ofReal u) *
          ENNReal.ofReal (s - 1) := by
        rw [← lintegral_mul_const' _ _ ofReal_ne_top, ← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun u => ?_
        by_cases hu : s - 1 < u
        · simp [F, hs, hu, indicator_of_mem (show u ∈ Ioi (s - 1) from hu)]
        · simp [F, hu, indicator_of_notMem (show u ∉ Ioi (s - 1) from hu)]
      rw [this]
      exact mul_le_mul_left (hrec s hs.le) _
    · simp [indicator_of_notMem (show s ∉ Ioi 2 from hs)]
  have h2 : ∫⁻ s, ∫⁻ u, F (s, u) = ∫⁻ u, ∫⁻ s, F (s, u) :=
    lintegral_lintegral_swap hFm.aemeasurable
  have h3 : ∫⁻ u, ∫⁻ s, F (s, u) =
      ∫⁻ u in Ioi 2, K u * ENNReal.ofReal ((u ^ 2 - 1) / (2 * u)) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun u => ?_
    have hin : ∫⁻ s, F (s, u) =
        K u / ENNReal.ofReal u * ∫⁻ s in Ioo 2 (u + 1), ENNReal.ofReal (s - 1) := by
      rw [← lintegral_const_mul (K u / ENNReal.ofReal u) (f := fun s => ENNReal.ofReal (s - 1))
        (ENNReal.measurable_ofReal.comp (measurable_id.sub measurable_const)),
        ← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun s => ?_
      by_cases hs : 2 < s ∧ s - 1 < u
      · rw [indicator_of_mem (show s ∈ Ioo 2 (u + 1) from ⟨hs.1, by linarith [hs.2]⟩)]
        simp [F, hs]
      · rw [indicator_of_notMem (show s ∉ Ioo 2 (u + 1) from fun h => hs ⟨h.1, by linarith [h.2]⟩)]
        simp [F, hs]
    rw [hin]
    by_cases hu2 : 2 < u
    · rw [indicator_of_mem (show u ∈ Ioi 2 from hu2), lintegral_weight (by linarith),
        div_eq_mul_inv, mul_assoc, ← ENNReal.ofReal_inv_of_pos (by linarith),
        ← ENNReal.ofReal_mul (by rw [inv_nonneg]; linarith)]
      congr 2
      field_simp
    · rw [indicator_of_notMem (show u ∉ Ioi 2 from hu2)]
      by_cases hu1 : 1 < u
      · rw [h12 u hu1 (not_lt.mp hu2)]; simp
      · have : Ioo (2 : ℝ) (u + 1) = ∅ := Ioo_eq_empty (by linarith)
        simp [this]
  have hAB := h1.trans (h2.trans h3).le
  -- split the weight
  have hsplit : ∫⁻ u in Ioi 2, K u * ENNReal.ofReal (u - 1) =
      (∫⁻ u in Ioi 2, K u * ENNReal.ofReal ((u ^ 2 - 1) / (2 * u))) +
      ∫⁻ u in Ioi 2, K u * ENNReal.ofReal ((u - 1) ^ 2 / (2 * u)) := by
    rw [← lintegral_add_left (f := fun u => K u * ENNReal.ofReal ((u ^ 2 - 1) / (2 * u)))
      (hK.mul (ENNReal.measurable_ofReal.comp (by fun_prop)))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu : (2 : ℝ) < u := hu
    rw [← mul_add, ← ENNReal.ofReal_add (div_nonneg (by nlinarith) (by linarith)) (by positivity)]
    congr 2
    field_simp
    ring
  have hB : ∫⁻ u in Ioi 2, K u * ENNReal.ofReal ((u ^ 2 - 1) / (2 * u)) ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [hsplit]; exact le_self_add
  have hC : ∫⁻ u in Ioi 2, K u * ENNReal.ofReal ((u - 1) ^ 2 / (2 * u)) = 0 := by
    have := hAB
    rw [hsplit] at this
    exact le_antisymm ((ENNReal.add_le_add_iff_left hB).mp (by simpa using this)) bot_le
  have hae := (lintegral_eq_zero_iff (hK.mul (ENNReal.measurable_ofReal.comp (by fun_prop)))).mp hC
  have hae2 : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioi 2 → K u = 0 := by
    rw [← ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with u h hu
    have hu : (2 : ℝ) < u := hu
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exfalso
      simp only [Function.comp_apply, ENNReal.ofReal_eq_zero] at h
      have : 0 < (u - 1) ^ 2 / (2 * u) := by apply div_pos <;> nlinarith
      linarith
  intro s hs
  refine le_antisymm ((hrec s hs).trans (le_of_eq ?_)) bot_le
  have : (fun u => K u / ENNReal.ofReal u) =ᵐ[volume.restrict (Ioi (s - 1))] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hae2] with u hus hu
    have hus : s - 1 < u := hus
    by_cases hu2 : 2 < u
    · simp [hu hu2]
    · simp [h12 u (by linarith) (not_lt.mp hu2)]
  rw [lintegral_congr_ae this]; simp

end LeanFormalizations.Erdos385.LinearSieve

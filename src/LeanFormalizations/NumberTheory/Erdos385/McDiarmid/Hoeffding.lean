/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Hoeffding's lemma, finite uniform form (phase E4b helper)

From mathlib's measure-theoretic Hoeffding lemma on the uniform PMF.
-/

namespace LeanFormalizations.Erdos385.McDiarmid

open MeasureTheory ProbabilityTheory

/-- **Hoeffding's lemma**, finite form: a mean-zero function with oscillation `≤ c` has
`Σ exp(λ g) ≤ N exp(λ² c² / 8)`. -/
theorem hoeffding_finite {β : Type*} [Fintype β] [Nonempty β] (g : β → ℝ) (c l : ℝ)
    (hmean : ∑ x, g x = 0) (hosc : ∀ x y, |g x - g y| ≤ c) :
    ∑ x, Real.exp (l * g x) ≤ Fintype.card β * Real.exp (l ^ 2 * c ^ 2 / 8) := by
  letI : MeasurableSpace β := ⊤
  haveI : MeasurableSingletonClass β := ⟨fun _ => trivial⟩
  set p := PMF.uniformOfFintype β
  set μ := p.toMeasure
  have hN : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hint (F : β → ℝ) : ∫ x, F x ∂μ = (∑ x, F x) / Fintype.card β := by
    rw [PMF.integral_eq_sum]
    simp [p, PMF.uniformOfFintype_apply, div_eq_inv_mul, ENNReal.toReal_inv, Finset.mul_sum]
  obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  obtain ⟨x1, -, hx1⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  have hs := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := g)
    (a := g x0) (b := g x1) (Measurable.of_discrete.aemeasurable)
    (Filter.Eventually.of_forall fun x => ⟨hx0 x (Finset.mem_univ _), hx1 x (Finset.mem_univ _)⟩)
    (by rw [hint, hmean, zero_div])
  have h1 := hs.mgf_le l
  rw [mgf, hint] at h1
  have hab : 0 ≤ g x1 - g x0 := sub_nonneg.2 (hx0 x1 (Finset.mem_univ _))
  have hc : g x1 - g x0 ≤ c := le_trans (le_abs_self _) (hosc x1 x0)
  have hsq : (‖g x1 - g x0‖₊ / 2 : NNReal) ^ 2 * l ^ 2 / 2 ≤ l ^ 2 * c ^ 2 / 8 := by
    have : ((‖g x1 - g x0‖₊ : NNReal) : ℝ) = g x1 - g x0 := by
      rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hab]
    push_cast [this]
    have : (g x1 - g x0) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hab hc 2
    nlinarith [sq_nonneg l]
  rw [div_le_iff₀ hN] at h1
  calc ∑ x, Real.exp (l * g x) ≤ _ := h1
    _ ≤ Real.exp (l ^ 2 * c ^ 2 / 8) * Fintype.card β := 
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by push_cast at hsq ⊢; linarith)) hN.le
    _ = _ := mul_comm _ _

end LeanFormalizations.Erdos385.McDiarmid

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Plancherel

/-!
# Band projections

`plancherel_integral` (Bochner form), `plancherel_fourierInv` (`∫|𝓕⁻ F|² = ∫|F|²`), and the
complement identity `∫ |f − 𝓕⁻(1_S 𝓕 f)|² = ∫_{Sᶜ} |𝓕 f|²`, which needs no integrability of the
high-frequency remainder beyond what Plancherel already gives.
-/

open MeasureTheory Filter Complex Set
open scoped Topology FourierTransform ComplexConjugate ENNReal

noncomputable section

namespace Erdos385.Parseval

/-- Plancherel, Bochner form. -/
theorem plancherel_integral {f : ℝ → ℂ} (hf : Integrable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (hcont : ∀ᵐ x, ContinuousAt f x) :
    Integrable (fun ξ ↦ ‖𝓕 f ξ‖ ^ 2) ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hP := plancherel_lintegral hf hM hcont
  have hf2 : Integrable (fun x ↦ ‖f x‖ ^ 2) := by
    refine (hf.norm.mul_const M).mono' (hf.1.norm.pow 2) (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
  have hFm : AEStronglyMeasurable (𝓕 f) :=
    (continuous_fourier_of_integrable hf).aestronglyMeasurable
  have hconv : ∀ g : ℝ → ℂ, AEStronglyMeasurable g →
      ∫⁻ x, ‖g x‖ₑ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := fun g _ ↦
    lintegral_congr fun x ↦ by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hfin : ∫⁻ ξ, ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) < ∞ := by
    rw [← hconv _ hFm, hP, hconv _ hf.1, ← ofReal_integral_eq_lintegral_ofReal hf2
      (Eventually.of_forall fun x ↦ by positivity)]
    exact ENNReal.ofReal_lt_top
  have hF2 : Integrable (fun ξ ↦ ‖𝓕 f ξ‖ ^ 2) :=
    ⟨(hFm.norm.pow 2), by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ ↦ by positivity)]
      exact hfin⟩
  refine ⟨hF2, ?_⟩
  rw [hconv _ hFm, hconv _ hf.1, ← ofReal_integral_eq_lintegral_ofReal hf2
      (Eventually.of_forall fun x ↦ by positivity), ← ofReal_integral_eq_lintegral_ofReal hF2
      (Eventually.of_forall fun x ↦ by positivity)] at hP
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ ↦ by positivity)
    (integral_nonneg fun _ ↦ by positivity)).mp hP

/-- Plancherel for the inverse transform. -/
theorem plancherel_fourierInv {F : ℝ → ℂ} (hF : Integrable F) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M)
    (hcont : ∀ᵐ x, ContinuousAt F x) :
    Integrable (fun x ↦ ‖𝓕⁻ F x‖ ^ 2) ∧ ∫ x, ‖𝓕⁻ F x‖ ^ 2 = ∫ ξ, ‖F ξ‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := plancherel_integral hF hM hcont
  simp_rw [Real.fourierInv_eq_fourier_neg]
  refine ⟨h1.comp_neg, ?_⟩
  rw [integral_neg_eq_self (fun x ↦ ‖𝓕 F x‖ ^ 2), h2]

/-- The multiplication formula `∫ conj (𝓕 f) g = ∫ conj f (𝓕⁻ g)`. -/
lemma integral_conj_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, conj (𝓕 f ξ) * g ξ = ∫ x, conj (f x) * 𝓕⁻ g x := by
  have := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg
  simp at this
  calc _ = ∫ ξ, g ξ * conj (𝓕 f ξ) := by congr 1 with ξ; ring
    _ = ∫ x, 𝓕⁻ g x * conj (f x) := this
    _ = _ := by congr 1 with x; ring

/-- **Band complement.**  `∫ |f − 𝓕⁻(1_S 𝓕f)|² = ∫_{Sᶜ} |𝓕 f|²`. -/
theorem integral_norm_sub_proj {f : ℝ → ℂ} (hf : Integrable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (hcont : ∀ᵐ x, ContinuousAt f x) {S : Set ℝ} (hS : MeasurableSet S)
    (hFi : Integrable (S.indicator (𝓕 f)))
    (hFc : ∀ᵐ ξ, ContinuousAt (S.indicator (𝓕 f)) ξ) :
    Integrable (fun x ↦ ‖f x - 𝓕⁻ (S.indicator (𝓕 f)) x‖ ^ 2) ∧
      ∫ x, ‖f x - 𝓕⁻ (S.indicator (𝓕 f)) x‖ ^ 2 = ∫ ξ in Sᶜ, ‖𝓕 f ξ‖ ^ 2 := by
  set F := S.indicator (𝓕 f)
  set P := 𝓕⁻ F
  have hFb : ∀ ξ, ‖F ξ‖ ≤ ∫ x, ‖f x‖ := by
    intro ξ
    by_cases h : ξ ∈ S
    · simp only [F, indicator_of_mem h]; exact norm_fourier_le ξ
    · simp only [F, indicator_of_notMem h, norm_zero]; exact integral_nonneg fun _ ↦ norm_nonneg _
  obtain ⟨hFf2, hFfeq⟩ := plancherel_integral hf hM hcont
  obtain ⟨hP2, hPeq⟩ := plancherel_fourierInv hFi hFb hFc
  have hf2 : Integrable (fun x ↦ ‖f x‖ ^ 2) := by
    refine (hf.norm.mul_const M).mono' (hf.1.norm.pow 2) (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
  have hPm : AEStronglyMeasurable P := by
    have : Continuous P := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner.neg hFi
    exact this.aestronglyMeasurable
  have hfL : MemLp f 2 := (memLp_two_iff_integrable_sq_norm hf.1).mpr hf2
  have hPL : MemLp P 2 := (memLp_two_iff_integrable_sq_norm hPm).mpr hP2
  have hcross : Integrable (fun x ↦ conj (f x) * P x) := by
    have hcf : MemLp (fun x ↦ conj (f x)) 2 := by
      refine (memLp_two_iff_integrable_sq_norm
        (Complex.continuous_conj.comp_aestronglyMeasurable hf.1)).mpr ?_
      simpa using hf2
    exact hcf.integrable_mul hPL
  have hcrossval : ∫ x, conj (f x) * P x = ∫ ξ in S, ((‖𝓕 f ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_conj_fourier_mul hf hFi, ← integral_indicator hS]
    congr 1 with ξ
    by_cases h : ξ ∈ S
    · simp only [F, indicator_of_mem h]; rw [Complex.conj_mul']; push_cast; ring
    · simp [F, indicator_of_notMem h]
  have hPval : ∫ x, ‖P x‖ ^ 2 = ∫ ξ in S, ‖𝓕 f ξ‖ ^ 2 := by
    rw [hPeq, ← integral_indicator hS]
    congr 1 with ξ
    by_cases h : ξ ∈ S
    · simp [F, indicator_of_mem h]
    · simp [F, indicator_of_notMem h]
  have hpt : ∀ x, ‖f x - P x‖ ^ 2 = ‖f x‖ ^ 2 - 2 * (conj (f x) * P x).re + ‖P x‖ ^ 2 := by
    intro x
    rw [@norm_sub_sq ℂ ℂ _ _ _ (f x) (P x)]
    simp [inner, mul_comm]
  have hre : Integrable (fun x ↦ 2 * (conj (f x) * P x).re) := hcross.re.const_mul 2
  have hP2' : Integrable (fun x ↦ ‖P x‖ ^ 2) := hP2
  have hA : Integrable (fun x ↦ ‖f x‖ ^ 2 - 2 * (conj (f x) * P x).re) := hf2.sub hre
  have hint : Integrable (fun x ↦ ‖f x - P x‖ ^ 2) := by
    simp_rw [hpt]
    exact hA.add hP2'
  refine ⟨hint, ?_⟩
  simp_rw [hpt]
  rw [integral_add hA hP2', integral_sub hf2 hre,
    integral_const_mul,
    show ∫ x, (conj (f x) * P x).re = (∫ x, conj (f x) * P x).re from integral_re hcross,
    hcrossval, integral_complex_ofReal, Complex.ofReal_re,
    hPval, ← hFfeq, ← integral_add_compl hS hFf2]
  ring

end Erdos385.Parseval

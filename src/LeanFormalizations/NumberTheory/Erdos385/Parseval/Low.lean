/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Mellin
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Kernel

/-!
# Window differences of band-limited pieces; the low band

`Δ g x h = (x+h) g(log(x+h)) − x g(log x)` and `Dif g x = Δ g x h₁/h₁ − Δ g x h₂/h₂`.
For `g = 𝓕⁻ F`, `v g(log v) = ∫ F(ξ) v^{s(ξ)} dξ`.  Low band: `‖Dif‖ ≤ 2R·K·4πR h₂/x`.
-/

open MeasureTheory Complex Set
open scoped FourierTransform

noncomputable section

namespace Erdos385.Parseval

/-- `Δ g x h = (x+h) g(log(x+h)) − x g(log x)`. -/
def winDelta (g : ℝ → ℂ) (x h : ℝ) : ℂ :=
  ((x + h : ℝ) : ℂ) * g (Real.log (x + h)) - (x : ℂ) * g (Real.log x)

/-- `D g x = Δ g x h₁ / h₁ − Δ g x h₂ / h₂`. -/
def winDif (g : ℝ → ℂ) (h₁ h₂ x : ℝ) : ℂ :=
  winDelta g x h₁ / h₁ - winDelta g x h₂ / h₂

lemma mul_fourierInv_log (F : ℝ → ℂ) {v : ℝ} (hv : 0 < v) :
    (v : ℂ) * 𝓕⁻ F (Real.log v) = ∫ ξ, F ξ * (v : ℂ) ^ sArg ξ := by
  rw [Real.fourierInv_eq', ← integral_const_mul]
  congr 1 with ξ
  rw [smul_eq_mul, cpow_def_of_ne_zero (by exact_mod_cast hv.ne'), ← ofReal_log hv.le]
  have : (v : ℂ) = cexp (Real.log v) := by
    rw [← ofReal_exp, Real.exp_log hv]
  conv_lhs => rw [this]
  rw [← mul_assoc, mul_comm _ (F ξ), mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [sArg, RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- The window kernel at frequency `ξ`. -/
def winKer (h₁ h₂ x ξ : ℝ) : ℂ :=
  (((x + h₁ : ℝ) : ℂ) ^ sArg ξ - (x : ℂ) ^ sArg ξ) / (sArg ξ * h₁) -
    (((x + h₂ : ℝ) : ℂ) ^ sArg ξ - (x : ℂ) ^ sArg ξ) / (sArg ξ * h₂)

lemma integrable_mul_cpow {F : ℝ → ℂ} (hF : Integrable F) {v : ℝ} (hv : 0 < v) :
    Integrable (fun ξ ↦ F ξ * (v : ℂ) ^ sArg ξ) := by
  refine hF.mul_bdd (c := v) ?_ (Filter.Eventually.of_forall fun ξ ↦ ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.cpow (by unfold sArg; fun_prop)
      (fun _ ↦ Or.inl (by exact_mod_cast hv))
  · rw [norm_cpow_eq_rpow_re_of_pos hv, sArg_re, Real.rpow_one]

lemma winDelta_fourierInv {F : ℝ → ℂ} (hF : Integrable F) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    winDelta (𝓕⁻ F) x h = ∫ ξ, F ξ * (((x + h : ℝ) : ℂ) ^ sArg ξ - (x : ℂ) ^ sArg ξ) := by
  rw [winDelta, mul_fourierInv_log F (by linarith), mul_fourierInv_log F hx,
    ← integral_sub (integrable_mul_cpow hF (by linarith)) (integrable_mul_cpow hF hx)]
  simp_rw [mul_sub]

lemma winDif_fourierInv {F : ℝ → ℂ} (hF : Integrable F) {x h₁ h₂ : ℝ} (hx : 0 < x)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    winDif (𝓕⁻ F) h₁ h₂ x = ∫ ξ, F ξ * sArg ξ * winKer h₁ h₂ x ξ := by
  have hi : ∀ h : ℝ, 0 < h → Integrable
      (fun ξ ↦ F ξ * (((x + h : ℝ) : ℂ) ^ sArg ξ - (x : ℂ) ^ sArg ξ)) := fun h hh ↦ by
    simp_rw [mul_sub]
    exact (integrable_mul_cpow hF (by linarith)).sub (integrable_mul_cpow hF hx)
  rw [winDif, winDelta_fourierInv hF hx hh₁.le, winDelta_fourierInv hF hx hh₂.le,
    ← integral_div, ← integral_div, ← integral_sub ((hi h₁ hh₁).div_const _)
      ((hi h₂ hh₂).div_const _)]
  congr 1 with ξ
  have hs := sArg_ne_zero ξ
  have h1 : (h₁ : ℂ) ≠ 0 := by exact_mod_cast hh₁.ne'
  have h2 : (h₂ : ℂ) ≠ 0 := by exact_mod_cast hh₂.ne'
  rw [winKer]
  field_simp

lemma sArg_eq (ξ : ℝ) : sArg ξ = 1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by
  simp only [sArg]; push_cast; ring

/-- **Low band.**  Pointwise bound on the window difference of a band-limited piece. -/
theorem norm_winDif_low {G : ℝ → ℂ} {K R : ℝ} (hG : ∀ ξ, ‖G ξ‖ ≤ K) (hR : 0 ≤ R)
    {S : Set ℝ} (hSR : S ⊆ Icc (-R) R)
    (hF : Integrable (S.indicator fun ξ ↦ G ξ / sArg ξ)) {x h₁ h₂ : ℝ} (hx : 0 < x)
    (hh₁ : 0 < h₁) (h12 : h₁ ≤ h₂) :
    ‖winDif (𝓕⁻ (S.indicator fun ξ ↦ G ξ / sArg ξ)) h₁ h₂ x‖ ≤
      2 * R * (K * (2 * (2 * Real.pi * R) * h₂ / x)) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hG 0)
  rw [winDif_fourierInv hF hx hh₁ (hh₁.trans_le h12)]
  set C := K * (2 * (2 * Real.pi * R) * h₂ / x)
  have hint : Integrable ((Icc (-R) R).indicator fun _ ↦ C) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun ξ ↦ ?_)).trans ?_
  · by_cases hξ : ξ ∈ S
    · rw [indicator_of_mem hξ, indicator_of_mem (hSR hξ), div_mul_cancel₀ _ (sArg_ne_zero ξ),
        norm_mul]
      apply mul_le_mul (hG ξ) _ (norm_nonneg _) hK
      have hk := norm_kernel_le (τ := 2 * Real.pi * ξ) hx hh₁ h12
      simp only [winKer, sArg_eq]
      refine hk.trans ?_
      have : |2 * Real.pi * ξ| ≤ 2 * Real.pi * R := by
        rw [abs_mul, abs_of_pos (by positivity)]
        gcongr
        exact abs_le.mpr (hSR hξ)
      have : 0 ≤ h₂ / x := div_nonneg (hh₁.le.trans h12) hx.le
      calc 2 * |2 * Real.pi * ξ| * h₂ / x = 2 * |2 * Real.pi * ξ| * (h₂ / x) := by ring
        _ ≤ 2 * (2 * Real.pi * R) * (h₂ / x) := by gcongr
        _ = _ := by ring
    · rw [indicator_of_notMem hξ, zero_mul, zero_mul, norm_zero]
      by_cases h' : ξ ∈ Icc (-R) R
      · rw [indicator_of_mem h']
        have : 0 ≤ h₂ / x := div_nonneg (hh₁.le.trans h12) hx.le
        have : 0 ≤ 2 * (2 * Real.pi * R) * h₂ / x := by
          rw [mul_div_assoc]; positivity
        exact mul_nonneg hK this
      · rw [indicator_of_notMem h']
  · rw [integral_indicator measurableSet_Icc, setIntegral_const]
    simp only [Real.volume_real_Icc, smul_eq_mul]
    rw [max_eq_left (by linarith)]
    ring_nf; rfl

end Erdos385.Parseval

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Low

/-!
# Erdős #385 power saving: the near part pointwise (phase E9b)

The window average `((x+h)^s − x^s)/(s h)`, `Re s = 1`, is the mean of `v^{iτ}` over `[x, x+h]`, so
has norm `≤ 1`; the window kernel has norm `≤ 2`, and

* `norm_winDif_fourierInv_le`: `‖D[𝓕⁻ F](x)‖ ≤ 2 ∫ ‖F(ξ) s(ξ)‖ dξ` for every `x > 0`.

Applied to `F = 1_E · (Â/s)` (`E` = the near-1 large-value frequencies) this is the pointwise
bound on `D_near`.
-/

open Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace Erdos385.Parseval

lemma norm_avg_le_one {τ x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖(((x + h : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / ((1 + τ * I) * h)‖ ≤ 1 := by
  have hint : ∫ v in x..x + h, (v : ℂ) ^ ((τ : ℂ) * I) =
      (((x + h : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / (1 + τ * I) := by
    rw [integral_cpow (Or.inl (by simp))]
    rw [add_comm ((τ : ℂ) * I) 1]
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [← div_div, ← hint, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_le_one hh]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + h)
    (C := 1) (f := fun v : ℝ ↦ (v : ℂ) ^ ((τ : ℂ) * I)) (fun v hv ↦ by
      rw [Set.uIoc_of_le (by linarith)] at hv
      have hv0 : 0 < v := by linarith [hv.1]
      rw [norm_cpow_eq_rpow_re_of_pos hv0]; simp)
  rw [show x + h - x = h by ring, abs_of_pos hh, one_mul] at hb
  exact hb

lemma norm_winKer_le {h₁ h₂ x ξ : ℝ} (hx : 0 < x) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    ‖winKer h₁ h₂ x ξ‖ ≤ 2 := by
  rw [winKer, sArg_eq]
  refine (norm_sub_le _ _).trans ?_
  have e1 := norm_avg_le_one (τ := 2 * Real.pi * ξ) hx hh₁
  have e2 := norm_avg_le_one (τ := 2 * Real.pi * ξ) hx hh₂
  linarith

/-- **Near part, pointwise.** -/
theorem norm_winDif_fourierInv_le {F : ℝ → ℂ} (hF : Integrable F)
    (hFs : Integrable fun ξ ↦ F ξ * sArg ξ) {x h₁ h₂ : ℝ} (hx : 0 < x)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    ‖winDif (𝓕⁻ F) h₁ h₂ x‖ ≤ 2 * ∫ ξ, ‖F ξ * sArg ξ‖ := by
  rw [winDif_fourierInv hF hx hh₁ hh₂, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hFs.norm.const_mul 2) (Filter.Eventually.of_forall
    fun ξ ↦ ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_winKer_le hx hh₁ hh₂) (norm_nonneg _)

end Erdos385.Parseval

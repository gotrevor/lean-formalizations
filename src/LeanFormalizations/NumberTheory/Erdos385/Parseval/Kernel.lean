/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The low-frequency kernel bound

With `s = 1 + iτ`: `((x+h)^s − x^s)/(s h)` is the average of `v^{iτ}` over `[x, x+h]`, hence within
`|τ| h / x` of `x^{iτ}`; two window lengths differ by at most `2|τ|h₂/x`.
-/

open Complex

noncomputable section

namespace Erdos385.Parseval

lemma norm_cpow_I_sub_le {τ x v : ℝ} (hx : 0 < x) (hxv : x ≤ v) :
    ‖(v : ℂ) ^ ((τ : ℂ) * I) - (x : ℂ) ^ ((τ : ℂ) * I)‖ ≤ |τ| * ((v - x) / x) := by
  have hv : 0 < v := lt_of_lt_of_le hx hxv
  have e : ∀ w : ℝ, 0 < w → (w : ℂ) ^ ((τ : ℂ) * I) = cexp (I * ((τ * Real.log w : ℝ) : ℂ)) := by
    intro w hw
    rw [cpow_def_of_ne_zero (by exact_mod_cast hw.ne'), ← ofReal_log hw.le]
    congr 1; push_cast; ring
  rw [e v hv, e x hx]
  have : cexp (I * ((τ * Real.log v : ℝ) : ℂ)) - cexp (I * ((τ * Real.log x : ℝ) : ℂ)) =
      cexp (I * ((τ * Real.log x : ℝ) : ℂ)) *
        (cexp (I * ((τ * (Real.log v - Real.log x) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]
  gcongr
  have h1 : 0 ≤ Real.log v - Real.log x := by linarith [Real.log_le_log hx hxv]
  rw [abs_of_nonneg h1, ← Real.log_div hv.ne' hx.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hv hx)
  rw [sub_div, div_self hx.ne']
  exact this

/-- `((x+h)^s − x^s)/(s h)` is within `|τ| h/x` of `x^{iτ}`. -/
lemma norm_avg_sub_le {τ x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖(((x + h : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / ((1 + τ * I) * h) -
        (x : ℂ) ^ ((τ : ℂ) * I)‖ ≤ |τ| * h / x := by
  have hs : (1 + (τ : ℂ) * I) ≠ 0 := fun h0 ↦ by
    have := congrArg Complex.re h0; simp at this
  have hint : ∫ v in x..x + h, (v : ℂ) ^ ((τ : ℂ) * I) =
      (((x + h : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / (1 + τ * I) := by
    rw [integral_cpow (Or.inl (by simp))]
    rw [add_comm ((τ : ℂ) * I) 1]
  have hc : ∫ v in x..x + h, (x : ℂ) ^ ((τ : ℂ) * I) = h * (x : ℂ) ^ ((τ : ℂ) * I) := by
    simp
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have key : (((x + h : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / ((1 + τ * I) * h) -
      (x : ℂ) ^ ((τ : ℂ) * I) =
      (∫ v in x..x + h, ((v : ℂ) ^ ((τ : ℂ) * I) - (x : ℂ) ^ ((τ : ℂ) * I))) / h := by
    rw [intervalIntegral.integral_sub, hint, hc]
    · field_simp
    · apply ContinuousOn.intervalIntegrable
      intro v hv
      have : 0 < v := by
        rw [Set.uIcc_of_le (by linarith)] at hv; linarith [hv.1]
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr this.ne')).continuousWithinAt
    · exact intervalIntegrable_const
  rw [key, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_le_iff₀ hh]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + h)
    (C := |τ| * (h / x)) (f := fun v : ℝ ↦ (v : ℂ) ^ ((τ : ℂ) * I) - (x : ℂ) ^ ((τ : ℂ) * I))
    (fun v hv ↦ by
      rw [Set.uIoc_of_le (by linarith)] at hv
      refine (norm_cpow_I_sub_le hx hv.1.le).trans ?_
      gcongr
      linarith [hv.2])
  rw [show x + h - x = h by ring, abs_of_pos hh] at hb
  calc _ ≤ |τ| * (h / x) * h := hb
    _ = |τ| * h / x * h := by ring

/-- **Kernel bound.**  Two window averages differ by at most `2|τ|h₂/x`. -/
theorem norm_kernel_le {τ x h₁ h₂ : ℝ} (hx : 0 < x) (hh₁ : 0 < h₁) (h12 : h₁ ≤ h₂) :
    ‖(((x + h₁ : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / ((1 + τ * I) * h₁) -
      (((x + h₂ : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / ((1 + τ * I) * h₂)‖ ≤
      2 * |τ| * h₂ / x := by
  have e1 := norm_avg_sub_le (τ := τ) hx hh₁
  have e2 := norm_avg_sub_le (τ := τ) hx (hh₁.trans_le h12)
  set q1 := (((x + h₁ : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / ((1 + τ * I) * h₁)
  set q2 := (((x + h₂ : ℝ) : ℂ) ^ (1 + τ * I) - (x : ℂ) ^ (1 + τ * I)) / ((1 + τ * I) * h₂)
  have := norm_sub_le_norm_sub_add_norm_sub q1 ((x : ℂ) ^ ((τ : ℂ) * I)) q2
  rw [norm_sub_rev ((x : ℂ) ^ ((τ : ℂ) * I)) q2] at this
  have h3 : |τ| * h₁ / x ≤ |τ| * h₂ / x := by gcongr
  calc _ ≤ _ := this
    _ ≤ |τ| * h₂ / x + |τ| * h₂ / x := add_le_add (e1.trans h3) e2
    _ = 2 * |τ| * h₂ / x := by ring

end Erdos385.Parseval

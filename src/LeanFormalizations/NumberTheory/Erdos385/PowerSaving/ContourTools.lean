/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll
import LeanFormalizations.NumberTheory.Erdos385.Landau.Basic

/-!
# Erdős #385 power saving: contour tools for local zero detection (phase E9b, crux step (b))

* `rect_shift_gen`: Cauchy on `[σ₁, σ₂] × [−U, U]` (norm form), `rect_shift_norm` with `σ₂` free;
* `mellin_cube_decay`: `‖mellin f s‖ (1 + y²)³ ≤ K` on `1/2 ≤ Re s ≤ 2`;
* `norm_intervalIntegral_le_pi`: an interval integral under a `c/(1+y²)` majorant is `≤ cπ`;
* `zetaH_bound_right`: `‖ζ'/ζ(w) + 1/(w−1)‖ ≤ 2/(Re w − 1) + C` for `Re w > 1`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex

/-- **Contour shift (norm form)** on `[σ₁, σ₂] × [−U, U]`. -/
theorem rect_shift_gen {G : ℂ → ℂ} {σ₁ σ₂ U : ℝ} (hσ : σ₁ ≤ σ₂) (hU : 0 ≤ U)
    (hd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → |s.im| ≤ U → DifferentiableAt ℂ G s) :
    ‖∫ y in (-U)..U, G (σ₂ + y * I)‖ ≤ ‖∫ y in (-U)..U, G (σ₁ + y * I)‖ +
      ‖∫ x in σ₁..σ₂, G (x + U * I)‖ + ‖∫ x in σ₁..σ₂, G (x - U * I)‖ := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    (σ₁ + (-U) * I) (σ₂ + U * I) (by
      intro s hs
      rw [Complex.mem_reProdIm] at hs
      simp only [add_re, ofReal_re, mul_re, neg_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, neg_im, zero_add, neg_zero] at hs
      rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (by linarith)] at hs
      exact (hd s hs.1.1 hs.1.2 (abs_le.2 ⟨hs.2.1, hs.2.2⟩)).differentiableWithinAt)
  simp only [add_re, ofReal_re, mul_re, neg_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, mul_im, neg_im, zero_add, neg_zero, ofReal_neg] at hrect
  have hI : ∀ z : ℂ, ‖I • z‖ = ‖z‖ := fun z => by
    rw [smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
  set A := ∫ y in (-U)..U, G (σ₂ + y * I)
  set B := ∫ y in (-U)..U, G (σ₁ + y * I)
  set Tp := ∫ x in σ₁..σ₂, G (x + U * I)
  set Bt := ∫ x in σ₁..σ₂, G (x - U * I)
  have eBt : (∫ x in σ₁..σ₂, G (x + (-U : ℂ) * I)) = Bt := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    congr 1; ring
  rw [eBt] at hrect
  have hA : I • A = I • B - Bt + Tp := by
    linear_combination hrect
  calc ‖A‖ = ‖I • A‖ := (hI A).symm
    _ = ‖I • B - Bt + Tp‖ := by rw [hA]
    _ ≤ ‖I • B‖ + ‖Bt‖ + ‖Tp‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ = ‖B‖ + ‖Tp‖ + ‖Bt‖ := by rw [hI]; ring

/-- **Cubic Mellin decay** on the strip `1/2 ≤ Re s ≤ 2`. -/
theorem mellin_cube_decay {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖mellin f s‖ * (1 + s.im ^ 2) ^ 3 ≤ K := by
  obtain ⟨K0, h0⟩ := mellin_strip_decay 0 hf ha hab hs (1 / 2) 2
  obtain ⟨K6, h6⟩ := mellin_strip_decay 6 hf ha hab hs (1 / 2) 2
  refine ⟨4 * |K0| + 4 * |K6|, by positivity, fun s hs0 hs1 => ?_⟩
  have e0 := h0 s hs0 hs1
  have e6 := h6 s hs0 hs1
  simp only [pow_zero, one_mul] at e0
  set x := s.im ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg _
  have hxs : x ≤ ‖s‖ ^ 2 := by
    have := Complex.abs_im_le_norm s
    rw [hx]; nlinarith [abs_nonneg s.im, sq_abs s.im]
  have hx3 : x ^ 3 ≤ ‖s‖ ^ 6 := by
    calc x ^ 3 ≤ (‖s‖ ^ 2) ^ 3 := pow_le_pow_left₀ hx0 hxs 3
      _ = ‖s‖ ^ 6 := by ring
  have hcube : (1 + x) ^ 3 ≤ 4 * (1 + x ^ 3) := by nlinarith [sq_nonneg (1 - x)]
  have hF := norm_nonneg (mellin f s)
  calc ‖mellin f s‖ * (1 + x) ^ 3 ≤ ‖mellin f s‖ * (4 * (1 + x ^ 3)) :=
        mul_le_mul_of_nonneg_left hcube hF
    _ = 4 * ‖mellin f s‖ + 4 * (x ^ 3 * ‖mellin f s‖) := by ring
    _ ≤ 4 * |K0| + 4 * (‖s‖ ^ 6 * ‖mellin f s‖) := by
        have := mul_le_mul_of_nonneg_right hx3 hF
        linarith [le_abs_self K0]
    _ ≤ 4 * |K0| + 4 * |K6| := by linarith [le_abs_self K6]

/-- An interval integral under a majorant `c/(1+y²)` is at most `cπ`. -/
theorem norm_intervalIntegral_le_pi {φ : ℝ → ℂ} {u v c : ℝ} (huv : u ≤ v) (hc : 0 ≤ c)
    (h : ∀ y, u ≤ y → y ≤ v → ‖φ y‖ ≤ c * (1 + y ^ 2)⁻¹) : ‖∫ y in u..v, φ y‖ ≤ c * π := by
  calc ‖∫ y in u..v, φ y‖ ≤ ∫ y in u..v, c * (1 + y ^ 2)⁻¹ :=
        intervalIntegral.norm_integral_le_of_norm_le huv
          (Eventually.of_forall fun y hy => h y hy.1.le hy.2)
          ((integrable_inv_one_add_sq.const_mul _).intervalIntegrable)
    _ ≤ ∫ y, c * (1 + y ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_of_le huv]
        exact setIntegral_le_integral (integrable_inv_one_add_sq.const_mul _)
          (Eventually.of_forall fun y => by positivity)
    _ = c * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- `H = ζ'/ζ + 1/(w−1)` to the right of `Re w = 1`. -/
theorem zetaH_bound_right : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 < w.re →
    ‖zetaH w‖ ≤ 2 / (w.re - 1) + C := by
  obtain ⟨C, hC⟩ := logDeriv_zeta_dirichlet_bound
  refine ⟨|C|, abs_nonneg _, fun w hw => ?_⟩
  have hw' : ((w.re : ℂ) + w.im * I) = w := Complex.re_add_im w
  have h1 := hC w.re w.im hw
  rw [hw'] at h1
  have hd : 0 < w.re - 1 := by linarith
  have hinv : ‖1 / (w - 1)‖ ≤ 1 / (w.re - 1) := by
    have hre : (w - 1).re = w.re - 1 := by simp
    have hle : w.re - 1 ≤ ‖w - 1‖ := by
      have := Complex.re_le_norm (w - 1); rwa [hre] at this
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hd hle
  have e : zetaH w = zLD w + 1 / (w - 1) := rfl
  rw [e]
  calc ‖zLD w + 1 / (w - 1)‖ ≤ ‖zLD w‖ + ‖1 / (w - 1)‖ := norm_add_le _ _
    _ ≤ (1 / (w.re - 1) + C) + 1 / (w.re - 1) := add_le_add h1 hinv
    _ ≤ 2 / (w.re - 1) + |C| := by
        have := le_abs_self C
        have e2 : 2 / (w.re - 1) = 1 / (w.re - 1) + 1 / (w.re - 1) := by ring
        linarith

end LeanFormalizations.Erdos385

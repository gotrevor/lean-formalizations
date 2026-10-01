/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.PNTFromVK.Line

/-!
# Phase E3e helper: the contour estimate with explicit Mellin data

For a smooth `F` supported in `[a, b]`, `a ≥ 1`, the Perron identity on `Re s = c`
(`smoothTwist_sub_main_eq_line`, `P = 1`, `t = 0`) is shifted to the VK line `σ₁` for `|y| ≤ T`.
Everything about `F` enters only through two Mellin bounds with explicit constants `M`, `D`, so the
estimate is uniform over families of weights (the smooth sandwich at scale `η`).

Error terms: main line `2T · M X^{σ₁} · C log T`; two horizontal sides `D X^c C log T / T⁴` each;
(4 in all) tails `|y| > T` on `Re s = c`, where VK at height `|y|` gives `|H| ≤ C log |y| ≤ C |y|`:
`≤ 2π D X^c C / T`.
-/

open Real Filter MeasureTheory Complex

namespace LeanFormalizations.Erdos385.PNTVK

open LeanFormalizations.Erdos385 LeanFormalizations.Literature

/-- The VK abscissa at height `T`. -/
noncomputable def vkSigma (c₀ T : ℝ) : ℝ :=
  1 - c₀ / (Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3))

/-- **Contour shift (norm form)** on the rectangle `[σ₁, c] × [−U, U]`. -/
theorem rect_shift_norm_line {G : ℂ → ℂ} {σ₁ c U : ℝ} (hσ : σ₁ ≤ c) (hU : 0 ≤ U)
    (hd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → |s.im| ≤ U → DifferentiableAt ℂ G s) :
    ‖∫ y in (-U)..U, G (c + y * I)‖ ≤ ‖∫ y in (-U)..U, G (σ₁ + y * I)‖ +
      ‖∫ x in σ₁..c, G (x + U * I)‖ + ‖∫ x in σ₁..c, G (x - U * I)‖ := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    (σ₁ + (-U) * I) (c + U * I) (by
      intro s hs
      rw [Complex.mem_reProdIm] at hs
      norm_num at hs
      rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (by linarith)] at hs
      exact (hd s hs.1.1 hs.1.2 (abs_le.2 ⟨hs.2.1, hs.2.2⟩)).differentiableWithinAt)
  norm_num at hrect
  simp only [← sub_eq_add_neg] at hrect
  have hI : ∀ z : ℂ, ‖I • z‖ = ‖z‖ := fun z => by rw [smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
  set A := ∫ y in (-U)..U, G (c + y * I)
  set B := ∫ y in (-U)..U, G (σ₁ + y * I)
  set Tp := ∫ x in σ₁..c, G (x + U * I)
  set Bt := ∫ x in σ₁..c, G (x - U * I)
  have hA : I • A = I • B - Bt + Tp := by
    linear_combination hrect
  calc ‖A‖ = ‖I • A‖ := (hI A).symm
    _ = ‖I • B - Bt + Tp‖ := by rw [hA]
    _ ≤ ‖I • B‖ + ‖Bt‖ + ‖Tp‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ = ‖B‖ + ‖Tp‖ + ‖Bt‖ := by rw [hI]; ring

set_option maxHeartbeats 2000000 in
/-- **The contour estimate.** -/
theorem contour_estimate (h : VKZeroFreeLogDeriv) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : ℝ → ℂ), (∀ k : ℕ, ContDiff ℝ k F) → ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∀ x, F x ≠ 0 → a ≤ x ∧ x ≤ b) → ∀ c T X M D : ℝ, 1 < c → c ≤ 2 → 3 ≤ T → 1 ≤ X →
      1 / 2 ≤ vkSigma c₀ T →
      (∀ s : ℂ, vkSigma c₀ T ≤ s.re → s.re ≤ c → ‖mellin F s‖ ≤ M * X ^ s.re) →
      (∀ s : ℂ, vkSigma c₀ T ≤ s.re → s.re ≤ c → ‖mellin F s‖ * |s.im| ^ 4 ≤ D * X ^ s.re) →
      ‖smoothTwist F 1 0 - mellin F 1‖ ≤
        2 * T * M * X ^ vkSigma c₀ T * (C * Real.log T) + 4 * D * X ^ c * (C * Real.log T) / T ^ 4 +
          2 * π * D * X ^ c * C / T := by
  obtain ⟨L0, hL0⟩ := zetaH_extends h
  obtain ⟨c₀, hc₀, C₀, hVK⟩ := h
  refine ⟨c₀, hc₀, |C₀|, abs_nonneg _, ?_⟩
  intro F hF a b ha hab hs c T X M D hc hc2 hT hX hσ hM hD
  set σ₁ := vkSigma c₀ T with hσ₁
  set C := |C₀| with hC
  have hC0 : 0 ≤ C := abs_nonneg _
  have hT0 : 0 < T := by linarith
  have hlT : 1 < Real.log T := by
    have : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9; linarith
    linarith [Real.log_le_log (by norm_num) hT]
  have hden : 0 < Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3) := by
    have := Real.log_pos hlT
    positivity
  have hσ1 : σ₁ < 1 := by
    rw [hσ₁, vkSigma]; have := div_pos hc₀ hden; linarith
  have hσc : σ₁ < c := by linarith
  have hFd : Differentiable ℂ (mellin F) :=
    mellin_differentiable (hF 0).continuous (by linarith) hs
  have hXpos : 0 < X := by linarith
  -- VK in usable form
  have hreg : ∀ w : ℂ, σ₁ ≤ w.re → |w.im| ≤ T → w ≠ 1 →
      riemannZeta w ≠ 0 ∧ ‖zetaH w‖ ≤ C * Real.log T := by
    intro w hw him hw1
    have hw' : ((w.re : ℂ) + w.im * I) = w := Complex.re_add_im w
    have := hVK T w.re w.im hT (by unfold InVKRegion; rw [hσ₁, vkSigma] at hw; linarith) him
      (by rwa [hw'])
    rw [hw'] at this
    refine ⟨this.1, ?_⟩
    exact this.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  have hregY : ∀ y : ℝ, T ≤ |y| → ‖zetaH (c + y * I)‖ ≤ C * |y| := by
    intro y hy
    have hy3 : 3 ≤ |y| := by linarith
    have hne : ((c : ℂ) + y * I) ≠ 1 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have hden' : 0 ≤ Real.log |y| ^ ((2 : ℝ) / 3) * Real.log (Real.log |y|) ^ ((1 : ℝ) / 3) := by
      have h1 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
      have h2 : 1 ≤ Real.log |y| := by
        have : (1:ℝ) < Real.log 3 := by
          rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9; linarith
        linarith [Real.log_le_log (by norm_num) hy3]
      have h3 : 0 ≤ Real.log (Real.log |y|) := Real.log_nonneg h2
      positivity
    have := hVK |y| c y hy3 (by
      unfold InVKRegion; have := div_nonneg hc₀.le hden'; linarith) le_rfl hne
    have hlog : Real.log |y| ≤ |y| := by
      have := Real.log_le_sub_one_of_pos (show 0 < |y| by linarith); linarith
    exact this.2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith))).trans
      (mul_le_mul_of_nonneg_left hlog hC0))
  -- the identity
  set g : ℝ → ℂ := fun y => mellin F (c + y * I) * zetaH (c + y * I) with hg
  have hid : smoothTwist F 1 0 - mellin F 1 = -((1 / (2 * π) : ℝ) : ℂ) * ∫ y, g y := by
    have := smoothTwist_sub_main_eq_line hc hc2 hF (by linarith) hab hs (P := 1) (by linarith) 0
    simpa [hg] using this
  -- integrability of `g`
  obtain ⟨K, hK0, hKb, hKc, hKi⟩ := mellin_vertical_facts_line hc hc2 hF (by linarith) hab hs
  obtain ⟨B, hB⟩ := zetaH_bound_line hc
  have hzc : Continuous fun y : ℝ => zetaH (c + y * I) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hw : ((c : ℂ) + y * I) ≠ 1 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have hz : riemannZeta ((c : ℂ) + y * I) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa using hc)
    exact (zetaH_differentiableAt hw hz).continuousAt.comp
      (f := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop)
  have hgc : Continuous g := hKc.mul hzc
  have hgi : Integrable g := by
    refine (hKi.norm.mul_const |B|).mono' hgc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [hg, norm_mul]
    exact mul_le_mul_of_nonneg_left ((hB _ (by simp)).trans (le_abs_self B)) (norm_nonneg _)
  -- the shifted function
  set Hh := Function.update zetaH 1 L0 with hHh
  set G : ℂ → ℂ := fun s => mellin F s * Hh s with hG
  have hGd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → |s.im| ≤ T → DifferentiableAt ℂ G s := by
    intro s h1 h2 h3
    have hw : s = 1 ∨ riemannZeta s ≠ 0 := by
      by_cases h : s = 1
      · exact Or.inl h
      · exact Or.inr (hreg _ h1 h3 h).1
    exact (hFd s).mul (hL0 _ hw)
  have hshift := rect_shift_norm_line (G := G) hσc.le hT0.le hGd
  have hGg : ∫ y in (-T)..T, G (c + y * I) = ∫ y in (-T)..T, g y := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hw : ((c : ℂ) + y * I) ≠ 1 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    simp only [hG, hg, hHh, Function.update_of_ne hw]
  rw [hGg] at hshift
  -- (1) tails
  have hsplit : ∫ y, g y = (∫ y in (-T)..T, g y) + ∫ y in (Set.Ioc (-T) T)ᶜ, g y := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hgi]
  set c2 := 2 * D * X ^ c * C / T with hc2'
  have htailpt : ∀ y ∈ (Set.Ioc (-T) T)ᶜ, ‖g y‖ ≤ c2 * (1 + y ^ 2)⁻¹ := by
    intro y hy
    have hyT : T ≤ |y| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hDy := hD (c + y * I) (by simp; linarith) (by simp)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hDy
    have hz := hregY y hyT
    have hm := norm_nonneg (mellin F (c + y * I))
    have hay : 0 < |y| := by linarith
    have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    rw [hg, norm_mul, hc2', le_mul_inv_iff₀ (by positivity), div_eq_mul_inv]
    have hXc : 0 ≤ X ^ c := by positivity
    -- ‖m‖ ‖z‖ (1 + y²) ≤ ‖m‖ C |y| · 2 |y|² ≤ 2 C ‖m‖ |y|⁴ / T ≤ 2 C D X^c / T
    have h1 : ‖mellin F (c + y * I)‖ * ‖zetaH (c + y * I)‖ * (1 + y ^ 2) ≤
        ‖mellin F (c + y * I)‖ * (C * |y|) * (2 * |y| ^ 2) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hz hm) _ (by positivity) (by positivity)
      rw [hy2]; nlinarith
    have h2 : ‖mellin F (c + y * I)‖ * (C * |y|) * (2 * |y| ^ 2) * T ≤
        2 * C * (‖mellin F (c + y * I)‖ * |y| ^ 4) := by
      have : ‖mellin F (c + y * I)‖ * C * |y| ^ 3 * T ≤ ‖mellin F (c + y * I)‖ * C * |y| ^ 3 * |y| :=
        mul_le_mul_of_nonneg_left hyT (by positivity)
      nlinarith
    have h3 : 2 * C * (‖mellin F (c + y * I)‖ * |y| ^ 4) ≤ 2 * C * (D * X ^ c) :=
      mul_le_mul_of_nonneg_left hDy (by positivity)
    rw [le_mul_inv_iff₀ hT0]
    nlinarith
  have htail : ‖∫ y in (Set.Ioc (-T) T)ᶜ, g y‖ ≤ 2 * π * D * X ^ c * C / T := by
    calc ‖∫ y in (Set.Ioc (-T) T)ᶜ, g y‖ ≤ ∫ y in (Set.Ioc (-T) T)ᶜ, c2 * (1 + y ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _).integrableOn
            ((ae_restrict_iff' measurableSet_Ioc.compl).2 (Eventually.of_forall htailpt))
      _ ≤ ∫ y, c2 * (1 + y ^ 2)⁻¹ := by
          refine setIntegral_le_integral (integrable_inv_one_add_sq.const_mul _)
            (Eventually.of_forall fun y => ?_)
          have : 0 ≤ c2 := by
            have := (htailpt (T + 1) (by simp)).trans' (norm_nonneg _)
            have hp : 0 < (1 + (T + 1) ^ 2)⁻¹ := by positivity
            exact nonneg_of_mul_nonneg_left this hp
          positivity
      _ = c2 * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
      _ = 2 * π * D * X ^ c * C / T := by rw [hc2']; ring
  -- (2) main line
  have hleftpt : ∀ y : ℝ, |y| ≤ T → ‖G (σ₁ + y * I)‖ ≤ M * X ^ σ₁ * (C * Real.log T) := by
    intro y hy
    have hw1 : (σ₁ : ℂ) + y * I ≠ 1 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have h3 := (hreg (σ₁ + y * I) (by simp) (by simpa using hy) hw1).2
    have h1 := hM (σ₁ + y * I) (by simp) (by simp; linarith)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero] at h1
    simp only [hG, hHh, Function.update_of_ne hw1, norm_mul]
    exact mul_le_mul h1 h3 (norm_nonneg _) (by
      have := (norm_nonneg _).trans h1; exact this)
  have hleft : ‖∫ y in (-T)..T, G (σ₁ + y * I)‖ ≤ 2 * T * M * X ^ σ₁ * (C * Real.log T) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
      (C := M * X ^ σ₁ * (C * Real.log T)) (f := fun y => G (σ₁ + y * I)) (fun y hy => by
        rw [Set.uIoc_of_le (by linarith)] at hy
        exact hleftpt y (abs_le.2 ⟨hy.1.le, hy.2⟩))
    rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith)] at this
    linarith
  -- (3) horizontal sides
  have hae : ∀ᵐ x : ℝ, x ≠ 1 := by
    rw [ae_iff]; simp
  have hhor : ∀ v : ℝ, |v| = T → ‖∫ x in σ₁..c, G (x + v * I)‖ ≤ 2 * D * X ^ c * (C * Real.log T) / T ^ 4 := by
    intro v hv
    set c3 := D * X ^ c / T ^ 4 * (C * Real.log T) with hc3
    have hpt : ∀ᵐ x : ℝ, x ∈ Set.uIoc σ₁ c → ‖G (x + v * I)‖ ≤ c3 := by
      filter_upwards [hae] with x hx1 hx
      rw [Set.uIoc_of_le hσc.le] at hx
      have h1 := hD (x + v * I) (by simp; linarith [hx.1]) (by simp; linarith [hx.2])
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add] at h1
      rw [hv] at h1
      have hXx : X ^ x ≤ X ^ c := Real.rpow_le_rpow_of_exponent_le hX hx.2
      have hF : ‖mellin F (x + v * I)‖ ≤ D * X ^ c / T ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        have : 0 ≤ D := by
          have := (mul_nonneg (norm_nonneg _) (by positivity : (0:ℝ) ≤ T ^ 4)).trans h1
          exact nonneg_of_mul_nonneg_left this (by positivity)
        nlinarith
      have hw1 : (x : ℂ) + v * I ≠ 1 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; exact hx1 this
      have h3 := (hreg ((x : ℂ) + v * I) (by simp; linarith [hx.1]) (by simp [hv]) hw1).2
      simp only [hG, hHh, Function.update_of_ne hw1, norm_mul]
      exact mul_le_mul hF h3 (norm_nonneg _) ((norm_nonneg _).trans hF)
    have hc30 : 0 ≤ c3 := by
      have hD0 := hD (c : ℂ) (by simp; linarith) (by simp)
      simp only [ofReal_im, abs_zero, ofReal_re] at hD0
      norm_num at hD0
      have : 0 ≤ D := nonneg_of_mul_nonneg_left hD0 (by positivity)
      have : 0 ≤ Real.log T := by linarith
      rw [hc3]; positivity
    calc ‖∫ x in σ₁..c, G (x + v * I)‖ ≤ c3 * |c - σ₁| :=
          intervalIntegral.norm_integral_le_of_norm_le_const_ae hpt
      _ ≤ c3 * 2 := by
          apply mul_le_mul_of_nonneg_left _ hc30
          rw [abs_of_pos (by linarith)]; linarith
      _ = 2 * D * X ^ c * (C * Real.log T) / T ^ 4 := by rw [hc3]; ring
  have htop := hhor T (abs_of_pos hT0)
  have hbot := hhor (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hbot' : ∫ x in σ₁..c, G (x - T * I) = ∫ x in σ₁..c, G (x + (-T : ℝ) * I) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    congr 1; push_cast; ring
  rw [← hbot'] at hbot
  -- (4) assemble
  have hint : ‖∫ y, g y‖ ≤ 2 * T * M * X ^ σ₁ * (C * Real.log T) +
      4 * D * X ^ c * (C * Real.log T) / T ^ 4 + 2 * π * D * X ^ c * C / T := by
    calc ‖∫ y, g y‖ ≤ ‖∫ y in (-T)..T, g y‖ + ‖∫ y in (Set.Ioc (-T) T)ᶜ, g y‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ (‖∫ y in (-T)..T, G (σ₁ + y * I)‖ + ‖∫ x in σ₁..c, G (x + T * I)‖ +
            ‖∫ x in σ₁..c, G (x - T * I)‖) + ‖∫ y in (Set.Ioc (-T) T)ᶜ, g y‖ := by gcongr
      _ ≤ (2 * T * M * X ^ σ₁ * (C * Real.log T) + 2 * D * X ^ c * (C * Real.log T) / T ^ 4 +
            2 * D * X ^ c * (C * Real.log T) / T ^ 4) + 2 * π * D * X ^ c * C / T := by gcongr
      _ = _ := by ring
  rw [hid, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2π : 1 / (2 * π) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  calc 1 / (2 * π) * ‖∫ y, g y‖ ≤ 1 * ‖∫ y, g y‖ :=
        mul_le_mul_of_nonneg_right h2π (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hint

end LeanFormalizations.Erdos385.PNTVK

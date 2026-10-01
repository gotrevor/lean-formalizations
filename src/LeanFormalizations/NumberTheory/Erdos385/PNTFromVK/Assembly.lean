/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.PNTFromVK.Kernel
import LeanFormalizations.NumberTheory.Erdos385.PNTFromVK.Contour
import LeanFormalizations.Literature.Erdos385VK

/-!
# Phase E3e helper: assembly of the de la Vallée Poussin PNT

At scale `x`, `L = log x`: `η = exp(−√L)`, `T = η^{−4} = exp(4√L)`, `X = 2x`, `c = 1 + 1/log X`,
weight `wt (e^η) B η` (lower support edge exactly `1`), `B = x e^{±η}`.

* Sandwich: `ψ(B e^{−η}) ≤ Re Σ Λ(n) wt(n) ≤ ψ(B e^η)` (`Λ(1) = 0`, `e^{2η} < 2`).
* Main term `∫ wt ∈ [B e^{−η} − e^{2η}, B e^η − 1]` (`mellin_wt_one`).
* Error (`contour_estimate`, `M = 4K₀`, `D = 2K₃ η^{−3}`): the tail is `≍ x η`, the horizontal
  sides are tiny, and the main line is `x · T · √L · exp(−(1−σ₁)L) ≪ x η` because
  `(1 − σ₁) L ≥ (4√L)^{−3/4} L ≍ L^{5/8} ≫ 5√L`.
-/

open Real Filter MeasureTheory Complex Asymptotics
open scoped Chebyshev

namespace LeanFormalizations.Erdos385.PNTVK

open LeanFormalizations.Erdos385 LeanFormalizations.Literature

/-- **Uniform Mellin bounds for the weight.** -/
theorem wt_mellin_bounds : ∃ K₀ K₃ : ℝ, 0 ≤ K₀ ∧ 0 ≤ K₃ ∧
    ∀ A B η X : ℝ, 0 < A → A ≤ B → 0 < η → η ≤ 1 → B ≤ X → ∀ s : ℂ, 1 / 2 ≤ s.re →
      s.re ≤ 2 →
      ‖mellin (wt A B η) s‖ ≤ 4 * K₀ * X ^ s.re ∧
      ‖mellin (wt A B η) s‖ * |s.im| ^ 4 ≤ 2 * K₃ * η⁻¹ ^ 3 * X ^ s.re := by
  have hsφ : ∀ x, phi x ≠ 0 → Real.exp (-1) ≤ x ∧ x ≤ Real.exp 1 := fun x h => phi_support h
  have hle : Real.exp (-1) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
  obtain ⟨K₀, h0⟩ := mellin_strip_decay 0 phi_contDiff (Real.exp_pos _) hle hsφ 0 2
  obtain ⟨K₃, h3⟩ := mellin_strip_decay 3 phi_contDiff (Real.exp_pos _) hle hsφ 0 2
  refine ⟨|K₀|, |K₃|, abs_nonneg _, abs_nonneg _, fun A B η X hA hAB hη hη1 hBX s hs1 hs2 => ?_⟩
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hX : 0 < X := lt_of_lt_of_le hB hBX
  set σ := s.re
  have hσ0 : 0 ≤ σ := by linarith
  have hN : σ ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm s)
  have hN0 : 0 < ‖s‖ := by linarith
  have hs0 : s ≠ 0 := norm_pos_iff.1 hN0
  have hw1 : 0 ≤ ((η : ℂ) * s).re := by simp; positivity
  have hw2 : ((η : ℂ) * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; nlinarith
  have e0 := h0 _ hw1 hw2
  have e3 := h3 _ hw1 hw2
  simp only [pow_zero, one_mul] at e0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη, mul_pow] at e3
  set m := ‖mellin phi ((η : ℂ) * s)‖
  have hm : 0 ≤ m := norm_nonneg _
  set E := ‖(B : ℂ) ^ s - (A : ℂ) ^ s‖
  have hE : E ≤ 2 * X ^ σ := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hB, Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have := Real.rpow_le_rpow hB.le hBX hσ0
    have := Real.rpow_le_rpow hA.le (hAB.trans hBX) hσ0
    linarith
  have hE0 : 0 ≤ E := norm_nonneg _
  have hmel : ‖mellin (wt A B η) s‖ = E * m / ‖s‖ := by
    rw [mellin_wt hA hAB hη hs0, norm_div, norm_mul]
  rw [hmel]
  have hXσ : 0 ≤ X ^ σ := by positivity
  constructor
  · rw [div_le_iff₀ hN0]
    have : E * m ≤ 2 * X ^ σ * |K₀| := mul_le_mul hE (e0.trans (le_abs_self _)) hm (by positivity)
    have h2 : 4 * |K₀| * X ^ σ * (1 / 2) ≤ 4 * |K₀| * X ^ σ * ‖s‖ :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · have him : |s.im| ^ 4 ≤ ‖s‖ ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm s) 4
    have hη3 : 0 < η ^ 3 := by positivity
    have hmN : m * ‖s‖ ^ 3 ≤ |K₃| * η⁻¹ ^ 3 := by
      rw [inv_pow, le_mul_inv_iff₀ hη3]
      nlinarith [le_abs_self K₃]
    calc E * m / ‖s‖ * |s.im| ^ 4 ≤ E * m / ‖s‖ * ‖s‖ ^ 4 :=
          mul_le_mul_of_nonneg_left him (by positivity)
      _ = E * (m * ‖s‖ ^ 3) := by field_simp
      _ ≤ (2 * X ^ σ) * (|K₃| * η⁻¹ ^ 3) := mul_le_mul hE hmN (by positivity) (by positivity)
      _ = _ := by ring

/-- **The sandwich.**  With lower edge `A = e^η` (`η ≤ 1/4`), the weighted prime sum lies between
`ψ(B e^{−η})` and `ψ(B e^η)`. -/
theorem smoothTwist_wt_sandwich {B η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hB : Real.exp η ≤ B) :
    (smoothTwist (wt (Real.exp η) B η) 1 0).im = 0 ∧
      ψ (B * Real.exp (-η)) ≤ (smoothTwist (wt (Real.exp η) B η) 1 0).re ∧
      (smoothTwist (wt (Real.exp η) B η) 1 0).re ≤ ψ (B * Real.exp η) := by
  set A := Real.exp η
  have hA : 0 < A := Real.exp_pos _
  have hAB : A ≤ B := hB
  have hBp : 0 < B := lt_of_lt_of_le hA hB
  set N := ⌊B * Real.exp η⌋₊ + 1
  have hzero : ∀ n ∉ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (n : ℂ) ^ (-(((0:ℝ) : ℂ) * I)) * wt A B η (n / 1) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have : B * Real.exp η < n := by
      have := Nat.lt_floor_add_one (B * Real.exp η)
      have h2 : ((⌊B * Real.exp η⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2; linarith
    simp [wt, wr_zero_right hA hBp hAB hη this]
  have hS : smoothTwist (wt A B η) 1 0 =
      ((∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * wr A B η n : ℝ) : ℂ) := by
    rw [smoothTwist, tsum_eq_sum hzero]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [wt]
  rw [hS, Complex.ofReal_re, Complex.ofReal_im]
  have hΛ : ∀ n, 0 ≤ ArithmeticFunction.vonMangoldt n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  have hwb := fun x => wr_bounds hA hAB hη x
  refine ⟨rfl, ?_, ?_⟩
  · -- lower
    have hfl : ⌊B * Real.exp (-η)⌋₊ ≤ ⌊B * Real.exp η⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hBp.le)
    rw [Chebyshev.psi_eq_sum_Icc]
    have hsub : Finset.Icc 0 ⌊B * Real.exp (-η)⌋₊ ⊆ Finset.range N := by
      intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
    have hA2 : A * Real.exp η < 2 := by
      rw [← Real.exp_add]
      have h1 : Real.exp (η + η) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
      have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h3 := Real.exp_one_lt_d9
      have h4 : Real.exp (1 / 2) < 2 := by nlinarith [Real.exp_pos (1 / 2)]
      linarith
    calc ∑ n ∈ Finset.Icc 0 ⌊B * Real.exp (-η)⌋₊, ArithmeticFunction.vonMangoldt n
        = ∑ n ∈ Finset.Icc 0 ⌊B * Real.exp (-η)⌋₊, ArithmeticFunction.vonMangoldt n * wr A B η n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rcases eq_or_ne (ArithmeticFunction.vonMangoldt n) 0 with h0 | h0
          · simp [h0]
          have h2 : 2 ≤ n := (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 h0).two_le
          have h2' : (2 : ℝ) ≤ n := by exact_mod_cast h2
          rw [Finset.mem_Icc] at hn
          have hnB : (n : ℝ) ≤ B * Real.exp (-η) :=
            (Nat.le_floor_iff (by positivity)).1 hn.2
          rw [(hwb n).2.2 (by linarith) hnB, mul_one]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          mul_nonneg (hΛ n) (hwb n).1
  · -- upper
    rw [Chebyshev.psi_eq_sum_Icc]
    have : Finset.range N = Finset.Icc 0 ⌊B * Real.exp η⌋₊ := by
      ext n; simp [N, Nat.lt_succ_iff]
    rw [← this]
    exact Finset.sum_le_sum fun n _ => by
      have := (hwb n).2.1
      nlinarith [hΛ n]

/-- **The main-line exponent beats `5√L`.** -/
theorem mainLine_eventually :
    ∀ᶠ L : ℝ in atTop, Real.sqrt L * Real.exp (5 * Real.sqrt L -
      (4 * Real.sqrt L) ^ (-(3 / 4 : ℝ)) * L) ≤ 1 := by
  filter_upwards [eventually_ge_atTop ((82944 : ℝ) ^ 2)] with L hL
  set r := Real.sqrt L
  have hr : 82944 ≤ r := by
    rw [show (82944 : ℝ) = Real.sqrt (82944 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hrL : r ^ 2 = L := Real.sq_sqrt hL0
  have h4r : 0 < 4 * r := by linarith
  set q := (4 * r) ^ ((3 / 4 : ℝ))
  have hq0 : 0 < q := Real.rpow_pos_of_pos h4r _
  have hq4 : q ^ 4 = (4 * r) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h4r.le]; norm_num
  have hqr : q ≤ r / 6 := by
    refine (pow_le_pow_iff_left₀ hq0.le (by linarith) (by norm_num : (4:ℕ) ≠ 0)).1 ?_
    rw [hq4]
    have : 0 ≤ r ^ 3 := by positivity
    nlinarith
  have hneg : (4 * r) ^ (-(3 / 4 : ℝ)) = q⁻¹ := Real.rpow_neg h4r.le _
  have hterm : 6 * r ≤ (4 * r) ^ (-(3 / 4 : ℝ)) * L := by
    rw [hneg, ← hrL, inv_mul_eq_div, le_div_iff₀ hq0]
    nlinarith
  have hexp : Real.exp (5 * r - (4 * r) ^ (-(3 / 4 : ℝ)) * L) ≤ Real.exp (-r) :=
    Real.exp_le_exp.2 (by linarith)
  have h1 : r * Real.exp (-r) ≤ 1 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
    linarith [Real.add_one_le_exp r]
  calc r * Real.exp (5 * r - (4 * r) ^ (-(3 / 4 : ℝ)) * L) ≤ r * Real.exp (-r) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ ≤ 1 := h1

/-- **PNT with error `x η`, `η = exp(−√log x)`.** -/
theorem psi_sub_le (h : VKZeroFreeLogDeriv) :
    ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |ψ x - x| ≤ K * (x * Real.exp (-Real.sqrt (Real.log x))) := by
  sorry

theorem dlvp_of_VK (h : VKZeroFreeLogDeriv) : DLVPStatement := by
  obtain ⟨K, hK⟩ := psi_sub_le h
  refine ⟨1, one_pos, IsBigO.of_bound K ?_⟩
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x * Real.exp (-1 * Real.sqrt (Real.log x)) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0]
  simpa only [Pi.sub_apply, id, neg_mul, one_mul] using hx

end LeanFormalizations.Erdos385.PNTVK

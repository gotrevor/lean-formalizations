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

/-- **The three contour error terms are `≪ x η`.** -/
theorem err_le {K₀ K₃ C x η r T X Xc XS E1 lT : ℝ} (hK₀ : 0 ≤ K₀) (hK₃ : 0 ≤ K₃) (hC : 0 ≤ C)
    (hx : 0 < x) (hη0 : 0 < η) (hη1 : η ≤ 1) (hr : 0 ≤ r) (hrη : r * η ≤ 1) (hT : T = η⁻¹ ^ 4)
    (hX : X = 2 * x) (hXc : Xc = Real.exp 1 * X) (hlT : lT = 4 * r) (hXS : XS ≤ X * E1)
    (hE1 : T * E1 * r ≤ η) (hE1p : 0 ≤ E1) :
    2 * T * (4 * K₀) * XS * (C * lT) + 4 * (2 * K₃ * η⁻¹ ^ 3) * Xc * (C * lT) / T ^ 4 +
      2 * π * (2 * K₃ * η⁻¹ ^ 3) * Xc * C / T ≤
      (64 * K₀ * C + 192 * K₃ * C + 96 * K₃ * C) * (x * η) := by
  subst hT hX hXc hlT
  have hηi : 0 < η⁻¹ := inv_pos.2 hη0
  have hT0 : 0 ≤ η⁻¹ ^ 4 := by positivity
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hπ : π ≤ 4 := by linarith [Real.pi_lt_four]
  have t1 : 2 * η⁻¹ ^ 4 * (4 * K₀) * XS * (C * (4 * r)) ≤ 64 * K₀ * C * (x * η) := by
    have h1 : 2 * η⁻¹ ^ 4 * (4 * K₀) * XS * (C * (4 * r)) ≤
        2 * η⁻¹ ^ 4 * (4 * K₀) * (2 * x * E1) * (C * (4 * r)) := by
      have : 0 ≤ 2 * η⁻¹ ^ 4 * (4 * K₀) := by positivity
      have h2 : 0 ≤ C * (4 * r) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXS this) h2
    have h2 : 2 * η⁻¹ ^ 4 * (4 * K₀) * (2 * x * E1) * (C * (4 * r)) =
        64 * K₀ * C * x * (η⁻¹ ^ 4 * E1 * r) := by ring
    have h3 : 64 * K₀ * C * x * (η⁻¹ ^ 4 * E1 * r) ≤ 64 * K₀ * C * x * η :=
      mul_le_mul_of_nonneg_left hE1 (by positivity)
    linarith
  have t2 : 4 * (2 * K₃ * η⁻¹ ^ 3) * (Real.exp 1 * (2 * x)) * (C * (4 * r)) / (η⁻¹ ^ 4) ^ 4 ≤
      192 * K₃ * C * (x * η) := by
    have e : 4 * (2 * K₃ * η⁻¹ ^ 3) * (Real.exp 1 * (2 * x)) * (C * (4 * r)) / (η⁻¹ ^ 4) ^ 4 =
        64 * Real.exp 1 * (K₃ * C * x) * ((r * η) * η ^ 12) := by
      field_simp; ring
    rw [e]
    have h12 : (r * η) * η ^ 12 ≤ 1 :=
      mul_le_one₀ hrη (by positivity) (pow_le_one₀ hη0.le hη1)
    have hb : 0 ≤ K₃ * C * x := by positivity
    have h4 : (r * η) * η ^ 12 ≤ η := by
      have : η ^ 12 ≤ 1 := pow_le_one₀ hη0.le hη1
      calc (r * η) * η ^ 12 = (r * η) * η ^ 11 * η := by ring
        _ ≤ 1 * 1 * η := by
          gcongr
          exact pow_le_one₀ hη0.le hη1
        _ = η := by ring
    have : 64 * Real.exp 1 * (K₃ * C * x) * ((r * η) * η ^ 12) ≤ 64 * 3 * (K₃ * C * x) * η := by
      gcongr
    nlinarith
  have t3 : 2 * π * (2 * K₃ * η⁻¹ ^ 3) * (Real.exp 1 * (2 * x)) * C / η⁻¹ ^ 4 ≤
      96 * K₃ * C * (x * η) := by
    have e : 2 * π * (2 * K₃ * η⁻¹ ^ 3) * (Real.exp 1 * (2 * x)) * C / η⁻¹ ^ 4 =
        8 * (π * Real.exp 1) * (K₃ * C * x * η) := by
      field_simp; ring
    rw [e]
    have hpe : π * Real.exp 1 ≤ 12 := by nlinarith [Real.pi_pos, Real.exp_pos 1]
    have : 0 ≤ K₃ * C * x * η := by positivity
    nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **PNT with error `x η`, `η = exp(−√log x)`.** -/
theorem psi_sub_le (h : VKZeroFreeLogDeriv) :
    ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |ψ x - x| ≤ K * (x * Real.exp (-Real.sqrt (Real.log x))) := by
  obtain ⟨c₀, hc₀, C, hC, hcont⟩ := contour_estimate h
  obtain ⟨K₀, K₃, hK₀, hK₃, hwb⟩ := wt_mellin_bounds
  refine ⟨64 * K₀ * C + 192 * K₃ * C + 96 * K₃ * C + 6, ?_⟩
  have hTt : Tendsto (fun x : ℝ => Real.exp (4 * Real.sqrt (Real.log x))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop
      (by norm_num))
  have hvk := hTt.eventually ((vk_width_eventually hc₀ (ε := 1 / 12) (by norm_num)).and
    (eventually_ge_atTop (3 : ℝ)))
  have hml := Real.tendsto_log_atTop.eventually mainLine_eventually
  have hsq : ∀ᶠ x : ℝ in atTop, Real.log 4 ≤ Real.sqrt (Real.log x) :=
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop _)
  have hlog1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hvk, hml, hsq, hlog1, eventually_ge_atTop (3 : ℝ)] with x hvx hmlx hsqx hL1 hx3
  obtain ⟨⟨hv1, hv2⟩, hT3⟩ := hvx
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt L := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = Real.exp (-r) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = Real.exp (4 * r) := ⟨_, rfl⟩
  rw [← hL] at hmlx hsqx hL1
  rw [← hr] at hmlx hsqx
  rw [← hL, ← hr, ← hT] at hv1 hv2 hT3
  rw [← hL, ← hr, ← hη]
  have hx0 : 0 < x := by linarith
  have hr1 : 1 ≤ r := by rw [hr, show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL1
  have hη0 : 0 < η := by rw [hη]; exact Real.exp_pos _
  have hη4 : η ≤ 1 / 4 := by
    rw [hη, show (1 / 4 : ℝ) = Real.exp (-Real.log 4) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    exact Real.exp_le_exp.2 (by linarith)
  have hη1 : η ≤ 1 := by linarith
  have hrη : r * η ≤ 1 := by
    rw [hη, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]; linarith [Real.add_one_le_exp r]
  have hTη : T = η⁻¹ ^ 4 := by
    rw [hT, hη, Real.exp_neg, inv_inv, ← Real.exp_nat_mul]; norm_num
  have hlogT : Real.log T = 4 * r := by rw [hT, Real.log_exp]
  obtain ⟨X, hX⟩ : ∃ X, X = 2 * x := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; positivity
  have hlogX : L ≤ Real.log X := by rw [hL, hX]; exact Real.log_le_log hx0 (by linarith)
  have hlX1 : 1 ≤ Real.log X := le_trans hL1 hlogX
  obtain ⟨c, hc⟩ : ∃ c, c = 1 + 1 / Real.log X := ⟨_, rfl⟩
  have hc1 : 1 < c := by
    have : 0 < 1 / Real.log X := by positivity
    linarith
  have hc2 : c ≤ 2 := by
    have : 1 / Real.log X ≤ 1 := by rw [div_le_one (by linarith)]; exact hlX1
    linarith
  have hXc : X ^ c = Real.exp 1 * X := by
    rw [Real.rpow_def_of_pos hX0, show Real.log X * c = Real.log X + 1 by
      rw [hc]; field_simp, Real.exp_add, Real.exp_log hX0, mul_comm]
  set ηT := c₀ / (Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3)) with hηTdef
  have hσ : vkSigma c₀ T = 1 - ηT := rfl
  have hηT : (4 * r) ^ (-(3 / 4 : ℝ)) ≤ ηT := by
    rw [Real.rpow_neg (by positivity), ← hlogT]
    have : ((2 : ℝ) / 3 + 1 / 12) = 3 / 4 := by norm_num
    rw [this] at hv1; exact hv1
  have hσhalf : 1 / 2 ≤ vkSigma c₀ T := by rw [hσ]; linarith
  set E1 := Real.exp (-((4 * r) ^ (-(3 / 4 : ℝ)) * L)) with hE1def
  have hXσ : X ^ vkSigma c₀ T ≤ X * E1 := by
    rw [hσ, Real.rpow_def_of_pos hX0, show Real.log X * (1 - ηT) = Real.log X + -(ηT * Real.log X) by ring,
      Real.exp_add, Real.exp_log hX0]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hX0.le
    have h0 : 0 ≤ (4 * r) ^ (-(3 / 4 : ℝ)) := by positivity
    have : (4 * r) ^ (-(3 / 4 : ℝ)) * L ≤ ηT * Real.log X :=
      mul_le_mul hηT hlogX (by linarith) (h0.trans hηT)
    linarith
  have hE1 : T * E1 * r ≤ η := by
    have : T * E1 * r = η * (r * Real.exp (5 * r - (4 * r) ^ (-(3 / 4 : ℝ)) * L)) := by
      rw [hT, hη, hE1def, show 5 * r - (4 * r) ^ (-(3 / 4 : ℝ)) * L =
        r + 4 * r + -((4 * r) ^ (-(3 / 4 : ℝ)) * L) by ring, Real.exp_add, Real.exp_add, Real.exp_neg r]
      field_simp
    rw [this]; exact mul_le_of_le_one_right hη0.le hmlx
  have hErr := err_le (XS := X ^ vkSigma c₀ T) (lT := Real.log T) hK₀ hK₃ hC hx0 hη0 hη1
    (by rw [hr]; exact Real.sqrt_nonneg _) hrη hTη hX hXc hlogT hXσ hE1 (Real.exp_pos _).le
  set Err := 64 * K₀ * C + 192 * K₃ * C + 96 * K₃ * C
  -- e^{2η} < 2
  have he2 : Real.exp (2 * η) ≤ 2 := by
    have h1 : Real.exp (2 * η) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2)]
  -- one side
  have key : ∀ B : ℝ, Real.exp (2 * η) * Real.exp η ≤ B → B ≤ x * Real.exp η →
      |(smoothTwist (wt (Real.exp η) B η) 1 0).re - (mellin (wt (Real.exp η) B η) 1).re| ≤
        Err * (x * η) := by
    intro B hB1 hB2
    have hAe : Real.exp η ≤ Real.exp (2 * η) * Real.exp η := by
      have := Real.one_le_exp (show 0 ≤ 2 * η by linarith)
      exact le_mul_of_one_le_left (Real.exp_pos η).le this
    have hAB : Real.exp η ≤ B := hAe.trans hB1
    have hBp : 0 < B := lt_of_lt_of_le (Real.exp_pos _) hAB
    have hBX : B ≤ X := by
      rw [hX]
      have : Real.exp η ≤ 2 := le_trans (Real.exp_le_exp.2 (by linarith)) he2
      have := mul_le_mul_of_nonneg_left this hx0.le
      linarith
    have hsupp : ∀ y, wt (Real.exp η) B η y ≠ 0 → 1 ≤ y ∧ y ≤ B * Real.exp η := by
      intro y hy
      have := wt_support (Real.exp_pos η) hAB hη0 hy
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      exact this
    have hb : 1 ≤ B * Real.exp η := by
      have h1 := Real.one_le_exp hη0.le
      exact one_le_mul_of_one_le_of_one_le (h1.trans hAB) h1
    have hT3' : 3 ≤ T := hT3
    have hc0 := hcont (wt (Real.exp η) B η) (wt_contDiff (Real.exp_pos η) hAB hη0) 1 (B * Real.exp η)
      le_rfl hb hsupp c T X (4 * K₀) (2 * K₃ * η⁻¹ ^ 3) hc1 hc2 hT3' (by linarith) hσhalf
      (fun s h1 h2 => (hwb _ B η X (Real.exp_pos η) hAB hη0 hη1 hBX s (by linarith) (by linarith)).1)
      (fun s h1 h2 => (hwb _ B η X (Real.exp_pos η) hAB hη0 hη1 hBX s (by linarith) (by linarith)).2)
    calc _ = |(smoothTwist (wt (Real.exp η) B η) 1 0 - mellin (wt (Real.exp η) B η) 1).re| := by
          rw [Complex.sub_re]
      _ ≤ ‖smoothTwist (wt (Real.exp η) B η) 1 0 - mellin (wt (Real.exp η) B η) 1‖ :=
          Complex.abs_re_le_norm _
      _ ≤ _ := hc0
      _ ≤ _ := hErr
  have hee : ∀ u : ℝ, Real.exp u * Real.exp (-u) = 1 := fun u => by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hx2η : Real.exp (2 * η) ≤ x := by linarith
  have hx4η : Real.exp (4 * η) ≤ x := by
    have := Real.exp_le_exp.2 (show 4 * η ≤ 1 by linarith)
    have := Real.exp_one_lt_d9; linarith
  have e2 : Real.exp (2 * η) = Real.exp η * Real.exp η := by rw [← Real.exp_add]; ring_nf
  have em2 : Real.exp (-(2 * η)) = Real.exp (-η) * Real.exp (-η) := by rw [← Real.exp_add]; ring_nf
  have h4 : |2 * η| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
  have h4' : |-(2 * η)| ≤ 1 := by rw [abs_neg]; exact h4
  have hup := abs_exp_sub_one_le h4
  have hdn := abs_exp_sub_one_le h4'
  rw [abs_of_pos (by linarith : 0 < 2 * η)] at hup
  rw [abs_neg, abs_of_pos (by linarith : 0 < 2 * η)] at hdn
  have hxη : 1 ≤ x * η := by
    have hrL : r ≤ L := by
      rw [hr]; calc Real.sqrt L ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = L := Real.sqrt_sq (by linarith)
    rw [hη, show x = Real.exp L by rw [hL, Real.exp_log hx0], ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hErr0 : 0 ≤ Err * (x * η) := by positivity
  -- upper bound
  have hU : ψ x - x ≤ (4 + Err) * (x * η) := by
    set B := x * Real.exp η
    have hB1 : Real.exp (2 * η) * Real.exp η ≤ B := mul_le_mul_of_nonneg_right hx2η (Real.exp_pos _).le
    have k := key B hB1 le_rfl
    have sw := smoothTwist_wt_sandwich hη0 hη4 ((le_mul_of_one_le_left (Real.exp_pos η).le
      (Real.one_le_exp (by linarith))).trans hB1)
    have hBx : B * Real.exp (-η) = x := by rw [mul_assoc, hee, mul_one]
    rw [hBx] at sw
    have mw := mellin_wt_one (Real.exp_pos η) (A := Real.exp η) (B := B)
      (by rw [hBx, ← e2]; exact hx2η) hη0
    have hm : (mellin (wt (Real.exp η) B η) 1).re ≤ x * Real.exp (2 * η) := by
      have := mw.2.2
      have : B * Real.exp η = x * Real.exp (2 * η) := by rw [e2]; ring
      have : 0 ≤ Real.exp η * Real.exp (-η) := by positivity
      linarith
    have := (abs_le.1 k).2
    have hp : x * (Real.exp (2 * η) - 1) ≤ x * (2 * (2 * η)) :=
      mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hup) hx0.le
    linarith [sw.2.1]
  -- lower bound
  have hD : x - ψ x ≤ (6 + Err) * (x * η) := by
    set B := x * Real.exp (-η)
    have hB1 : Real.exp (2 * η) * Real.exp η ≤ B := by
      have : Real.exp (2 * η) * Real.exp η * Real.exp η ≤ x := by
        rw [mul_assoc, ← e2, ← Real.exp_add]; ring_nf; ring_nf at hx4η; exact hx4η
      calc _ = Real.exp (2 * η) * Real.exp η * Real.exp η * Real.exp (-η) := by
            rw [mul_assoc _ (Real.exp η), hee, mul_one]
        _ ≤ x * Real.exp (-η) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    have hB2 : B ≤ x * Real.exp η :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hx0.le
    have k := key B hB1 hB2
    have sw := smoothTwist_wt_sandwich hη0 hη4 ((le_mul_of_one_le_left (Real.exp_pos η).le
      (Real.one_le_exp (by linarith))).trans hB1)
    have hBx : B * Real.exp η = x := by rw [mul_assoc, mul_comm (Real.exp (-η)), hee, mul_one]
    rw [hBx] at sw
    have hBm : B * Real.exp (-η) = x * Real.exp (-(2 * η)) := by rw [em2]; ring
    have hAB' : Real.exp η * Real.exp η ≤ B * Real.exp (-η) := by
      rw [← e2, hBm]
      calc Real.exp (2 * η) = Real.exp (4 * η) * Real.exp (-(2 * η)) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ x * Real.exp (-(2 * η)) := mul_le_mul_of_nonneg_right hx4η (Real.exp_pos _).le
    have mw := mellin_wt_one (Real.exp_pos η) hAB' hη0
    have hm : x * Real.exp (-(2 * η)) - 2 ≤ (mellin (wt (Real.exp η) B η) 1).re := by
      have := mw.2.1
      have : B * Real.exp (-η) = x * Real.exp (-(2 * η)) := by rw [em2]; ring
      have : Real.exp η * Real.exp η ≤ 2 := by rw [← e2]; exact he2
      linarith
    have := (abs_le.1 k).1
    have hp : x * (1 - Real.exp (-(2 * η))) ≤ x * (2 * (2 * η)) := by
      refine mul_le_mul_of_nonneg_left ?_ hx0.le
      have := neg_abs_le (Real.exp (-(2 * η)) - 1); linarith
    linarith [sw.2.2]
  rw [abs_le]
  constructor <;> linarith

theorem dlvp_of_VK (h : VKZeroFreeLogDeriv) : DLVPStatement := by
  obtain ⟨K, hK⟩ := psi_sub_le h
  refine ⟨1, one_pos, IsBigO.of_bound K ?_⟩
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x * Real.exp (-1 * Real.sqrt (Real.log x)) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0]
  simpa only [Pi.sub_apply, id, neg_mul, one_mul] using hx

end LeanFormalizations.Erdos385.PNTVK

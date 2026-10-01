/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385AlmostAll
import LeanFormalizations.Literature.Erdos385VK
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Landau's method, layer 1: interfaces (phase E2e)

Notation for height `T` (large): `L = log T`, `φ = log log T`, `w = vkW T = 1/(L^{2/3} φ^{1/3})`,
`θ = vkTheta T = φ · w = (φ/L)^{2/3}` (the Richert width).  Landau discs are centred at
`1 + θ + it` with radius `2θ`.

Named inputs (each a disclosed `sorry` until proved):
* `landau_neg_re_upper` — FinalBound applied to `ζ` with only non-negative zero terms kept (Z1);
* `landau_logderiv_bound` — FinalBound with every zero at distance `≥ η` (Z2);
* `logDeriv_zeta_dirichlet_bound` — `|ζ'/ζ(σ+it)| ≤ 1/(σ−1) + C` for `σ > 1` (D3);
* `three_four_one` — `3 Re(−ζ'/ζ)(σ) + 4 Re(−ζ'/ζ)(σ+it) + Re(−ζ'/ζ)(σ+2it) ≥ 0` (D2);
* `vk_asymp` — the elementary asymptotics of `L, φ, w`.
Proved from these: `vk_zero_free` (3-4-1) and `vk_large_height_of` (the log-derivative bound).
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature Complex

/-- The VK width `1 / ((log T)^{2/3} (log log T)^{1/3})`. -/
noncomputable def vkW (T : ℝ) : ℝ :=
  1 / (Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3))

/-- The Richert width `θ = log log T · vkW T`. -/
noncomputable def vkTheta (T : ℝ) : ℝ := Real.log (Real.log T) * vkW T

/-- The logarithmic derivative of `ζ`. -/
noncomputable def zLD (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma vkW_denom_pos {T : ℝ} (hT : 3 ≤ T) :
    0 < Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3) := by
  have h1 : 1 < Real.log T :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hT)
  have h2 : 0 < Real.log (Real.log T) := Real.log_pos h1
  positivity

lemma vkW_pos {T : ℝ} (hT : 3 ≤ T) : 0 < vkW T := by
  unfold vkW; exact one_div_pos.mpr (vkW_denom_pos hT)

lemma vkW_anti {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) : vkW b ≤ vkW a := by
  unfold vkW
  apply one_div_le_one_div_of_le (vkW_denom_pos ha)
  have h1 : 1 < Real.log a := one_lt_log_three.trans_le (Real.log_le_log (by norm_num) ha)
  have hl : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hll : Real.log (Real.log a) ≤ Real.log (Real.log b) := Real.log_le_log (by linarith) hl
  have h2 : 0 < Real.log (Real.log a) := Real.log_pos h1
  apply mul_le_mul (Real.rpow_le_rpow (by linarith) hl (by norm_num))
    (Real.rpow_le_rpow h2.le hll (by norm_num)) (by positivity)
    (Real.rpow_nonneg (by linarith) _)

lemma inVKRegion_iff (c₀ T σ : ℝ) : InVKRegion c₀ T σ ↔ 1 - c₀ * vkW T ≤ σ := by
  unfold InVKRegion vkW; rw [mul_one_div]

lemma re_neg_le_norm (z : ℂ) : (-z).re ≤ ‖z‖ := by
  simpa [norm_neg] using Complex.re_le_norm (-z)

lemma zeta_zero_re_lt_one {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ

/-- **Elementary asymptotics** of `L, φ, w` (all as `T → ∞`). -/
lemma vk_asymp (C : ℝ) : ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
    1 ≤ Real.log (Real.log T) ∧ vkW T / 2 ≤ vkW (2 * T) ∧ 1 / vkW T ≤ Real.log T ∧
    Real.log (Real.log T) / vkW T ≤ Real.log T ∧ vkTheta T ≤ 1 / 8 ∧ C * vkW T ≤ 1 := by
  sorry

/-- **(D3) Dirichlet-series bound** for `σ > 1`. -/
lemma logDeriv_zeta_dirichlet_bound : ∃ C : ℝ, ∀ σ t : ℝ, 1 < σ →
    ‖zLD (σ + t * I)‖ ≤ 1 / (σ - 1) + C := by
  obtain ⟨U, hU, hB⟩ := riemannZetaLogDerivResidue
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  rw [bddAbove_def] at hB
  obtain ⟨B, hB⟩ := hB
  set σ₀ : ℝ := 1 + r / 2
  have hσ₀ : 1 < σ₀ := by simp only [σ₀]; linarith
  refine ⟨max B ‖zLD σ₀‖, fun σ t hσ => ?_⟩
  have hvert : ‖zLD (σ + t * I)‖ ≤ ‖zLD σ‖ := by
    have := dlog_riemannZeta_bdd_on_vertical_lines_generalized σ σ t hσ le_rfl
    rwa [neg_div, norm_neg] at this
  refine hvert.trans ?_
  have hpos : 0 < 1 / (σ - 1) := by have : 0 < σ - 1 := by linarith
                                    positivity
  by_cases hσσ₀ : σ < σ₀
  · have hmem : (σ : ℂ) ∈ U \ {1} := by
      refine ⟨hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> simp only [σ₀] at hσσ₀ <;> linarith
      · intro h
        have : (σ : ℂ) = ((1 : ℝ) : ℂ) := by simpa using h
        have := Complex.ofReal_injective this
        linarith
    have hb := hB _ ⟨σ, hmem, rfl⟩
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply] at hb
    have e : zLD σ = -(-(deriv riemannZeta σ / riemannZeta σ) - ((σ : ℂ) - 1)⁻¹) -
        ((σ : ℂ) - 1)⁻¹ := by unfold zLD; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    have h1 : ‖((σ : ℂ) - 1)⁻¹‖ = 1 / (σ - 1) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by have : 0 < σ - 1 := by linarith
                                         positivity), one_div]
    rw [h1]
    have := le_max_left B ‖zLD σ₀‖
    linarith
  · push Not at hσσ₀
    have := dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ 0 hσ₀ hσσ₀
    rw [neg_div, norm_neg] at this
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    have h2 : ‖zLD σ‖ ≤ ‖zLD σ₀‖ := this
    have := le_max_right B ‖zLD σ₀‖
    linarith

open ArithmeticFunction in
lemma ld_series (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ s) ∧
      -zLD s = ∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s := by
  refine ⟨?_, ?_⟩
  · have := LSeriesSummable_vonMangoldt hs
    refine this.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn]
  · unfold zLD; rw [← neg_div]; exact LogDerivativeDirichlet s hs

open ArithmeticFunction in
lemma ld_term_re (n : ℕ) (σ y : ℝ) :
    ((Λ n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + y * I)).re =
      Λ n * Real.exp (-(Real.log n) * σ) * Real.cos (Real.log n * y) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [div_eq_mul_inv, ← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hn', hlog,
    Complex.re_ofReal_mul, Complex.exp_re]
  have hre : ((Real.log n : ℂ) * -((σ : ℂ) + y * I)).re = -(Real.log n) * σ := by simp only [neg_add, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have him : ((Real.log n : ℂ) * -((σ : ℂ) + y * I)).im = -(Real.log n * y) := by simp only [neg_add, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [hre, him, Real.cos_neg]; ring

open ArithmeticFunction in
/-- **(D2) The 3-4-1 inequality.** -/
lemma three_four_one (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-zLD σ).re + 4 * (-zLD (σ + t * I)).re + (-zLD (σ + (2 * t : ℝ) * I)).re := by
  have e0 : zLD (σ : ℂ) = zLD (σ + ((0 : ℝ) : ℂ) * I) := by simp
  have hre : ∀ y : ℝ, 1 < ((σ : ℂ) + y * I).re := fun y => by simp [hσ]
  obtain ⟨S0, E0⟩ := ld_series _ (hre 0)
  obtain ⟨S1, E1⟩ := ld_series _ (hre t)
  obtain ⟨S2, E2⟩ := ld_series _ (hre (2 * t))
  rw [e0, E0, E1, E2, Complex.re_tsum S0, Complex.re_tsum S1, Complex.re_tsum S2]
  have R0 := S0.mapL Complex.reCLM
  have R1 := S1.mapL Complex.reCLM
  have R2 := S2.mapL Complex.reCLM
  simp only [Complex.reCLM_apply] at R0 R1 R2
  rw [← R0.tsum_mul_left, ← R1.tsum_mul_left, ← (R0.mul_left 3).tsum_add (R1.mul_left 4),
    ← ((R0.mul_left 3).add (R1.mul_left 4)).tsum_add R2]
  refine tsum_nonneg fun n => ?_
  simp only [ld_term_re]
  set E := Λ n * Real.exp (-(Real.log n) * σ)
  have hE : 0 ≤ E := mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
  set c := Real.cos (Real.log n * t)
  have h2 : Real.cos (Real.log n * (2 * t)) = 2 * c ^ 2 - 1 := by
    rw [show Real.log n * (2 * t) = 2 * (Real.log n * t) by ring, Real.cos_two_mul]
  rw [h2, mul_zero, Real.cos_zero]
  have : 0 ≤ E * (2 * (1 + c) ^ 2) := mul_nonneg hE (by positivity)
  nlinarith

end LeanFormalizations.Erdos385

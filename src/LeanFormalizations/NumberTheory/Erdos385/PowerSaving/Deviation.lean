/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.LargeValueSum

/-!
# Erdős #385 power saving: large `P` forces a large VK deviation (phase E9b)

`dev_lower`: if `|P(1+it)| ≥ u ≥ Z^{−1/8}` and `u t² ≥ 4K` (`K` from second-order Mellin decay of
`g₀ = cutoffDiv g`), then the smoothed prime sum `Σ Λ(n) n^{−it} g₀(n/√Z)` deviates from its main
term `mellin g₀ (1 − it) (√Z)^{1−it}` by `≥ √Z u / 2`.  Inputs: `primeP_decomp` (prime powers
`≤ 2(ψ − θ)(√Z) ≤ 2 Z^{1/4} log Z`) and `mellin_decay_two` (main term `≤ √Z u/4`).
-/

namespace LeanFormalizations.Erdos385

open Real Filter Complex LeanFormalizations.Literature
open scoped Chebyshev

/-- The VK deviation of the smoothed prime sum at height `t`, scale `P`. -/
noncomputable def vkDev (f : ℝ → ℂ) (P t : ℝ) : ℂ :=
  (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) * f (n / P)) -
    mellin f (1 - t * I) * (P : ℂ) ^ (1 - t * I)

theorem dev_lower {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∃ Km : ℝ, 0 < Km ∧ ∀ᶠ Z : ℝ in atTop, ∀ u : ℝ, Z ^ (-(1 / 8 : ℝ)) ≤ u → ∀ t : ℝ,
      4 * Km ≤ u * t ^ 2 → u ≤ ‖primeP g Z (1 + t * I)‖ →
        √Z * u / 2 ≤ ‖vkDev (cutoffDiv g) (√Z) t‖ := by
  obtain ⟨hs, -, -, hsupp, -⟩ := cutoffDiv_facts hδ hδ' hg
  obtain ⟨K₀, hK₀⟩ := mellin_decay_two (hs 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hsupp
  refine ⟨|K₀| + 1, by positivity, ?_⟩
  filter_upwards [ev_log_rpow_le (C := 1) zero_le_one (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_ge_atTop (16 : ℝ)] with Z hlog hZ16 u hu t ht hP
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  set w := √Z with hw
  have hw1 : 1 ≤ w := Real.one_le_sqrt.2 hZ1
  have hw0 : 0 < w := by linarith
  set M := mellin (cutoffDiv g) (1 - t * I) with hM
  set S := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) *
    cutoffDiv g (n / w) with hS
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  -- main term `≤ w u / 4`
  have ht0 : 0 < t ^ 2 := by
    have : 0 < u * t ^ 2 := lt_of_lt_of_le (by positivity) ht
    exact pos_of_mul_pos_right this hu0.le
  have hMb : ‖M‖ ≤ u / 4 := by
    have h1 := hK₀ t
    rw [← hM] at h1
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have : ‖M‖ * t ^ 2 * 4 ≤ u * t ^ 2 := by
      have := le_abs_self K₀; nlinarith
    nlinarith
  have hmain : ‖M * (w : ℂ) ^ (1 - t * I)‖ = ‖M‖ * w := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw0]; simp
  -- prime powers `≤ w u / 4`
  have hdec := primeP_decomp hδ hδ' hg hZ1 t
  have hpsi : ψ w - θ w ≤ 2 * √w * Real.log w := Chebyshev.psi_sub_theta_le hw1
  have hlw : Real.log w = Real.log Z / 2 := by
    rw [hw, Real.log_sqrt hZ0.le]
  have hsw : √w = Z ^ (1 / 4 : ℝ) := by
    rw [hw, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hZ0.le]; norm_num
  have hwZ : w = Z ^ (1 / 2 : ℝ) := by rw [hw, Real.sqrt_eq_rpow]
  have hE : 2 * (ψ w - θ w) ≤ w * u / 4 := by
    have h1 : 2 * (ψ w - θ w) ≤ 2 * Z ^ (1 / 4 : ℝ) * Real.log Z := by
      rw [hsw, hlw] at hpsi; linarith
    have h2 : w * Z ^ (-(1 / 8 : ℝ)) = Z ^ (1 / 4 : ℝ) * Z ^ (1 / 8 : ℝ) := by
      rw [hwZ, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; norm_num
    have h3 : w * Z ^ (-(1 / 8 : ℝ)) ≤ w * u := mul_le_mul_of_nonneg_left hu hw0.le
    have hl : Real.log Z ^ (1 : ℝ) = Real.log Z := Real.rpow_one _
    rw [hl] at hlog
    have h4 : 0 ≤ Z ^ (1 / 4 : ℝ) := by positivity
    have h5 : 2 * Z ^ (1 / 4 : ℝ) * Real.log Z * 4 ≤ Z ^ (1 / 4 : ℝ) * Z ^ (1 / 8 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlog h4; nlinarith
    linarith
  -- assemble
  have hwP : w * u ≤ ‖(w : ℂ) * primeP g Z (1 + t * I)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0.le]
    exact mul_le_mul_of_nonneg_left hP hw0.le
  have htri : ‖(w : ℂ) * primeP g Z (1 + t * I)‖ ≤
      ‖(w : ℂ) * primeP g Z (1 + t * I) - S‖ + ‖vkDev (cutoffDiv g) w t‖ +
        ‖M * (w : ℂ) ^ (1 - t * I)‖ := by
    have e : (w : ℂ) * primeP g Z (1 + t * I) = ((w : ℂ) * primeP g Z (1 + t * I) - S) +
        vkDev (cutoffDiv g) w t + M * (w : ℂ) ^ (1 - t * I) := by
      simp only [vkDev, hS, hM]; ring
    calc _ = ‖((w : ℂ) * primeP g Z (1 + t * I) - S) + vkDev (cutoffDiv g) w t +
          M * (w : ℂ) ^ (1 - t * I)‖ := by rw [← e]
      _ ≤ _ := norm_add₃_le
  rw [hmain] at htri
  have : ‖M‖ * w ≤ w * u / 4 := by nlinarith
  linarith

end LeanFormalizations.Erdos385

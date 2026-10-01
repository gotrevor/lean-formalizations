/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385AlmostAll
import LeanFormalizations.Literature.Erdos385VK

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
    Real.log (Real.log T) / vkW T ≤ Real.log T ∧ vkTheta T ≤ 1 / 2 ∧ C * vkW T ≤ 1 := by
  sorry

/-- **(D3) Dirichlet-series bound** for `σ > 1`. -/
lemma logDeriv_zeta_dirichlet_bound : ∃ C : ℝ, ∀ σ t : ℝ, 1 < σ →
    ‖zLD (σ + t * I)‖ ≤ 1 / (σ - 1) + C := by
  sorry

/-- **(D2) The 3-4-1 inequality.** -/
lemma three_four_one (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-zLD σ).re + 4 * (-zLD (σ + t * I)).re + (-zLD (σ + (2 * t : ℝ) * I)).re := by
  sorry

end LeanFormalizations.Erdos385

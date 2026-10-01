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

/-- **(Z1) Landau's local formula, one-sided.**  `FinalBound` (PNT+, sorry-free) for
`f(z) = ζ(s₀ + 2θz)/ζ(s₀)`, `s₀ = 1 + θ + it`, with `log B ≪ φ` from Richert (upper) and
`ZetaLowerBound3` (lower, at `s₀`); every zero term has `Re(1/(s−ρ)) ≥ 0` because `Re ρ < 1 < σ`,
so all but those in `S` may be dropped. -/
lemma landau_neg_re_upper (h : RichertZetaGrowth) : ∃ K t₁ : ℝ, ∀ t σ : ℝ, t₁ ≤ |t| → 1 < σ →
    σ ≤ 1 + vkTheta |t| → ∀ S : Finset ℂ, (∀ ρ ∈ S, riemannZeta ρ = 0 ∧
      ‖ρ - (1 + vkTheta |t| + t * I)‖ ≤ 15 / 8 * vkTheta |t|) →
    (-zLD (σ + t * I)).re ≤ K / vkW |t| - ∑ ρ ∈ S, (1 / ((σ : ℂ) + t * I - ρ)).re := by
  sorry

/-- **(Z2) Landau's local formula, two-sided** (zeros at distance `≥ η`; `ZerosBound` counts
`≪ φ` of them). -/
lemma landau_logderiv_bound (h : RichertZetaGrowth) : ∃ K t₁ : ℝ, ∀ t σ η : ℝ, t₁ ≤ |t| →
    1 - vkTheta |t| / 4 ≤ σ → σ ≤ 1 + vkTheta |t| → 0 < η →
    (∀ ρ : ℂ, riemannZeta ρ = 0 → ‖ρ - (1 + vkTheta |t| + t * I)‖ ≤ 15 / 8 * vkTheta |t| →
      η ≤ ‖(σ : ℂ) + t * I - ρ‖) →
    riemannZeta (σ + t * I) ≠ 0 →
    ‖zLD (σ + t * I)‖ ≤ K / vkW |t| + K * Real.log (Real.log |t|) / η := by
  sorry

end LeanFormalizations.Erdos385

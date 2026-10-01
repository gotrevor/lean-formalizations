/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Landau.Basic

/-!
# Landau's method, layer 2: zero-free region and log-derivative bound (phase E2e)

From the layer-1 interfaces:
* `vk_zero_free` — the 3-4-1 argument: zeros at height `γ` have `β < 1 − c vkW |γ|`.
  At `σ = 1 + ε w` (`w = vkW |γ|`, `ε = 1/(4A)`, `A = 1 + 6K`):
  `0 ≤ 3(1/(εw) + C) + 4(K/w − 1/(σ−β)) + 2K/w` gives `σ − β ≥ 4w/(13A)`, so
  `β ≤ 1 − 3w/(52A)`.
* `vk_large_height_of` — zeros in the Landau disc at height `t` lie left of `1 − (c/2) w`, so
  points with `σ ≥ 1 − (c/4) w` are at distance `≥ (c/4) w` from them, and Z2 gives
  `|ζ'/ζ| ≪ 1/w + φ/w ≪ log t`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature Complex

lemma re_neg_le_norm (z : ℂ) : (-z).re ≤ ‖z‖ := by
  simpa [norm_neg] using Complex.re_le_norm (-z)

lemma zeta_zero_re_lt_one {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ

/-- **The VK zero-free region** (3-4-1 with Landau's local formula). -/
theorem vk_zero_free (h : RichertZetaGrowth) : ∃ c t₀ : ℝ, 0 < c ∧ 3 ≤ t₀ ∧
    ∀ ρ : ℂ, riemannZeta ρ = 0 → t₀ ≤ |ρ.im| → ρ.re < 1 - c * vkW |ρ.im| := by
  obtain ⟨K, t₁, hZ1⟩ := landau_neg_re_upper h
  obtain ⟨C₃, hD3⟩ := logDeriv_zeta_dirichlet_bound
  obtain ⟨T₀, hT₀3, hT₀⟩ := vk_asymp (3 * max C₃ 0)
  set Kp := max K 0 with hKp
  set A := 1 + 6 * Kp with hA
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  refine ⟨3 / (104 * A), max T₀ t₁, by positivity, le_max_of_le_left hT₀3, ?_⟩
  intro ρ hρ hγ
  set γ := ρ.im with hγdef
  set β := ρ.re with hβdef
  set T := |γ| with hT
  have hTT₀ : T₀ ≤ T := le_of_max_le_left hγ
  have hTt₁ : t₁ ≤ T := le_of_max_le_right hγ
  have hT3 : 3 ≤ T := hT₀3.trans hTT₀
  obtain ⟨hφ1, hw2, -, -, -, hCw⟩ := hT₀ T hTT₀
  obtain ⟨hφ21, -, -, -, -, -⟩ := hT₀ (2 * T) (by linarith)
  set w := vkW T with hwdef
  have hw : 0 < w := vkW_pos hT3
  have hθ : vkTheta T = Real.log (Real.log T) * w := rfl
  have hwθ : w ≤ vkTheta T := by rw [hθ]; nlinarith
  have hβ1 : β < 1 := zeta_zero_re_lt_one hρ
  have hcw : 3 / (104 * A) * w ≤ w / 4 := by
    have : 3 / (104 * A) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  by_cases hb : β < 1 - vkTheta T / 4
  · linarith
  push Not at hb
  set ε := 1 / (4 * A) with hε
  have hε0 : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set σ := 1 + ε * w with hσ
  have hσ1 : 1 < σ := by have := mul_pos hε0 hw; linarith
  have hσθ : σ ≤ 1 + vkTheta T := by nlinarith
  have hρeq : ρ = (β : ℂ) + γ * I := (Complex.re_add_im ρ).symm
  -- Z1 at height γ with S = {ρ}
  have hball : ‖ρ - (1 + vkTheta T + γ * I)‖ ≤ 5 / 4 * vkTheta T := by
    have : ρ - (1 + vkTheta T + γ * I) = ((β - 1 - vkTheta T : ℝ) : ℂ) := by
      rw [hρeq]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
    linarith
  have h1 := hZ1 γ σ hTt₁ hσ1 hσθ {ρ} (by simpa using ⟨hρ, hball⟩)
  rw [Finset.sum_singleton] at h1
  have hu : 0 < σ - β := by linarith
  have hsub : (σ : ℂ) + γ * I - ρ = ((σ - β : ℝ) : ℂ) := by rw [hρeq]; push_cast; ring
  rw [hsub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re] at h1
  -- Z1 at height 2γ with S = ∅
  have h2T : |2 * γ| = 2 * T := by rw [abs_mul, abs_two]
  have hw2T : 0 < vkW (2 * T) := vkW_pos (by linarith)
  have hσθ2 : σ ≤ 1 + vkTheta |2 * γ| := by
    rw [h2T, vkTheta]
    have : ε * w ≤ vkW (2 * T) := by nlinarith
    nlinarith
  have h2 := hZ1 (2 * γ) σ (by rw [h2T]; linarith) hσ1 hσθ2 ∅ (by simp)
  rw [Finset.sum_empty, sub_zero, h2T] at h2
  have h2' : K / vkW (2 * T) ≤ 2 * Kp * (1 / w) := by
    calc K / vkW (2 * T) ≤ Kp / vkW (2 * T) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hw2T.le
      _ ≤ Kp / (w / 2) := div_le_div_of_nonneg_left hKp0 (by positivity) hw2
      _ = 2 * Kp * (1 / w) := by field_simp
  -- D3 at real σ
  have h3 := hD3 σ 0 hσ1
  have h3' : (-zLD σ).re ≤ 1 / (σ - 1) + C₃ := by
    have := re_neg_le_norm (zLD σ)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h3
    linarith
  have h4 := three_four_one σ γ hσ1
  -- combine
  set x := 1 / w with hx
  have hx0 : 0 < x := by positivity
  have hσ1' : 1 / (σ - 1) = 4 * A * x := by
    rw [show σ - 1 = ε * w by rw [hσ]; ring, hε, hx]; field_simp
  have hKx : K / w ≤ Kp * x := by
    rw [hx, ← div_eq_mul_one_div]; exact div_le_div_of_nonneg_right (le_max_left _ _) hw.le
  have hC : 3 * C₃ ≤ x := by
    have : 3 * max C₃ 0 ≤ x := by
      rw [hx, le_div_iff₀ hw]; linarith
    have := le_max_left C₃ 0; linarith
  have key : 4 * (1 / (σ - β)) ≤ 13 * A * x := by
    have : (-zLD (σ + γ * I)).re ≤ K / w - 1 / (σ - β) := h1
    have hAx : A * x = x + 6 * (Kp * x) := by rw [hA]; ring
    have h2'' := h2.trans h2'
    linarith
  have hu' : 4 * w / (13 * A) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_div_iff₀ hu hw).mp (by
      calc (4 : ℝ) / (σ - β) = 4 * (1 / (σ - β)) := by ring
        _ ≤ 13 * A * x := key
        _ = 13 * A / w := by rw [hx]; ring)
    linarith
  have hfin : ε * w - 4 * w / (13 * A) < -(3 / (104 * A) * w) := by
    have e1 : ε * w = (w / A) / 4 := by rw [hε]; field_simp
    have e2 : 4 * w / (13 * A) = 4 * (w / A) / 13 := by field_simp
    have e3 : 3 / (104 * A) * w = 3 * (w / A) / 104 := by field_simp
    have : 0 < w / A := by positivity
    rw [e1, e2, e3]; linarith
  linarith

/-- **Large height**, from the layer-1 interfaces and `vk_zero_free`. -/
theorem vk_large_height_of (h : RichertZetaGrowth) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C₁ t₁ : ℝ, 3 ≤ t₁ ∧ ∀ σ y : ℝ, t₁ ≤ |y| → InVKRegion c₁ |y| σ →
      riemannZeta (σ + y * I) ≠ 0 ∧ ‖zLD (σ + y * I)‖ ≤ C₁ * Real.log |y| := by
  obtain ⟨c, t₃, hc, ht₃, hZF⟩ := vk_zero_free h
  obtain ⟨K, t₂, hZ2⟩ := landau_logderiv_bound h
  obtain ⟨C₃, hD3⟩ := logDeriv_zeta_dirichlet_bound
  obtain ⟨T₀, hT₀3, hT₀⟩ := vk_asymp 0
  set Kp := max K 0
  set C₃p := max C₃ 0
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have hC₃p0 : 0 ≤ C₃p := le_max_right _ _
  set c₁ := min (c / 4) 1 with hc₁
  have hc₁0 : 0 < c₁ := lt_min (by positivity) one_pos
  have hc₁4 : c₁ ≤ c / 4 := min_le_left _ _
  have hc₁1 : c₁ ≤ 1 := min_le_right _ _
  refine ⟨c₁, hc₁0, C₃p + 1 + Kp + 4 * Kp / c, max (max T₀ t₂) (t₃ + 1),
    le_max_of_le_left (le_max_of_le_left hT₀3), ?_⟩
  intro σ y hy hreg
  rw [inVKRegion_iff] at hreg
  set T := |y| with hT
  have hTT₀ : T₀ ≤ T := le_of_max_le_left (le_of_max_le_left hy)
  have hTt₂ : t₂ ≤ T := le_of_max_le_right (le_of_max_le_left hy)
  have hTt₃ : t₃ + 1 ≤ T := le_of_max_le_right hy
  have hT3 : 3 ≤ T := hT₀3.trans hTT₀
  obtain ⟨hφ1, hw2, hwL, hφwL, hθ45, -⟩ := hT₀ T hTT₀
  set w := vkW T with hwdef
  have hw : 0 < w := vkW_pos hT3
  have hθ : vkTheta T = Real.log (Real.log T) * w := rfl
  have hwθ : w ≤ vkTheta T := by rw [hθ]; nlinarith
  have hL1 : 1 ≤ Real.log T :=
    (one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hT3)).le
  have hfinal : ∀ B : ℝ, B ≤ (C₃p + 1 + Kp + 4 * Kp / c) * Real.log T →
      B ≤ (C₃p + 1 + Kp + 4 * Kp / c) * Real.log T := fun _ hB => hB
  by_cases hσ : 1 + vkTheta T < σ
  · refine ⟨riemannZeta_ne_zero_of_one_le_re (by simp; linarith), ?_⟩
    have hb := hD3 σ y (by linarith)
    have h1 : 1 / (σ - 1) ≤ 1 / w :=
      one_div_le_one_div_of_le hw (by linarith)
    have : C₃ ≤ C₃p := le_max_left _ _
    have h4 : 0 ≤ 4 * Kp / c := by positivity
    nlinarith
  push Not at hσ
  have hσlo : 1 - vkTheta T ≤ σ := by nlinarith
  refine ⟨?_, ?_⟩
  · intro hz
    have := hZF _ hz (by simp; linarith)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
      add_zero, add_im, ofReal_im, mul_im, zero_add] at this
    have : c₁ * w < c * w := by nlinarith
    linarith
  · have hη : 0 < c / 4 * w := by positivity
    have hdist : ∀ ρ : ℂ, riemannZeta ρ = 0 → ‖ρ - (1 + vkTheta T + y * I)‖ ≤ 5 / 4 * vkTheta T →
        c / 4 * w ≤ ‖(σ : ℂ) + y * I - ρ‖ := by
      intro ρ hρ hb
      have him : |ρ.im - y| ≤ 1 := by
        have := Complex.abs_im_le_norm (ρ - (1 + vkTheta T + y * I))
        simp at this
        linarith
      have hγlo : t₃ ≤ |ρ.im| := by
        have := abs_sub_abs_le_abs_sub y ρ.im
        rw [abs_sub_comm] at this
        linarith
      have hγhi : |ρ.im| ≤ 2 * T := by
        have := abs_sub_abs_le_abs_sub ρ.im y
        linarith
      have hz := hZF ρ hρ hγlo
      have hwγ : vkW (2 * T) ≤ vkW |ρ.im| := vkW_anti (ht₃.trans hγlo) hγhi
      have : c * (w / 2) ≤ c * vkW |ρ.im| := mul_le_mul_of_nonneg_left (hw2.trans hwγ) hc.le
      have hre := Complex.re_le_norm ((σ : ℂ) + y * I - ρ)
      simp at hre
      have : c₁ * w ≤ c / 4 * w := mul_le_mul_of_nonneg_right hc₁4 hw.le
      linarith
    have hne : riemannZeta (σ + y * I) ≠ 0 := by
      intro hz
      have := hZF _ hz (by simp; linarith)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
        add_zero, add_im, ofReal_im, mul_im, zero_add] at this
      have : c₁ * w < c * w := by nlinarith
      linarith
    have hb := hZ2 y σ (c / 4 * w) hTt₂ hσlo hσ hη hdist hne
    have e1 : K / w ≤ Kp * Real.log T := by
      calc K / w ≤ Kp / w := div_le_div_of_nonneg_right (le_max_left _ _) hw.le
        _ = Kp * (1 / w) := by ring
        _ ≤ Kp * Real.log T := mul_le_mul_of_nonneg_left hwL hKp0
    have e2 : K * Real.log (Real.log T) / (c / 4 * w) ≤ 4 * Kp / c * Real.log T := by
      have hφ0 : 0 ≤ Real.log (Real.log T) := by linarith
      calc K * Real.log (Real.log T) / (c / 4 * w)
          ≤ Kp * Real.log (Real.log T) / (c / 4 * w) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hφ0) hη.le
        _ = 4 * Kp / c * (Real.log (Real.log T) / w) := by field_simp
        _ ≤ 4 * Kp / c * Real.log T := mul_le_mul_of_nonneg_left hφwL (by positivity)
    nlinarith

end LeanFormalizations.Erdos385

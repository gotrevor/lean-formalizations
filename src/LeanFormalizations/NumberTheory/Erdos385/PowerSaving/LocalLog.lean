/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Landau.Zeta

/-!
# Erdős #385 power saving: Landau's local lemma at a free scale (phase E9b, crux step (a))

`local_logDeriv_bound`: if `ζ` has no zero within `5η₂/2` of `c₀ = 1 + η₂ + iy₀`, then on the
segment `σ ∈ [1 − η₂, 1 + 3η₂]` at height `y₀`,
`|ζ'/ζ(σ + iy₀)| ≤ K (log|y₀| + (log log|y₀| + log(1/η₂) + 1)/η₂)`.

`Landau.local_landau` on `closedBall c₀ (4η₂)`: growth `M = 4AC e^{k₁ η₂^{3/2} log|y₀|} log|y₀|`
from Richert (`σ ≤ 1`) and PNT+ `ZetaUpperBnd` (`σ ≥ 1`); centre `|ζ(c₀)| ≥ c η₂^{3/4}/(log|y₀|)^{1/4}`
(PNT+ `ZetaLowerBound3`); the zero sum is empty by hypothesis.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature Complex Metric

set_option maxHeartbeats 1000000 in
/-- **Landau's local lemma at scale `η₂`, zero-free form.** -/
theorem local_logDeriv_bound (h : RichertZetaGrowth) : ∃ K y₁ : ℝ, 0 ≤ K ∧ ∀ η₂ y₀ : ℝ,
    0 < η₂ → η₂ ≤ 1 / 8 → y₁ ≤ |y₀| →
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 5 / 2 * η₂ < ‖ρ - (1 + η₂ + y₀ * I)‖) →
    ∀ σ : ℝ, 1 - η₂ ≤ σ → σ ≤ 1 + 3 * η₂ →
      ‖zLD (σ + y₀ * I)‖ ≤ K * (Real.log |y₀| +
        (Real.log (Real.log |y₀|) + Real.log (1 / η₂) + 1) / η₂) := by
  obtain ⟨K₀, hK₀⟩ := Landau.local_landau
  obtain ⟨A, B, hR⟩ := h
  obtain ⟨A', hA', C, hC, hU⟩ := ZetaUpperBnd
  obtain ⟨c, hc, hLB⟩ := ZetaLowerBound3
  set K₀p := max K₀ 0 with hK₀p
  set Bp := max B 0 with hBp
  set Ap := max A 1 with hAp
  set Cp := max C 1 with hCp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  have hAp1 : 1 ≤ Ap := le_max_right _ _
  have hCp1 : 1 ≤ Cp := le_max_right _ _
  have hK₀p0 : 0 ≤ K₀p := le_max_right _ _
  set k₁ := 2 * Bp * (3 : ℝ) ^ ((3 : ℝ) / 2) with hk₁
  have hk₁0 : 0 ≤ k₁ := by positivity
  set K₁ := k₁ + 2 + |Real.log (8 * Ap * Cp / c)| with hK₁
  refine ⟨K₀p * K₁, 16, by positivity, ?_⟩
  intro η₂ y₀ hη hη8 hy hfree σ hσl hσu
  set ℓ := Real.log |y₀| with hℓ
  have hy0 : 0 < |y₀| := by linarith
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9; linarith
  have hℓ0 : 0 < ℓ := by linarith
  set c₀ : ℂ := 1 + η₂ + y₀ * I with hc₀
  set δ := 4 * η₂ with hδ
  have hδ0 : 0 < δ := by positivity
  have h1 : (1 : ℂ) ∉ closedBall c₀ δ := by
    intro hm
    rw [mem_closedBall, dist_comm, dist_eq_norm] at hm
    have him : (c₀ - 1).im = y₀ := by simp [hc₀]
    have := Complex.abs_im_le_norm (c₀ - 1)
    rw [him] at this
    linarith
  set E := Real.exp (k₁ * η₂ ^ ((3 : ℝ) / 2) * ℓ) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set M := 4 * Ap * Cp * E * ℓ with hM
  have hMb : ∀ s ∈ closedBall c₀ δ, ‖riemannZeta s‖ ≤ M := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm] at hs
    set σ' := s.re
    set τ := s.im
    have hseq : s = (σ' : ℂ) + τ * I := (Complex.re_add_im s).symm
    have hre : |σ' - (1 + η₂)| ≤ 4 * η₂ := by
      have := Complex.abs_re_le_norm (s - c₀)
      have e : (s - c₀).re = σ' - (1 + η₂) := by simp [hc₀, σ']
      rw [e] at this; linarith
    have him : |τ - y₀| ≤ 4 * η₂ := by
      have := Complex.abs_im_le_norm (s - c₀)
      have e : (s - c₀).im = τ - y₀ := by simp [hc₀, τ]
      rw [e] at this; linarith
    have hτlo : |y₀| - 1 / 2 ≤ |τ| := by
      have := abs_sub_abs_le_abs_sub y₀ τ; rw [abs_sub_comm] at him; linarith
    have hτhi : |τ| ≤ |y₀| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub τ y₀; linarith
    have hτ3 : 3 < |τ| := by linarith
    have hτ0 : 0 < |τ| := by linarith
    have hlτ : Real.log |τ| ≤ 2 * ℓ := by
      have hsq : |τ| ≤ |y₀| ^ 2 := by nlinarith
      calc Real.log |τ| ≤ Real.log (|y₀| ^ 2) := Real.log_le_log hτ0 hsq
        _ = 2 * ℓ := by rw [Real.log_pow]; push_cast; ring
    have hlτ1 : 1 ≤ Real.log |τ| := by
      rw [Real.le_log_iff_exp_le hτ0]
      have := Real.exp_one_lt_d9; linarith
    by_cases hσ1 : σ' ≤ 1
    · have hσh : 1 / 2 ≤ σ' := by have := (abs_le.mp hre).1; linarith
      have hb := hR σ' τ hσh hσ1 hτ3.le
      rw [← hseq] at hb
      have hx : (1 - σ') ^ ((3 : ℝ) / 2) ≤ (3 * η₂) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by linarith) (by have := (abs_le.mp hre).1; linarith) (by norm_num)
      have h3 : (3 * η₂) ^ ((3 : ℝ) / 2) = (3 : ℝ) ^ ((3 : ℝ) / 2) * η₂ ^ ((3 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) hη.le
      have hEx : B * (1 - σ') ^ ((3 : ℝ) / 2) ≤ Bp * ((3 : ℝ) ^ ((3 : ℝ) / 2) * η₂ ^ ((3 : ℝ) / 2)) := by
        rw [← h3]
        calc B * (1 - σ') ^ ((3 : ℝ) / 2) ≤ Bp * (1 - σ') ^ ((3 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
          _ ≤ Bp * (3 * η₂) ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hx hBp0
      have hX : |τ| ^ (B * (1 - σ') ^ ((3 : ℝ) / 2)) ≤ E := by
        rw [Real.rpow_def_of_pos hτ0, hE]
        apply Real.exp_le_exp.mpr
        calc Real.log |τ| * (B * (1 - σ') ^ ((3 : ℝ) / 2))
            ≤ Real.log |τ| * (Bp * ((3 : ℝ) ^ ((3 : ℝ) / 2) * η₂ ^ ((3 : ℝ) / 2))) :=
              mul_le_mul_of_nonneg_left hEx (by linarith)
          _ ≤ (2 * ℓ) * (Bp * ((3 : ℝ) ^ ((3 : ℝ) / 2) * η₂ ^ ((3 : ℝ) / 2))) :=
              mul_le_mul_of_nonneg_right hlτ (by positivity)
          _ = k₁ * η₂ ^ ((3 : ℝ) / 2) * ℓ := by rw [hk₁]; ring
      have hY : Real.log |τ| ^ ((2 : ℝ) / 3) ≤ 2 * ℓ := by
        have := Real.rpow_le_rpow_of_exponent_le hlτ1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)
        rw [Real.rpow_one] at this
        linarith
      have hX0 : 0 ≤ |τ| ^ (B * (1 - σ') ^ ((3 : ℝ) / 2)) := Real.rpow_nonneg hτ0.le _
      have hY0 : 0 ≤ Real.log |τ| ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
      calc ‖riemannZeta s‖ ≤ A * |τ| ^ (B * (1 - σ') ^ ((3 : ℝ) / 2)) *
            Real.log |τ| ^ ((2 : ℝ) / 3) := hb
        _ ≤ Ap * (|τ| ^ (B * (1 - σ') ^ ((3 : ℝ) / 2)) * Real.log |τ| ^ ((2 : ℝ) / 3)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hX0 hY0)
        _ ≤ Ap * (E * (2 * ℓ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hX hY hY0 (by linarith)) (by linarith)
        _ = 2 * (Ap * E * ℓ) := by ring
        _ ≤ 4 * Cp * (Ap * E * ℓ) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = M := by rw [hM]; ring
    · push Not at hσ1
      have hσ2 : σ' ≤ 2 := by have := (abs_le.mp hre).2; linarith
      have hb := hU σ' τ hτ3 ⟨by
        have : 0 ≤ A' / Real.log |τ| := div_nonneg hA'.1.le (by linarith)
        linarith, hσ2⟩
      rw [← hseq] at hb
      calc ‖riemannZeta s‖ ≤ C * Real.log |τ| := hb
        _ ≤ Cp * (2 * ℓ) := mul_le_mul (le_max_left _ _) hlτ (by linarith) (by linarith)
        _ = 2 * (1 * (Cp * ℓ)) := by ring
        _ ≤ 4 * ((Ap * E) * (Cp * ℓ)) := by
            have h1 : 1 ≤ Ap * E := one_le_mul_of_one_le_of_one_le hAp1 hE1
            have h2 : 1 * (Cp * ℓ) ≤ (Ap * E) * (Cp * ℓ) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
            have h3 : 0 ≤ 1 * (Cp * ℓ) := by positivity
            linarith
        _ = M := by rw [hM]; ring
  -- the centre
  have hc0eq : c₀ = ((1 + η₂ : ℝ) : ℂ) + y₀ * I := by rw [hc₀]; push_cast; ring
  have hLBc := hLB (σ := 1 + η₂) ⟨by linarith, by linarith⟩ y₀ (by linarith)
  rw [← hc0eq, add_sub_cancel_left] at hLBc
  set a := ‖riemannZeta c₀‖ with ha
  set a₀ := c * η₂ ^ ((3 : ℝ) / 4) / ℓ ^ ((1 : ℝ) / 4) with ha₀
  have ha₀0 : 0 < a₀ := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le ha₀0 hLBc
  have hne : riemannZeta c₀ ≠ 0 := fun h0 => by rw [ha, h0, norm_zero] at ha0; exact lt_irrefl _ ha0
  obtain ⟨Z, m, hZ, -, -, hloc⟩ := hK₀ riemannZeta c₀ δ M hδ0 (zeta_analyticOnNhd h1)
    (zeta_zeros_finite h1) hne hMb
  have hZe : Z = ∅ := by
    ext ρ
    simp only [Finset.notMem_empty, iff_false]
    intro hρ
    obtain ⟨h0, hd⟩ := (hZ ρ).1 hρ
    have := hfree ρ h0
    rw [hδ] at hd
    linarith
  set s : ℂ := σ + y₀ * I with hs
  have hsc : ‖s - c₀‖ ≤ 2 * η₂ := by
    have e : s - c₀ = ((σ - 1 - η₂ : ℝ) : ℂ) := by rw [hs, hc₀]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hs0 : riemannZeta s ≠ 0 := by
    intro h0
    have := hfree s h0
    linarith
  have hmain := hloc s (by rw [hδ]; linarith) hs0
  rw [hZe, Finset.sum_empty, sub_zero] at hmain
  -- the log bound
  have haM : a ≤ M := hMb c₀ (mem_closedBall_self hδ0.le)
  set Λ := Real.log (2 * M / a) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  have hM0 : 0 < M := by positivity
  have hlogM : Real.log (2 * M) = Real.log (8 * Ap * Cp) + k₁ * η₂ ^ ((3 : ℝ) / 2) * ℓ +
      Real.log ℓ := by
    have e : 2 * M = (8 * Ap * Cp) * E * ℓ := by rw [hM]; ring
    rw [e, Real.log_mul (by positivity) hℓ0.ne', Real.log_mul (by positivity) (by positivity),
      hE, Real.log_exp]
  have hloga₀ : Real.log a₀ = Real.log c + 3 / 4 * Real.log η₂ - 1 / 4 * Real.log ℓ := by
    rw [ha₀, Real.log_div (by positivity) (by positivity), Real.log_mul hc.ne' (by positivity),
      Real.log_rpow hη, Real.log_rpow hℓ0]
  have hΛb : Λ ≤ Real.log (8 * Ap * Cp / c) + k₁ * η₂ ^ ((3 : ℝ) / 2) * ℓ +
      5 / 4 * Real.log ℓ + 3 / 4 * Real.log (1 / η₂) := by
    calc Λ ≤ Real.log (2 * M / a₀) :=
          Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by positivity) ha₀0 hLBc)
      _ = Real.log (2 * M) - Real.log a₀ := Real.log_div (by positivity) ha₀0.ne'
      _ = _ := by
          rw [hlogM, hloga₀, Real.log_div (by positivity) hc.ne', Real.log_div one_ne_zero hη.ne',
            Real.log_one]
          ring
  have hlη : 0 ≤ Real.log (1 / η₂) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have hlℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hη32 : η₂ ^ ((3 : ℝ) / 2) ≤ η₂ := by
    have := Real.rpow_le_rpow_of_exponent_ge hη (by linarith) (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rwa [Real.rpow_one] at this
  set R := Real.log ℓ + Real.log (1 / η₂) + 1 with hR'
  have hΛK : Λ ≤ K₁ * (η₂ * ℓ + R) := by
    have hab := le_abs_self (Real.log (8 * Ap * Cp / c))
    have e1 : k₁ * η₂ ^ ((3 : ℝ) / 2) * ℓ ≤ k₁ * (η₂ * ℓ) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hη32 hℓ0.le) hk₁0
    have hηℓ : 0 ≤ η₂ * ℓ := by positivity
    have habs : 0 ≤ |Real.log (8 * Ap * Cp / c)| := abs_nonneg _
    rw [hK₁, hR']
    nlinarith
  calc ‖zLD s‖ ≤ K₀ * Λ / δ := hmain
    _ ≤ K₀p * Λ / δ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ0) hδ0.le
    _ ≤ K₀p * (K₁ * (η₂ * ℓ + R)) / δ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΛK hK₀p0) hδ0.le
    _ = K₀p * K₁ * (ℓ / 4 + R / η₂ / 4) := by rw [hδ]; field_simp
    _ ≤ K₀p * K₁ * (ℓ + R / η₂) := by
        have hR0 : 0 ≤ R / η₂ := div_nonneg (by rw [hR']; linarith) hη.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end LeanFormalizations.Erdos385

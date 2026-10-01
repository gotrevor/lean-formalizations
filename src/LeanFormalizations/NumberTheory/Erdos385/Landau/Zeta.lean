/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Landau.Basic
import LeanFormalizations.NumberTheory.Erdos385.Landau.Local

/-!
# Landau's method, layer 1b: `local_landau` for `ζ` (phase E2e)

Disc `closedBall (1 + θ + it) (3θ)`, `θ = vkTheta |t|`.  Inputs:
* `zeta_disc_growth` — `|ζ| ≤ (log t)^K` on the disc (Richert for `σ ≤ 1`, PNT+ `ZetaUpperBnd`
  for `σ ≥ 1`);
* `zeta_center_lower` — `|ζ(1 + θ + it)| ≥ (log t)^{-K}` (PNT+ `ZetaLowerBound3`);
* `zeta_zeros_finite` — finitely many zeros in a disc avoiding `1`.
Then `log(2M/|ζ(c₀)|) ≪ φ`, and `local_landau` gives `zeta_local`, whence Z1 and Z2.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature Complex Metric

/-- Centre of the Landau disc at height `t`. -/
noncomputable def lc (t : ℝ) : ℂ := 1 + vkTheta |t| + t * I

lemma zeta_analyticOnNhd {c₀ : ℂ} {δ : ℝ} (h1 : (1 : ℂ) ∉ closedBall c₀ δ) :
    AnalyticOnNhd ℂ riemannZeta (closedBall c₀ δ) := by
  intro s hs
  have hs1 : s ≠ 1 := fun h => h1 (h ▸ hs)
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs1)

/-- Finitely many zeros of `ζ` in a closed disc avoiding the pole. -/
lemma zeta_zeros_finite {c₀ : ℂ} {δ : ℝ} (h1 : (1 : ℂ) ∉ closedBall c₀ δ) :
    {ρ | ρ ∈ closedBall c₀ δ ∧ riemannZeta ρ = 0}.Finite := by
  sorry

lemma vkTheta_rpow {T : ℝ} (hT : 3 ≤ T) :
    vkTheta T ^ ((3 : ℝ) / 2) = Real.log (Real.log T) / Real.log T := by
  have hL : 1 < Real.log T := one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hT)
  have hφ : 0 < Real.log (Real.log T) := Real.log_pos hL
  have hL0 : 0 < Real.log T := by linarith
  have e : vkTheta T = (Real.log (Real.log T) / Real.log T) ^ ((2 : ℝ) / 3) := by
    unfold vkTheta vkW
    rw [Real.div_rpow hφ.le hL0.le]
    have hsplit : Real.log (Real.log T) =
        Real.log (Real.log T) ^ ((1 : ℝ) / 3) * Real.log (Real.log T) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_add hφ]; norm_num
    have h1 : 0 < Real.log (Real.log T) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hφ _
    have h2 : 0 < Real.log T ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hL0 _
    nth_rewrite 1 [hsplit]
    field_simp
  rw [e, ← Real.rpow_mul (div_pos hφ hL0).le]; norm_num

/-- Growth of `ζ` on the Landau disc. -/
lemma zeta_disc_growth (h : RichertZetaGrowth) : ∃ K t₁ : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t₁ ≤ |t| →
    ∀ s ∈ closedBall (lc t) (3 * vkTheta |t|), ‖riemannZeta s‖ ≤ Real.log |t| ^ K := by
  obtain ⟨A, B, hR⟩ := h
  obtain ⟨A', hA', C, hC, hU⟩ := ZetaUpperBnd
  obtain ⟨T₀, hT₀3, hT₀⟩ := vk_asymp 0
  set Bp := max B 0
  have hBp : 0 ≤ Bp := le_max_right _ _
  set Ap := max A 1
  set Cp := max C 1
  set k := 2 * Bp * (2 : ℝ) ^ ((3 : ℝ) / 2)
  have hk : 0 ≤ k := by positivity
  refine ⟨k + 3, max T₀ (Real.exp (max Ap (2 * Cp) + 2)) + 5, by linarith, ?_⟩
  intro t ht s hs
  set T := |t| with hT
  have hT4 : 5 ≤ T := by
    have := le_max_left T₀ (Real.exp (max Ap (2 * Cp) + 2)); linarith
  have hTT₀ : T₀ ≤ T := by
    have := le_max_left T₀ (Real.exp (max Ap (2 * Cp) + 2)); linarith
  obtain ⟨hφ1, -, -, -, hθ8, -⟩ := hT₀ T hTT₀
  set L := Real.log T with hLdef
  have hLbig : max Ap (2 * Cp) + 2 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := le_max_right T₀ (Real.exp (max Ap (2 * Cp) + 2)); linarith
  have hAp : Ap ≤ L := by have := le_max_left Ap (2 * Cp); linarith
  have hCp : 2 * Cp ≤ L := by have := le_max_right Ap (2 * Cp); linarith
  have hL2 : 2 ≤ L := by have := le_max_left Ap (2 * Cp); have := le_max_right A 1; linarith
  have hL0 : 0 < L := by linarith
  set θ := vkTheta T with hθdef
  have hθ0 : 0 < θ := by
    rw [hθdef, vkTheta]
    exact mul_pos (by linarith) (vkW_pos (by linarith))
  -- coordinates of s
  rw [mem_closedBall, dist_eq_norm] at hs
  set σ := s.re
  set τ := s.im
  have hseq : s = (σ : ℂ) + τ * I := (Complex.re_add_im s).symm
  have hre : |σ - (1 + θ)| ≤ 3 * θ := by
    have := Complex.abs_re_le_norm (s - lc t)
    have e : (s - lc t).re = σ - (1 + θ) := by simp [lc, σ, θ, hT]
    rw [e] at this
    linarith
  have him : |τ - t| ≤ 3 * θ := by
    have := Complex.abs_im_le_norm (s - lc t)
    have e : (s - lc t).im = τ - t := by simp [lc, τ]
    rw [e] at this
    linarith
  have hτlo : T - 1 ≤ |τ| := by
    have := abs_sub_abs_le_abs_sub t τ; rw [abs_sub_comm] at this; linarith
  have hτhi : |τ| ≤ T + 1 := by
    have := abs_sub_abs_le_abs_sub τ t; linarith
  have hτ3 : 3 ≤ |τ| := by linarith
  have hlτ : Real.log |τ| ≤ 2 * L := by
    rw [hLdef, ← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
  have hlτ1 : 1 ≤ Real.log |τ| :=
    (one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hτ3)).le
  have hLK : L ^ (3 : ℝ) ≤ L ^ (k + 3) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hL3 : L ^ (3 : ℝ) = L * L * L := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  by_cases hσ1 : σ ≤ 1
  · have hσh : 1 / 2 ≤ σ := by have := (abs_le.mp hre).1; linarith
    have hb := hR σ τ hσh hσ1 hτ3
    rw [← hseq] at hb
    -- exponent
    have hx : (1 - σ) ^ ((3 : ℝ) / 2) ≤ (2 * θ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith) (by have := (abs_le.mp hre).1; linarith) (by norm_num)
    have h2θ : (2 * θ) ^ ((3 : ℝ) / 2) = (2 : ℝ) ^ ((3 : ℝ) / 2) * (Real.log L / L) := by
      rw [Real.mul_rpow (by norm_num) hθ0.le, hθdef, vkTheta_rpow (by linarith)]
    have hE : B * (1 - σ) ^ ((3 : ℝ) / 2) ≤ Bp * ((2 : ℝ) ^ ((3 : ℝ) / 2) * (Real.log L / L)) := by
      rw [← h2θ]
      calc B * (1 - σ) ^ ((3 : ℝ) / 2) ≤ Bp * (1 - σ) ^ ((3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ Bp * (2 * θ) ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hx hBp
    have hX : |τ| ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) ≤ L ^ k := by
      rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hL0]
      apply Real.exp_le_exp.mpr
      have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
      calc Real.log |τ| * (B * (1 - σ) ^ ((3 : ℝ) / 2))
          ≤ Real.log |τ| * (Bp * ((2 : ℝ) ^ ((3 : ℝ) / 2) * (Real.log L / L))) :=
            mul_le_mul_of_nonneg_left hE (by linarith)
        _ ≤ (2 * L) * (Bp * ((2 : ℝ) ^ ((3 : ℝ) / 2) * (Real.log L / L))) :=
            mul_le_mul_of_nonneg_right hlτ (by positivity)
        _ = Real.log L * k := by rw [show k = 2 * Bp * (2 : ℝ) ^ ((3 : ℝ) / 2) from rfl]; field_simp
    have hY : Real.log |τ| ^ ((2 : ℝ) / 3) ≤ L * L := by
      have := Real.rpow_le_rpow_of_exponent_le hlτ1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)
      rw [Real.rpow_one] at this
      nlinarith
    have hX0 : 0 ≤ |τ| ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) := Real.rpow_nonneg (by linarith) _
    have hY0 : 0 ≤ Real.log |τ| ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
    calc ‖riemannZeta s‖ ≤ A * |τ| ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) *
          Real.log |τ| ^ ((2 : ℝ) / 3) := hb
      _ ≤ L * L ^ k * (L * L) := by
          have hA : A ≤ L := (le_max_left A 1).trans hAp
          have hLk : 0 ≤ L ^ k := Real.rpow_nonneg hL0.le _
          have := mul_le_mul hX hY hY0 hLk
          have h2 : A * (|τ| ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log |τ| ^ ((2 : ℝ) / 3))
              ≤ L * (|τ| ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log |τ| ^ ((2 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_right hA (mul_nonneg hX0 hY0)
          nlinarith
      _ = L ^ (k + 3) := by
          rw [Real.rpow_add hL0, hL3]; ring
  · push Not at hσ1
    have hσ2 : σ ≤ 2 := by have := (abs_le.mp hre).2; linarith
    have hb := hU σ τ (by linarith) ⟨by
      have : 0 ≤ A' / Real.log |τ| := div_nonneg hA'.1.le (by linarith)
      linarith, hσ2⟩
    rw [← hseq] at hb
    have hCC : C ≤ Cp := le_max_left _ _
    calc ‖riemannZeta s‖ ≤ C * Real.log |τ| := hb
      _ ≤ Cp * (2 * L) := mul_le_mul hCC hlτ (by linarith) (by positivity)
      _ ≤ L * L * L := by nlinarith
      _ ≤ L ^ (k + 3) := by rw [← hL3]; exact hLK

/-- Lower bound for `ζ` at the centre of the Landau disc. -/
lemma zeta_center_lower : ∃ K t₁ : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t₁ ≤ |t| →
    Real.log |t| ^ (-K) ≤ ‖riemannZeta (lc t)‖ := by
  sorry

/-- **Landau's local formula for `ζ`.** -/
theorem zeta_local (h : RichertZetaGrowth) : ∃ K t₁ : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t₁ ≤ |t| →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ ‖ρ - lc t‖ ≤ 15 / 8 * vkTheta |t|) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, (m ρ : ℝ)) ≤ K * Real.log (Real.log |t|)) ∧
      ∀ s, ‖s - lc t‖ ≤ 3 / 2 * vkTheta |t| → riemannZeta s ≠ 0 →
        ‖zLD s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ K / vkW |t| := by
  obtain ⟨K₀, hK₀⟩ := Landau.local_landau
  obtain ⟨Kg, t₁, hKg, hG⟩ := zeta_disc_growth h
  obtain ⟨Kl, t₂, hKl, hLB⟩ := zeta_center_lower
  obtain ⟨T₀, hT₀3, hT₀⟩ := vk_asymp 0
  set K₀p := max K₀ 0
  have hK₀p : 0 ≤ K₀p := le_max_right _ _
  refine ⟨K₀p * (1 + Kg + Kl), max (max t₁ t₂) T₀, by positivity, ?_⟩
  intro t ht
  set T := |t| with hT
  have hTT₀ : T₀ ≤ T := le_of_max_le_right ht
  have hT3 : 3 ≤ T := hT₀3.trans hTT₀
  obtain ⟨hφ1, -, -, -, hθ, -⟩ := hT₀ T hTT₀
  set φ := Real.log (Real.log T) with hφ
  set w := vkW T with hw
  have hw0 : 0 < w := vkW_pos hT3
  have hθe : vkTheta T = φ * w := rfl
  set θ := vkTheta T with hθdef
  have hθ0 : 0 < θ := by rw [hθe]; positivity
  have hL1 : 1 ≤ Real.log T :=
    (one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hT3)).le
  have h1 : (1 : ℂ) ∉ closedBall (lc t) (3 * θ) := by
    intro hm
    rw [mem_closedBall, dist_comm, dist_eq_norm] at hm
    have him : (lc t - 1).im = t := by simp [lc]
    have := Complex.abs_im_le_norm (lc t - 1)
    rw [him, ← hT] at this
    linarith
  set M := Real.log T ^ Kg with hM
  have hGb := hG t (le_of_max_le_left (le_of_max_le_left ht))
  have hLb := hLB t (le_of_max_le_right (le_of_max_le_left ht))
  obtain ⟨Z, m, hZ, hm, hsum, hloc⟩ := hK₀ riemannZeta (lc t) (3 * θ) M (by positivity)
    (zeta_analyticOnNhd h1) (zeta_zeros_finite h1)
    (by intro h0; have := hLb; rw [h0, norm_zero] at this
        exact absurd this (not_le.mpr (Real.rpow_pos_of_pos (by linarith) _)))
    hGb
  -- the log bound
  set a := ‖riemannZeta (lc t)‖ with ha
  have hLpos : 0 < Real.log T := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (Real.rpow_pos_of_pos hLpos _) hLb
  have haM : a ≤ M := hGb _ (mem_closedBall_self (by positivity))
  set Λ := Real.log (2 * M / a) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  have hΛ : Λ ≤ (1 + Kg + Kl) * φ := by
    have hinv : 1 / a ≤ Real.log T ^ Kl := by
      rw [div_le_iff₀ ha0]
      have := mul_le_mul_of_nonneg_left hLb (Real.rpow_nonneg hLpos.le Kl)
      rwa [← Real.rpow_add hLpos, add_neg_cancel, Real.rpow_zero] at this
    have hstep : 2 * M / a ≤ 2 * Real.log T ^ (Kg + Kl) := by
      rw [Real.rpow_add hLpos, hM, div_eq_mul_one_div, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv (by positivity))
        (by norm_num)
    calc Λ ≤ Real.log (2 * Real.log T ^ (Kg + Kl)) :=
          Real.log_le_log (by positivity) hstep
      _ = Real.log 2 + (Kg + Kl) * φ := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hLpos]
      _ ≤ (1 + Kg + Kl) * φ := by
          have : Real.log 2 ≤ 1 := by
            have := Real.log_two_lt_d9; linarith
          nlinarith
  have hK₀Λ : K₀ * Λ ≤ K₀p * (1 + Kg + Kl) * φ := by
    calc K₀ * Λ ≤ K₀p * Λ := mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ0
      _ ≤ K₀p * ((1 + Kg + Kl) * φ) := mul_le_mul_of_nonneg_left hΛ hK₀p
      _ = _ := by ring
  refine ⟨Z, m, ?_, hm, hsum.trans hK₀Λ, ?_⟩
  · intro ρ; rw [hZ]; constructor <;> rintro ⟨h0, hd⟩ <;> exact ⟨h0, by linarith⟩
  · intro s hs hs0
    have := hloc s (by linarith) hs0
    calc _ ≤ K₀ * Λ / (3 * θ) := this
      _ ≤ K₀p * (1 + Kg + Kl) * φ / (3 * θ) := div_le_div_of_nonneg_right hK₀Λ (by positivity)
      _ = K₀p * (1 + Kg + Kl) / w / 3 := by rw [hθe]; field_simp
      _ ≤ K₀p * (1 + Kg + Kl) / w := by
          have : 0 ≤ K₀p * (1 + Kg + Kl) / w := by positivity
          linarith

lemma re_one_div_nonneg {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ (1 / z).re := by
  rw [one_div, Complex.inv_re]; exact div_nonneg hz (Complex.normSq_nonneg _)

lemma re_natCast_div (n : ℕ) (z : ℂ) : ((n : ℂ) / z).re = n * (1 / z).re := by
  rw [div_eq_mul_one_div, show ((n : ℂ)) = ((n : ℝ) : ℂ) by simp, Complex.re_ofReal_mul]

/-- **(Z1) Landau's local formula, one-sided.** -/
lemma landau_neg_re_upper (h : RichertZetaGrowth) : ∃ K t₁ : ℝ, ∀ t σ : ℝ, t₁ ≤ |t| → 1 < σ →
    σ ≤ 1 + vkTheta |t| → ∀ S : Finset ℂ, (∀ ρ ∈ S, riemannZeta ρ = 0 ∧
      ‖ρ - (1 + vkTheta |t| + t * I)‖ ≤ 15 / 8 * vkTheta |t|) →
    (-zLD (σ + t * I)).re ≤ K / vkW |t| - ∑ ρ ∈ S, (1 / ((σ : ℂ) + t * I - ρ)).re := by
  obtain ⟨K, t₁, hK, hL⟩ := zeta_local h
  refine ⟨K, t₁, fun t σ ht hσ1 hσθ S hS => ?_⟩
  obtain ⟨Z, m, hZ, hm, -, hloc⟩ := hL t ht
  set s : ℂ := σ + t * I with hs
  have hθ0 : 0 ≤ vkTheta |t| := by linarith
  have hsc : ‖s - lc t‖ ≤ 3 / 2 * vkTheta |t| := by
    have : s - lc t = ((σ - 1 - vkTheta |t| : ℝ) : ℂ) := by simp only [hs, lc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hs0 : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [hs]; linarith)
  have hE := hloc s hsc hs0
  have hSZ : S ⊆ Z := fun ρ hρ => (hZ ρ).mpr (hS ρ hρ)
  have hpos : ∀ ρ ∈ Z, 0 ≤ (1 / (s - ρ)).re := by
    intro ρ hρ
    have := zeta_zero_re_lt_one ((hZ ρ).mp hρ).1
    exact re_one_div_nonneg (by simp [hs]; linarith)
  have hsumS : ∑ ρ ∈ S, (1 / (s - ρ)).re ≤ (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re := by
    rw [Complex.re_sum]
    calc ∑ ρ ∈ S, (1 / (s - ρ)).re ≤ ∑ ρ ∈ S, ((m ρ : ℂ) / (s - ρ)).re := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [re_natCast_div]
          have h1 : (1 : ℝ) ≤ m ρ := by exact_mod_cast hm ρ (hSZ hρ)
          have := hpos ρ (hSZ hρ)
          nlinarith
      _ ≤ ∑ ρ ∈ Z, ((m ρ : ℂ) / (s - ρ)).re := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hSZ fun ρ hρ _ => ?_
          rw [re_natCast_div]; exact mul_nonneg (Nat.cast_nonneg _) (hpos ρ hρ)
  have hre := re_neg_le_norm (zLD s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
  rw [neg_sub, Complex.sub_re] at hre
  have : (-zLD s).re = -(zLD s).re := by simp
  rw [this]
  linarith

/-- **(Z2) Landau's local formula, two-sided.** -/
lemma landau_logderiv_bound (h : RichertZetaGrowth) : ∃ K t₁ : ℝ, ∀ t σ η : ℝ, t₁ ≤ |t| →
    1 - vkTheta |t| / 4 ≤ σ → σ ≤ 1 + vkTheta |t| → 0 < η →
    (∀ ρ : ℂ, riemannZeta ρ = 0 → ‖ρ - (1 + vkTheta |t| + t * I)‖ ≤ 15 / 8 * vkTheta |t| →
      η ≤ ‖(σ : ℂ) + t * I - ρ‖) →
    riemannZeta (σ + t * I) ≠ 0 →
    ‖zLD (σ + t * I)‖ ≤ K / vkW |t| + K * Real.log (Real.log |t|) / η := by
  obtain ⟨K, t₁, hK, hL⟩ := zeta_local h
  refine ⟨K, t₁, fun t σ η ht hσl hσu hη hdist hs0 => ?_⟩
  obtain ⟨Z, m, hZ, hm, hsum, hloc⟩ := hL t ht
  set s : ℂ := σ + t * I with hs
  have hθ0 : 0 ≤ vkTheta |t| := by linarith
  have hsc : ‖s - lc t‖ ≤ 3 / 2 * vkTheta |t| := by
    have : s - lc t = ((σ - 1 - vkTheta |t| : ℝ) : ℂ) := by simp only [hs, lc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hE := hloc s hsc hs0
  have hZb : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / η := by
    rw [Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    have hd := hdist ρ ((hZ ρ).mp hρ).1 ((hZ ρ).mp hρ).2
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη hd
  have hsum' : (∑ ρ ∈ Z, (m ρ : ℝ)) / η ≤ K * Real.log (Real.log |t|) / η :=
    div_le_div_of_nonneg_right hsum hη.le
  calc ‖zLD s‖ = ‖(zLD s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
        rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hE (hZb.trans hsum')

end LeanFormalizations.Erdos385

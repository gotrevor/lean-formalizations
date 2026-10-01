/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Tail
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Analytic
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Terms

/-!
# Erdős #385, phase E4, step 4: the parameter choice

With `L = log X`, `θ = 1/2 − ε`: `y = ⌊L/8⌋`, `R = y²`, `j = ⌈L^θ⌉`, `K = ⌈c y / log y⌉`,
`Q = ⌊√X⌋`.  Then `y# R^j ≤ Q` and each term of `bad_count_le` is `≤ 2 X e^{−L^θ}`.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open LeanFormalizations.Literature LeanFormalizations.Erdos385 Finset

theorem le_rpow_of_div_nine {L y ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hL : 1 ≤ L)
    (hy : L / 9 ≤ y) (h3 : 3 ≤ L ^ (ε / 2)) :
    L ^ ((1 : ℝ) / 2 - ε) ≤ y ^ ((1 : ℝ) / 2 - ε / 2) := by
  have ha : 0 ≤ (1 : ℝ) / 2 - ε / 2 := by linarith
  have h1 : (L / 9) ^ ((1 : ℝ) / 2 - ε / 2) ≤ y ^ ((1 : ℝ) / 2 - ε / 2) :=
    Real.rpow_le_rpow (by linarith) hy ha
  rw [Real.div_rpow (by linarith) (by norm_num)] at h1
  have h9 : (9 : ℝ) ^ ((1 : ℝ) / 2 - ε / 2) ≤ 3 := by
    calc (9 : ℝ) ^ ((1 : ℝ) / 2 - ε / 2) ≤ (9 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := by
          rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hsplit : L ^ ((1 : ℝ) / 2 - ε / 2) = L ^ ((1 : ℝ) / 2 - ε) * L ^ (ε / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hθ0 : 0 ≤ L ^ ((1 : ℝ) / 2 - ε) := Real.rpow_nonneg (by linarith) _
  have h9p : 0 < (9 : ℝ) ^ ((1 : ℝ) / 2 - ε / 2) := by positivity
  rw [div_le_iff₀ h9p] at h1
  have : L ^ ((1 : ℝ) / 2 - ε) * 3 ≤ L ^ ((1 : ℝ) / 2 - ε / 2) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_left h3 hθ0
  have hyp : 0 ≤ y ^ ((1 : ℝ) / 2 - ε / 2) := Real.rpow_nonneg (by linarith) _
  nlinarith

theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem eventually_bad_le (h1 : ArithLargeSieve) (h2 : LinearSieveIntervalLower)
    (h3 : McDiarmidFinite) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ) ≤
        5 * X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 2 - ε)) := by
  classical
  obtain ⟨c, hc, y₀, htail⟩ := tail_bound h2 h3 (ε := ε / 2) (by linarith) (by linarith)
  obtain ⟨Yw, hpw⟩ := pool_weight_ge hc
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (eventually_L_conditions hε hε2)
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ, L₁ = max L₀ (9 * ((y₀ : ℝ) + Yw + 81) + 72) := ⟨_, rfl⟩
  refine ⟨⌈Real.exp L₁⌉₊ + 1, fun X hX => ?_⟩
  have hXL : Real.exp L₁ ≤ X := by
    have := Nat.le_ceil (Real.exp L₁)
    have : ((⌈Real.exp L₁⌉₊ + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
    push_cast at this; linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hXL
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  have hLL₁ : L₁ ≤ L := by
    rw [hL, ← Real.log_exp L₁]; exact Real.log_le_log (Real.exp_pos _) hXL
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hL₀ L (le_trans (hL₁ ▸ le_max_left _ _) hLL₁)
  have hL72 : 9 * ((y₀ : ℝ) + Yw + 81) + 72 ≤ L := le_trans (hL₁ ▸ le_max_right _ _) hLL₁
  have hy00 : (0 : ℝ) ≤ y₀ := Nat.cast_nonneg _
  have hYw0 : (0 : ℝ) ≤ Yw := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  -- `y`
  obtain ⟨y, hy⟩ : ∃ y : ℕ, y = ⌊L / 8⌋₊ := ⟨_, rfl⟩
  have hyle : (y : ℝ) ≤ L / 8 := by rw [hy]; exact Nat.floor_le (by linarith)
  have hyge : L / 9 ≤ y := by
    have := Nat.lt_floor_add_one (L / 8); rw [← hy] at this; linarith
  have hyb : (y₀ : ℝ) + Yw + 81 ≤ y := by linarith
  have hy_y₀ : y₀ ≤ y := by exact_mod_cast (show (y₀ : ℝ) ≤ y by linarith)
  have hy_Yw : Yw ≤ y := by exact_mod_cast (show (Yw : ℝ) ≤ y by linarith)
  have hy81 : 81 ≤ y := by exact_mod_cast (show (81 : ℝ) ≤ y by linarith)
  have hy1 : 1 ≤ y := by omega
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy1
  -- `j`, `K`, `Q`
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 : ℝ) / 2 - ε := ⟨_, rfl⟩
  rw [← hθ] at hc1 hc3 hc4
  have hLθ : 0 < L ^ θ := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌈L ^ θ⌉₊ := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by rw [hj]; exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hLθ).ne'
  have hjle : (j : ℝ) ≤ L ^ θ + 1 := by rw [hj]; exact (Nat.ceil_lt_add_one hLθ.le).le
  have hjge : L ^ θ ≤ j := by rw [hj]; exact Nat.le_ceil _
  have hjy : (j : ℝ) ≤ 4 * Real.sqrt y := by
    have h1 : L ^ θ ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hc5 (by linarith)
    have h2 : L ^ ((1 : ℝ) / 2) = Real.sqrt L := (Real.sqrt_eq_rpow L).symm
    have h3 : Real.sqrt L ≤ Real.sqrt (9 * y) := Real.sqrt_le_sqrt (by linarith)
    have h4 : Real.sqrt (9 * y) = 3 * Real.sqrt y := by
      rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have h5 : Real.sqrt 1 ≤ Real.sqrt y := Real.sqrt_le_sqrt hyR
    rw [Real.sqrt_one] at h5
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈c * y / Real.log y⌉₊ := ⟨_, rfl⟩
  have hKc : c * y / Real.log y ≤ K := by rw [hK]; exact Nat.le_ceil _
  have hW := hpw y hy_Yw j K hj1 hjy hKc
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = ⌊Real.sqrt X⌋₊ := ⟨_, rfl⟩
  have hsqX : Real.sqrt X = Real.exp (L / 2) := by
    have : (X : ℝ) = Real.exp (L / 2) ^ 2 := by
      rw [sq, ← Real.exp_add, add_halves, hL, Real.exp_log hXpos]
    rw [this, Real.sqrt_sq (Real.exp_pos _).le]
  have hQX : (Q : ℝ) ≤ Real.sqrt X := by rw [hQ]; exact Nat.floor_le (Real.sqrt_nonneg _)
  have hQ2 : (Q : ℝ) ^ 2 ≤ X := by
    calc (Q : ℝ) ^ 2 ≤ Real.sqrt X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQX 2
      _ = X := Real.sq_sqrt hXpos.le
  -- `y# R^j ≤ Q`
  have hlogy : Real.log y ≤ Real.log L := Real.log_le_log (by linarith) (by linarith)
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hyR
  have hPRr : ((primorial y * (y ^ 2) ^ j : ℕ) : ℝ) ≤ Real.sqrt X := by
    have hP4 : (primorial y : ℝ) ≤ Real.exp (y * Real.log 4) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      exact_mod_cast primorial_le_four_pow y
    have hRj : (((y ^ 2) ^ j : ℕ) : ℝ) = Real.exp ((2 * j : ℕ) * Real.log y) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]; push_cast; ring
    have hexp : (y : ℝ) * Real.log 4 + (2 * j : ℕ) * Real.log y ≤ L / 2 := by
      push_cast
      have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have e1 : (y : ℝ) * Real.log 4 ≤ L / 8 * Real.log 4 := mul_le_mul_of_nonneg_right hyle hl4
      have e2 : 2 * (j : ℝ) * Real.log y ≤ 2 * (L ^ θ + 1) * Real.log L := by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have := mul_le_mul hjle hlogy hlogy0 (by linarith)
        linarith
      have : L / 8 * Real.log 4 = L * Real.log 4 / 8 := by ring
      linarith
    rw [Nat.cast_mul, hRj, hsqX]
    calc (primorial y : ℝ) * Real.exp ((2 * j : ℕ) * Real.log y)
        ≤ Real.exp (y * Real.log 4) * Real.exp ((2 * j : ℕ) * Real.log y) :=
          mul_le_mul_of_nonneg_right hP4 (Real.exp_pos _).le
      _ = Real.exp ((y : ℝ) * Real.log 4 + (2 * j : ℕ) * Real.log y) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (L / 2) := Real.exp_le_exp.2 hexp
  have hPR : primorial y * (y ^ 2) ^ j ≤ Q := by rw [hQ]; exact Nat.le_floor hPRr
  -- the denominator
  have hPpos : (0 : ℝ) < primorial y := by exact_mod_cast primorial_pos y
  have hPr := primorial_le_mul_prod_sub_one y hy1
  have hPr0 : 0 < ∏ p ∈ ps y, ((p : ℝ) - 1) := by
    by_contra h; push Not at h
    have : (y : ℝ) * ∏ p ∈ ps y, ((p : ℝ) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have h8 : (0 : ℝ) < 8 ^ j := by positivity
  have hden : 0 < (∏ p ∈ ps y, ((p : ℝ) - 1)) * ((pool y (y ^ 2)).card.choose j : ℝ) *
      ((K : ℝ) / ((y ^ 2 : ℕ) : ℝ)) ^ j := by
    rw [mul_assoc]; exact mul_pos hPr0 (lt_of_lt_of_le h8 hW)
  have hB := bad_count_le h1 (X := X) (R := y ^ 2) (j := j) (K := K) (Q := Q) hy1 hPR hden
  -- term 1
  have hT1 : (((y ^ 2 : ℕ) : ℝ) + y) ≤ X * Real.exp (-(L ^ θ)) := by
    push_cast; exact term1_le hXpos hL (by linarith) (by linarith) hyle hc1
  -- term 2
  have hPX : (primorial y : ℝ) ≤ X := by
    have h1 : (primorial y : ℝ) ≤ ((primorial y * (y ^ 2) ^ j : ℕ) : ℝ) := by
      have hy2 : 0 < y ^ 2 := pow_pos (by omega) 2
      have : (1 : ℝ) ≤ (((y ^ 2) ^ j : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_pow j (y ^ 2) hy2
      rw [Nat.cast_mul]
      exact le_mul_of_one_le_right hPpos.le this
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    have h2 : Real.sqrt X ≤ X := sqrt_le_self_of_one_le hX1
    linarith
  have htailset : ((range (primorial y)).filter fun s => (uSet y s).card < K) =
      (range (primorial y)).filter fun s => ((uSet y s).card : ℝ) < c * y / Real.log y := by
    ext s; simp only [mem_filter, hK, Nat.lt_ceil]
  have hT2 := term2_le hPpos hPX (hθ ▸ le_rpow_of_div_nine hε hε2 hc5 hyge hc2)
    (htail y hy_y₀) (Nat.cast_nonneg _)
  rw [← htailset] at hT2
  -- term 3
  have hWe : Real.exp (2 * L ^ θ) ≤ ((pool y (y ^ 2)).card.choose j : ℝ) *
      ((K : ℝ) / ((y ^ 2 : ℕ) : ℝ)) ^ j := by
    refine le_trans ?_ hW
    have he : Real.exp 2 ≤ 8 := by
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    calc Real.exp (2 * L ^ θ) ≤ Real.exp (2 * j) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 2 ^ j := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ 8 ^ j := pow_le_pow_left₀ (Real.exp_pos _).le he j
  have hyE : (y : ℝ) ≤ Real.exp (L ^ θ) := by
    calc (y : ℝ) ≤ L := by linarith
      _ = Real.exp (Real.log L) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (L ^ θ) := Real.exp_le_exp.2 hc3
  have hT3 := term3_le hPpos (by linarith) hPr hQ2 (by positivity) hXpos.le
    hWe hyE
  rw [← hL, ← hθ]
  have := hB
  rw [mul_assoc (∏ p ∈ ps y, ((p : ℝ) - 1))] at this
  push_cast at this hT1 hT3
  linarith

end LeanFormalizations.Erdos385.Exceptional

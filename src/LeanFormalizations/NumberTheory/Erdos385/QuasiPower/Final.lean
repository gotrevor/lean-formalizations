/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Params

/-!
# Erdős #385, phase E8: the final real-analysis step

Write `B = m⁴/(log m)²`.  With `m⁴ ≤ L = log X ≤ 137 m⁴`, the target factor
`exp(−L/(32400 (log L)²))` is `≥ exp(−B/3600)` (`exp_target_ge`); each of the three terms of
`bound_m` is `≤ X exp(−B/3600)` (`term_pool`, `term_main`).
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open Real

/-- The target factor at `L ∈ [m⁴, 137 m⁴]` is at least `exp(−B/3600)`. -/
theorem exp_target_ge {m L : ℝ} (hm : 3 ≤ m) (hL1 : m ^ 4 ≤ L) (hL2 : L ≤ 137 * m ^ 4) :
    Real.exp (-(m ^ 4 / Real.log m ^ 2) / 3600) ≤
      Real.exp (-((1 / 32400) * L / Real.log L ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have hlm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hm4 : 0 < m ^ 4 := by positivity
  have hlL : 4 * Real.log m ≤ Real.log L := by
    have := Real.log_le_log hm4 hL1
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hsq : 16 * Real.log m ^ 2 ≤ Real.log L ^ 2 := by nlinarith
  have hp : 0 < Real.log m ^ 2 := by positivity
  have hL0 : 0 ≤ L := by linarith
  have h1 : L / Real.log L ^ 2 ≤ 137 * m ^ 4 / (16 * Real.log m ^ 2) :=
    div_le_div₀ (by positivity) hL2 (by positivity) hsq
  have h2 : 137 * m ^ 4 / (16 * Real.log m ^ 2) = 137 / 16 * (m ^ 4 / Real.log m ^ 2) := by
    field_simp
  have h3 : 0 ≤ m ^ 4 / Real.log m ^ 2 := by positivity
  rw [mul_div_assoc]
  nlinarith

/-- `t = ⌊log₂ m⌋ + 1 ≤ 3 log m` once `m ≥ 3`. -/
theorem t_le_three_log {m : ℕ} (hm : 3 ≤ m) :
    ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ 3 * Real.log m := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hpow : ((2 : ℝ) ^ Nat.log 2 m) ≤ m := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  push_cast
  nlinarith

set_option maxHeartbeats 400000 in
/-- The main term: `m⁴ (23/25)^k ≤ exp(−B/3600)` for `m ≥ 18000`. -/
theorem term_main {m : ℕ} (hm : 18000 ≤ m) :
    (m : ℝ) ^ 4 * (23 / 25 : ℝ) ^ (m ^ 4 / (16 * (Nat.log 2 m + 1) ^ 2)) ≤
      Real.exp (-((m : ℝ) ^ 4 / Real.log m ^ 2) / 3600) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = Nat.log 2 m + 1 := ⟨_, rfl⟩
  rw [← ht]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = m ^ 4 / (16 * t ^ 2) := ⟨_, rfl⟩
  rw [← hk]
  have hmR : (18000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlmm : Real.log m ≤ m := by linarith [Real.log_le_sub_one_of_pos hm0]
  have htR : (t : ℝ) ≤ 3 * Real.log m := by rw [ht]; exact t_le_three_log (by omega)
  have ht1 : 1 ≤ t := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
  -- k ≥ m⁴/(16t²) − 1
  have hkR : (m : ℝ) ^ 4 / (16 * t ^ 2) - 1 ≤ k := by
    have hd : m ^ 4 < (k + 1) * (16 * t ^ 2) := by
      have := Nat.lt_div_mul_add (a := m ^ 4) (show 0 < 16 * t ^ 2 by positivity)
      rw [← hk] at this; nlinarith [this]
    have hdR : (m : ℝ) ^ 4 < (k + 1) * (16 * t ^ 2) := by exact_mod_cast hd
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    linarith
  -- a = log(25/23) ∈ [2/25, 1]
  set a := Real.log (25 / 23 : ℝ) with ha
  have ha1 : (2 / 25 : ℝ) ≤ a := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 25 / 23 by norm_num)
    norm_num at this ⊢; linarith
  have ha2 : a ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 25 / 23 by norm_num)
    linarith
  have hpow : (23 / 25 : ℝ) ^ k = Real.exp (-(k * a)) := by
    have hl : Real.log (23 / 25) = -a := by rw [ha, ← Real.log_inv]; norm_num
    rw [← Real.exp_log (show (0 : ℝ) < 23 / 25 by norm_num), ← Real.exp_nat_mul, hl]
    norm_num
  have hm4 : (m : ℝ) ^ 4 = Real.exp (4 * Real.log m) := by
    rw [show (4 : ℝ) * Real.log m = Real.log ((m : ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [hpow]; nth_rewrite 1 [hm4]; rw [← Real.exp_add, Real.exp_le_exp]
  -- B ≥ m², and m⁴/(16t²) ≥ B/144
  set lm := Real.log m with hlm_def
  have hp : 0 < lm ^ 2 := by positivity
  set B := (m : ℝ) ^ 4 / lm ^ 2 with hB
  have hBm : (m : ℝ) ^ 2 ≤ B := by
    have : lm ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hlmm 2
    rw [hB, le_div_iff₀ hp]; nlinarith
  have hkB : B / 144 ≤ (m : ℝ) ^ 4 / (16 * t ^ 2) := by
    rw [hB, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 16 * (t : ℝ) ^ 2 ≤ 144 * lm ^ 2 := by nlinarith
    have hm4p : (0 : ℝ) ≤ (m : ℝ) ^ 4 := by positivity
    nlinarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hka : B / 1800 - 1 ≤ k * a := by
    have hB1 : 0 ≤ B / 144 - 1 := by nlinarith
    have hk' : B / 144 - 1 ≤ k := by linarith
    have := mul_le_mul hk' ha1 (by norm_num) hk0
    nlinarith
  have hmm : 18000 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- The two small terms: `2^{t²} + m⁹ ≤ 2 X exp(−B/3600)` once `X ≥ 2^{8m⁴}`. -/
theorem term_pool {m X : ℕ} (hm : 3 ≤ m) (hX : 2 ^ (8 * m ^ 4) ≤ X) :
    (2 : ℝ) ^ ((Nat.log 2 m + 1) ^ 2) + (m : ℝ) ^ 9 ≤
      2 * X * Real.exp (-((m : ℝ) ^ 4 / Real.log m ^ 2) / 3600) := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hB : (m : ℝ) ^ 4 / Real.log m ^ 2 / 3600 ≤ ((m ^ 4 : ℕ) : ℝ) := by
    push_cast
    have h1 : (m : ℝ) ^ 4 / Real.log m ^ 2 ≤ (m : ℝ) ^ 4 :=
      div_le_self (by positivity) (one_le_pow₀ hlm)
    have : 0 ≤ (m : ℝ) ^ 4 / Real.log m ^ 2 := by positivity
    linarith
  -- exp(N) ≤ 2^{2N}
  have hexp : Real.exp ((m ^ 4 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * m ^ 4) := by
    rw [← Real.exp_one_pow, pow_mul]
    gcongr
    linarith [Real.exp_one_lt_d9]
  have hXR : (2 : ℝ) ^ (8 * m ^ 4) ≤ X := by exact_mod_cast hX
  have hkey : (2 : ℝ) ^ (6 * m ^ 4) ≤ X * Real.exp (-((m : ℝ) ^ 4 / Real.log m ^ 2) / 3600) := by
    have he : Real.exp (-((m ^ 4 : ℕ) : ℝ)) ≤ Real.exp (-((m : ℝ) ^ 4 / Real.log m ^ 2) / 3600) :=
      Real.exp_le_exp.mpr (by rw [neg_div]; linarith)
    have h8 : (2 : ℝ) ^ (8 * m ^ 4) = 2 ^ (6 * m ^ 4) * 2 ^ (2 * m ^ 4) := by
      rw [← pow_add]; ring_nf
    have hpos : 0 < Real.exp ((m ^ 4 : ℕ) : ℝ) := Real.exp_pos _
    have hinv : Real.exp (-((m ^ 4 : ℕ) : ℝ)) * Real.exp ((m ^ 4 : ℕ) : ℝ) = 1 := by
      rw [← Real.exp_add]; simp
    have h6 : (0 : ℝ) ≤ 2 ^ (6 * m ^ 4) := by positivity
    calc (2 : ℝ) ^ (6 * m ^ 4) = 2 ^ (6 * m ^ 4) * Real.exp ((m ^ 4 : ℕ) : ℝ) *
          Real.exp (-((m ^ 4 : ℕ) : ℝ)) := by rw [mul_assoc, mul_comm (Real.exp _), hinv, mul_one]
      _ ≤ 2 ^ (6 * m ^ 4) * 2 ^ (2 * m ^ 4) * Real.exp (-((m ^ 4 : ℕ) : ℝ)) := by gcongr
      _ ≤ X * Real.exp (-((m : ℝ) ^ 4 / Real.log m ^ 2) / 3600) := by
        rw [← h8]; gcongr
  have ht : (Nat.log 2 m + 1) ^ 2 ≤ 6 * m ^ 4 := by
    have h1 : Nat.log 2 m < m := Nat.log_lt_self 2 (by omega)
    have h2 : (Nat.log 2 m + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : m ^ 2 ≤ m ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hm9 : m ^ 9 ≤ 2 ^ (6 * m ^ 4) := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    calc m ^ 9 ≤ (2 ^ m) ^ 9 := Nat.pow_le_pow_left h1.le 9
      _ = 2 ^ (9 * m) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (6 * m ^ 4) := Nat.pow_le_pow_right (by norm_num) (by
        have h3 : 3 ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hm 3
        have : m ^ 4 = m * m ^ 3 := by ring
        nlinarith)
  have h1 : (2 : ℝ) ^ ((Nat.log 2 m + 1) ^ 2) ≤ 2 ^ (6 * m ^ 4) :=
    pow_le_pow_right₀ (by norm_num) ht
  have h2 : (m : ℝ) ^ 9 ≤ 2 ^ (6 * m ^ 4) := by exact_mod_cast hm9
  linarith

end LeanFormalizations.Erdos385.QuasiPower

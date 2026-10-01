/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Total
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Esymm
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Window
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.MertensSums

/-!
# Erdős #385, phase E8: the parameter choice

With `t = ⌊log₂ m⌋ + 1`: `y = m⁴`, `Y = m⁹` (so `y = Y^{4/9}` and `log Y = (9/4) log y`),
`k = ⌊m⁴/(16 t²)⌋` positions, pool `(Y, 2^{t²}]`, `Q = 2^{4m⁴}`, `ρ = 1/20`, `δ₀ = 0.87`.
For `m` large and `X ≥ 2^{8m⁴}`:
`#{bad n ≤ X} ≤ 2^{t²} + m⁹ + m⁴ · C · 2X · (23/25)^k` (`bound_m`).
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open LeanFormalizations.Literature LeanFormalizations.Erdos385
  LeanFormalizations.Erdos385.Exceptional Finset

set_option maxHeartbeats 1000000 in
open scoped Classical in
theorem bound_m {C : ℝ} (h1 : LSWith C) (hC : 0 ≤ C) (h2 : LinearSieveIntervalLower) :
    ∃ m₀ : ℕ, ∀ X m : ℕ, m₀ ≤ m → 2 ^ (8 * m ^ 4) ≤ X →
      (((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ) ≤
        ((2 : ℝ) ^ ((Nat.log 2 m + 1) ^ 2) + (m : ℝ) ^ 9) +
          (m : ℝ) ^ 4 * (C * (X + X) * (23 / 25 : ℝ) ^ (m ^ 4 / (16 * (Nat.log 2 m + 1) ^ 2))) := by
  classical
  obtain ⟨c, hc, y₀w, hwin⟩ := exists_window h2
  obtain ⟨y₀d, hd⟩ := sum_inv_sub_one_le
  obtain ⟨N₀, hσ⟩ := sum_inv_ge
  set T : ℕ := max (max ⌈9 / (16 * c)⌉₊ ⌈9 * Real.exp 22⌉₊) 9 with hT
  refine ⟨max (max y₀w y₀d) (max N₀ (2 ^ T)), fun X m hm hX => ?_⟩
  have hmT : 2 ^ T ≤ m := le_of_max_le_right (le_of_max_le_right hm)
  have hT9 : 9 ≤ T := le_max_right _ _
  have hm2 : 2 ≤ m := le_trans (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) (by omega)) hmT
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = Nat.log 2 m + 1 := ⟨_, rfl⟩
  have hmt : m < 2 ^ t := by rw [ht]; exact Nat.lt_pow_succ_log_self (by norm_num) m
  have hTt : T ≤ t := by
    have : T ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) hmT
    omega
  have ht9 : 9 ≤ t := hT9.trans hTt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = m ^ 4 / (16 * t ^ 2) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, y = m ^ 4 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = m ^ 9 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = 2 ^ (t ^ 2) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 2 ^ (4 * m ^ 4) := ⟨_, rfl⟩
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogmt : Real.log m ≤ t * Real.log 2 := by
    have : (m : ℝ) ≤ 2 ^ t := by exact_mod_cast hmt.le
    calc Real.log m ≤ Real.log ((2 : ℝ) ^ t) := Real.log_le_log (by linarith) this
      _ = t * Real.log 2 := by rw [Real.log_pow]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have htR : (9 : ℝ) ≤ t := by exact_mod_cast ht9
  -- basic natural-number facts
  have hk16 : k * (16 * t ^ 2) ≤ m ^ 4 := by rw [hk]; exact Nat.div_mul_le_self _ _
  have hkm : k ≤ m ^ 4 := by
    have : 1 ≤ 16 * t ^ 2 := by have : 1 ≤ t := by omega
                                nlinarith
    nlinarith
  have hyY : y ≤ Y := by rw [hy, hY]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2kY : 2 * k ≤ Y := by
    have : 2 * m ^ 4 ≤ m ^ 9 := by
      have : m ^ 9 = m ^ 4 * m ^ 5 := by ring
      rw [this]
      have : 2 ≤ m ^ 5 := le_trans hm2 (Nat.le_self_pow (by norm_num) m)
      nlinarith [Nat.pow_pos (n := 4) (show 0 < m by omega)]
    rw [hY]; omega
  have hYR : Y ≤ R := by
    calc Y = m ^ 9 := hY
      _ ≤ (2 ^ t) ^ 9 := Nat.pow_le_pow_left hmt.le 9
      _ = 2 ^ (9 * t) := by ring
      _ ≤ 2 ^ (t ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      _ = R := hR.symm
  have hQle : primorial y * Y ^ k * R ^ k ≤ Q := by
    have hP : primorial y ≤ 2 ^ (2 * m ^ 4) := by
      calc primorial y ≤ 4 ^ y := primorial_le_four_pow y
        _ = 2 ^ (2 * m ^ 4) := by rw [hy, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hYk : Y ^ k ≤ 2 ^ (m ^ 4) := by
      calc Y ^ k = m ^ (9 * k) := by rw [hY, ← pow_mul]
        _ ≤ (2 ^ t) ^ (9 * k) := Nat.pow_le_pow_left hmt.le _
        _ = 2 ^ (t * (9 * k)) := by rw [← pow_mul]
        _ ≤ 2 ^ (m ^ 4) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hRk : R ^ k ≤ 2 ^ (m ^ 4) := by
      calc R ^ k = 2 ^ (t ^ 2 * k) := by rw [hR, ← pow_mul]
        _ ≤ 2 ^ (m ^ 4) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    calc primorial y * Y ^ k * R ^ k ≤ 2 ^ (2 * m ^ 4) * 2 ^ (m ^ 4) * 2 ^ (m ^ 4) := by
          gcongr
      _ = Q := by rw [hQ, ← pow_add, ← pow_add]; ring_nf
  have hQX : (Q : ℝ) ^ 2 ≤ X := by
    have : Q ^ 2 ≤ X := by
      calc Q ^ 2 = 2 ^ (8 * m ^ 4) := by rw [hQ, ← pow_mul]; ring_nf
        _ ≤ X := hX
    exact_mod_cast this
  -- the window input
  have hwin' : ∀ s : ℕ, ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ Y) ∧
      (∀ a ∈ A, ∀ p, p.Prime → p ≤ y → s % p ≠ a % p) ∧ (∀ a ∈ A, ∀ b ∈ A, b < a + y) := by
    intro s
    have hyw : y₀w ≤ y := (le_of_max_le_left (le_of_max_le_left hm)).trans
      (show m ≤ y by rw [hy]; exact Nat.le_self_pow (by norm_num) m)
    have hrp : (y : ℝ) ≤ (Y : ℝ) ^ ((4 : ℝ) / 9) := by
      have : ((Y : ℕ) : ℝ) ^ ((4 : ℝ) / 9) = (y : ℝ) := by
        rw [hY, hy]; push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
        norm_num
      rw [this]
    obtain ⟨A0, hA0c, hA01, hA0y, hA0d⟩ := hwin y Y hyw hrp s
    have hkA : k ≤ A0.card := by
      have hlogY : Real.log (Y : ℝ) = 9 * Real.log m := by rw [hY]; push_cast; rw [Real.log_pow]; norm_num
      have hk' : (k : ℝ) ≤ c * y / Real.log Y := by
        have hkr : (k : ℝ) * (16 * t ^ 2) ≤ m ^ 4 := by exact_mod_cast hk16
        rw [hlogY, le_div_iff₀ (by positivity)]
        have hcT : 9 ≤ 16 * c * t := by
          have h9 : 9 / (16 * c) ≤ (T : ℝ) := by
            have := Nat.le_ceil (9 / (16 * c))
            have hT0 : ⌈9 / (16 * c)⌉₊ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
            exact this.trans (by exact_mod_cast hT0)
          have : (T : ℝ) ≤ t := by exact_mod_cast hTt
          have := h9.trans this
          rw [div_le_iff₀ (by positivity)] at this
          linarith
        have hy' : (y : ℝ) = (m : ℝ) ^ 4 := by rw [hy]; push_cast; ring
        rw [hy']
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        -- k * 9 log m ≤ k * 9 t ≤ k * 16 c t² ≤ c m^4
        have e1 : (k : ℝ) * (9 * Real.log m) ≤ k * (9 * t) := by
          have : Real.log m ≤ t := by nlinarith
          nlinarith
        have e2 : (k : ℝ) * (9 * t) ≤ k * (16 * c * t * t) := by
          have : 9 * (t : ℝ) ≤ 16 * c * t * t := by nlinarith
          exact mul_le_mul_of_nonneg_left this hk0
        nlinarith
      exact_mod_cast hk'.trans hA0c
    obtain ⟨A, hAs, hAc⟩ := exists_subset_card_eq hkA
    exact ⟨A, hAc, fun a ha => hA01 a (hAs ha), fun a ha => hA0y a (hAs ha),
      fun a ha b hb => hA0d a (hAs ha) b (hAs hb)⟩
  -- the pool weight input
  have hw : ∀ K ≤ k, 1 ≤ (1 / 20 : ℝ) ^ K * poolWeight ((Ioc Y R).filter Nat.Prime) K K := by
    intro K hK
    have hpool : ∀ q ∈ (Ioc Y R).filter Nat.Prime, Y < q := fun q hq =>
      (mem_Ioc.1 (mem_filter.1 hq).1).1
    have hpw := poolWeight_ge hpool (show 2 * K ≤ Y by omega)
    have hYN : N₀ ≤ Y := (le_of_max_le_left (le_of_max_le_right hm)).trans
      (show m ≤ Y by rw [hY]; exact Nat.le_self_pow (by norm_num) m)
    have hs := hσ Y R hYN hYR
    have hlogY : Real.log (Y : ℝ) = 9 * Real.log m := by rw [hY]; push_cast; rw [Real.log_pow]; norm_num
    have hlogR : Real.log (R : ℝ) = t ^ 2 * Real.log 2 := by
      rw [hR]; push_cast; rw [Real.log_pow]; push_cast; ring
    have hratio : Real.exp 22 ≤ Real.log R / Real.log Y := by
      rw [hlogR, hlogY, le_div_iff₀ (by positivity)]
      have h1 : 9 * Real.exp 22 ≤ (t : ℝ) := by
        have := Nat.le_ceil (9 * Real.exp 22)
        have hT1 : ⌈9 * Real.exp 22⌉₊ ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
        exact this.trans (by exact_mod_cast hT1.trans hTt)
      have : Real.exp 22 * (9 * Real.log m) ≤ Real.exp 22 * (9 * (t * Real.log 2)) := by
        gcongr
      nlinarith [Real.exp_pos 22]
    have hll : 22 ≤ Real.log (Real.log R) - Real.log (Real.log Y) := by
      rw [← Real.log_div (by rw [hlogR]; positivity) (by rw [hlogY]; positivity)]
      calc (22 : ℝ) = Real.log (Real.exp 22) := (Real.log_exp 22).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 22) hratio
    have hKY : 2 * (K : ℝ) / Y ≤ 1 := by
      rw [div_le_one (by rw [hY]; push_cast; positivity)]; exact_mod_cast (show 2 * K ≤ Y by omega)
    have hbase : (20 : ℝ) ≤ max 0 (∑ q ∈ (Ioc Y R).filter Nat.Prime, (1 : ℝ) / q - 2 * K / Y) :=
      le_max_of_le_right (by linarith)
    calc (1 : ℝ) = (1 / 20 : ℝ) ^ K * 20 ^ K := by rw [← mul_pow]; norm_num
      _ ≤ (1 / 20 : ℝ) ^ K * (max 0 (∑ q ∈ (Ioc Y R).filter Nat.Prime, (1 : ℝ) / q -
            2 * K / Y)) ^ K := by gcongr
      _ ≤ _ := by gcongr
  -- the per-position input
  have hδ : ∀ a ≤ Y, ∑ p ∈ (Ioc y a).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 0.87 := by
    intro a ha
    have hyd : y₀d ≤ y := (le_of_max_le_right (le_of_max_le_left hm)).trans
      (show m ≤ y by rw [hy]; exact Nat.le_self_pow (by norm_num) m)
    refine hd y Y a hyd ?_ ha
    rw [hY, hy]; push_cast; rw [Real.log_pow, Real.log_pow]; push_cast
    nlinarith
  have htot := total_count h1 hC (X := X) (1 / 20) 0.87 (by norm_num)
    (show 1 ≤ y by rw [hy]; exact Nat.one_le_pow _ _ (by omega))
    hyY (show 1 ≤ R by rw [hR]; exact Nat.one_le_two_pow) hwin' hQle hw hδ
  have hb : (1 / 20 + 0.87 : ℝ) = 23 / 25 := by norm_num
  rw [hb] at htot
  have hRc : (R : ℝ) = (2 : ℝ) ^ ((Nat.log 2 m + 1) ^ 2) := by rw [hR, ht]; push_cast; ring
  have hYc : (Y : ℝ) = (m : ℝ) ^ 9 := by rw [hY]; push_cast; ring
  have hyc : (y : ℝ) = (m : ℝ) ^ 4 := by rw [hy]; push_cast; ring
  have hkk : m ^ 4 / (16 * (Nat.log 2 m + 1) ^ 2) = k := by rw [hk, ht]
  rw [hkk, ← hRc, ← hYc, ← hyc]
  refine htot.trans ?_
  have hb0 : (0 : ℝ) ≤ (23 / 25 : ℝ) ^ k := by positivity
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have : C * (X + (Q : ℝ) ^ 2) ≤ C * (X + X) := by gcongr
  have : C * (X + (Q : ℝ) ^ 2) * (23 / 25 : ℝ) ^ k ≤ C * (X + X) * (23 / 25 : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right this hb0
  have := mul_le_mul_of_nonneg_left this hy0
  linarith

end LeanFormalizations.Erdos385.QuasiPower

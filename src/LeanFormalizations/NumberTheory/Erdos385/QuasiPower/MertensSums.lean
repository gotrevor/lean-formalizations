/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Mertens

/-!
# Erdős #385, phase E8: the two Mertens sums

From `∑_{p ≤ N} 1/p = log log N + M + o(1)` (`Mertens.mertens_second_tendsto`):

* `sum_inv_sub_one_le`: `∑_{y < p ≤ a} 1/(p − 1) ≤ 0.87` once `a ≤ Y`, `log Y ≤ 2.3 log y`, `y` large
  (`log 2.3 < 0.844`): the per-position factor of `class_count` stays below `1 − ρ`.
* `sum_inv_ge`: `∑_{Y < q ≤ R} 1/q ≥ log log R − log log Y − 1` for `Y` large: the pool weight.
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open Finset Filter LeanFormalizations.Mertens

theorem primeRecipSum_sub' (w z : ℕ) (h : w ≤ z) :
    primeRecipSum z - primeRecipSum w = ∑ p ∈ (Ioc w z).filter Nat.Prime, (p : ℝ)⁻¹ := by
  unfold primeRecipSum
  rw [sum_filter, sum_filter, sum_filter, sub_eq_iff_eq_add,
    ← sum_Ioc_consecutive _ (Nat.zero_le w) h]
  ring

theorem eventually_close {η : ℝ} (hη : 0 < η) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    |primeRecipSum N - Real.log (Real.log N) - meisselMertensM| ≤ η := by
  obtain ⟨N₀, h⟩ := Metric.tendsto_atTop.1 mertens_second_tendsto η hη
  exact ⟨N₀, fun N hN => (h N hN).le⟩

theorem log_two_point_three_lt : Real.log 2.3 < 0.844 := by
  have h1 : Real.log 2.3 = Real.log 2 + Real.log 1.15 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 : Real.log 1.15 ≤ 1.15 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h3 := Real.log_two_lt_d9
  rw [h1]; linarith

theorem sum_inv_ge : ∃ N₀ : ℕ, ∀ Y R : ℕ, N₀ ≤ Y → Y ≤ R →
    Real.log (Real.log R) - Real.log (Real.log Y) - 1 ≤
      ∑ q ∈ (Ioc Y R).filter Nat.Prime, (1 : ℝ) / q := by
  obtain ⟨N₀, h⟩ := eventually_close (η := 1 / 2) (by norm_num)
  refine ⟨N₀, fun Y R hY hYR => ?_⟩
  have e := primeRecipSum_sub' Y R hYR
  simp only [one_div]
  rw [← e]
  have h1 := abs_le.1 (h R (hY.trans hYR))
  have h2 := abs_le.1 (h Y hY)
  linarith [h1.1, h2.2]

theorem sum_inv_sub_one_le : ∃ y₀ : ℕ, ∀ y Y a : ℕ, y₀ ≤ y →
    Real.log Y ≤ 2.3 * Real.log y → a ≤ Y →
      ∑ p ∈ (Ioc y a).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ 0.87 := by
  obtain ⟨N₀, h⟩ := eventually_close (η := 1 / 1000) (by norm_num)
  refine ⟨max N₀ 1000, fun y Y a hy hlog haY => ?_⟩
  have hyN : N₀ ≤ y := le_of_max_le_left hy
  have hy1000 : 1000 ≤ y := le_of_max_le_right hy
  have hyR : (1000 : ℝ) ≤ y := by exact_mod_cast hy1000
  rcases le_total a y with hay | hya
  · rw [Ioc_eq_empty (by omega)]; simp only [filter_empty, sum_empty]; norm_num
  have hyY : y ≤ Y := hya.trans haY
  -- termwise: 1/(p-1) ≤ (1 + 2/y) / p
  have hterm : ∀ p ∈ (Ioc y a).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤ (1 + 2 / y) * (p : ℝ)⁻¹ := by
    intro p hp
    have hpy : (y : ℝ) < p := by exact_mod_cast (mem_Ioc.1 (mem_filter.1 hp).1).1
    rw [div_le_iff₀ (by linarith), mul_assoc, inv_mul_eq_div]
    have e : ((p : ℝ) - 1) / p = 1 - 1 / p := by
      rw [sub_div, div_self (ne_of_gt (by linarith : (0:ℝ) < p))]
    rw [e]
    have hu : (1 : ℝ) / p ≤ 1 / y := one_div_le_one_div_of_le (by linarith) hpy.le
    have hu0 : (0 : ℝ) ≤ 1 / p := by positivity
    have ht : (1 : ℝ) / y ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hyR
    have h2y : 2 / (y : ℝ) = 2 * (1 / y) := by ring
    rw [h2y]
    nlinarith [mul_le_mul_of_nonneg_left hu (show (0:ℝ) ≤ 2 * (1 / y) by positivity)]
  have hsum : ∑ p ∈ (Ioc y a).filter Nat.Prime, (p : ℝ)⁻¹ ≤ 0.844 + 0.002 := by
    calc ∑ p ∈ (Ioc y a).filter Nat.Prime, (p : ℝ)⁻¹
        ≤ ∑ p ∈ (Ioc y Y).filter Nat.Prime, (p : ℝ)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ioc_subset_Ioc_right haY))
            fun _ _ _ => by positivity
      _ = primeRecipSum Y - primeRecipSum y := (primeRecipSum_sub' y Y hyY).symm
      _ ≤ Real.log (Real.log Y) - Real.log (Real.log y) + 0.002 := by
          have h1 := abs_le.1 (h Y (hyN.trans hyY))
          have h2 := abs_le.1 (h y hyN)
          linarith [h1.2, h2.1]
      _ ≤ 0.844 + 0.002 := by
          have hly : 0 < Real.log y := Real.log_pos (by linarith)
          have hlY : 0 < Real.log Y := Real.log_pos (by
            have : (y : ℝ) ≤ Y := by exact_mod_cast hyY
            linarith)
          rw [← Real.log_div hlY.ne' hly.ne']
          have : Real.log (Real.log Y / Real.log y) ≤ Real.log 2.3 :=
            Real.log_le_log (by positivity) (by rw [div_le_iff₀ hly]; linarith)
          linarith [log_two_point_three_lt]
  calc ∑ p ∈ (Ioc y a).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1)
      ≤ ∑ p ∈ (Ioc y a).filter Nat.Prime, (1 + 2 / y) * (p : ℝ)⁻¹ := sum_le_sum hterm
    _ = (1 + 2 / y) * ∑ p ∈ (Ioc y a).filter Nat.Prime, (p : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ (1 + 2 / 1000) * (0.844 + 0.002) := by
        have h0 : 0 ≤ ∑ p ∈ (Ioc y a).filter Nat.Prime, (p : ℝ)⁻¹ := sum_nonneg fun _ _ => by positivity
        have : 2 / (y : ℝ) ≤ 2 / 1000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hyR
        gcongr
    _ ≤ 0.87 := by norm_num

end LeanFormalizations.Erdos385.QuasiPower

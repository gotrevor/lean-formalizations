/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Mertens
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.CRT

/-!
# Erdős #385, phase E4: prime sums over `(y^θ, y]`

* `exists_prod_high_ge`: `∏_{y^θ < p ≤ y} (1 − 1/p) ≥ δ(θ) > 0` (Mertens' second theorem).
* `sum_high_inv_sq_le`: `∑_{z < p ≤ y} 1/p² ≤ 1/⌊z⌋`.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open Finset Filter LeanFormalizations.Mertens

/-- The primes `p ≤ y` with `p > z`. -/
noncomputable def hiPs (y : ℕ) (z : ℝ) : Finset ℕ := (ps y).filter fun p => ¬ (p : ℝ) ≤ z

theorem sum_Ioc_inv_sq_le (a b : ℕ) (ha : 1 ≤ a) :
    ∑ k ∈ Ioc a b, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / a - 1 / max a b := by
  induction b with
  | zero => rw [Ioc_eq_empty (by omega)]; simp
  | succ b ih =>
    rcases le_or_gt (b + 1) a with h | h
    · rw [Ioc_eq_empty (by omega)]
      simp [max_eq_left h]
    · have hI : Ioc a (b + 1) = insert (b + 1) (Ioc a b) := by ext; simp; omega
      rw [hI, sum_insert (by simp), max_eq_right h.le]
      rw [max_eq_right (by omega : a ≤ b)] at ih
      have hb : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      push_cast
      have : (1 : ℝ) / ((b : ℝ) + 1) ^ 2 ≤ 1 / b - 1 / (b + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith

theorem sum_high_inv_sq_le (y : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    ∑ p ∈ hiPs y z, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (⌊z⌋₊ : ℝ) := by
  have hz1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hsub : hiPs y z ⊆ Ioc ⌊z⌋₊ y := by
    intro p hp
    simp only [hiPs, ps, mem_filter, mem_range, not_le] at hp
    exact mem_Ioc.2 ⟨Nat.floor_lt' (by have := hp.1.2.pos; omega) |>.2 hp.2, by omega⟩
  calc ∑ p ∈ hiPs y z, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ k ∈ Ioc ⌊z⌋₊ y, (1 : ℝ) / (k : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 1 / ⌊z⌋₊ - 1 / max ⌊z⌋₊ y := sum_Ioc_inv_sq_le _ _ hz1
    _ ≤ 1 / ⌊z⌋₊ := by
        have : (0 : ℝ) ≤ 1 / (max ⌊z⌋₊ y : ℕ) := by positivity
        push_cast at this ⊢; linarith

theorem one_sub_ge_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-2 * x) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hpos : 0 < 1 + 2 * x := by linarith
  have : Real.exp (-2 * x) = (Real.exp (2 * x))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  rw [this]
  calc (Real.exp (2 * x))⁻¹ ≤ (1 + 2 * x)⁻¹ := by
        apply inv_anti₀ hpos; linarith
    _ ≤ 1 - x := by
        rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith

/-- **Mertens product over `(y^θ, y]`.** -/
theorem exists_prod_high_ge {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      δ ≤ ∏ p ∈ hiPs y ((y : ℝ) ^ θ), (1 - 1 / (p : ℝ)) := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.1 mertens_second
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hC
  set S₀ : ℝ := Real.log (2 / θ) + 2 * C
  refine ⟨Real.exp (-2 * S₀), Real.exp_pos _, ?_⟩
  have hev : ∀ᶠ y : ℕ in atTop, (2 * (N₀ : ℝ) + 2 ≤ (y : ℝ) ^ θ) ∧
      (2 * Real.log 2 / θ ≤ Real.log y) ∧ (1 ≤ (y : ℝ)) := by
    have h1 : Tendsto (fun y : ℕ => (y : ℝ) ^ θ) atTop atTop :=
      (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun y : ℕ => Real.log y) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (h1.eventually_ge_atTop _).and ((h2.eventually_ge_atTop _).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop _))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 hev
  refine ⟨y₀, fun y hy => ?_⟩
  obtain ⟨hz, hly, hy1⟩ := hy₀ y hy
  set z : ℝ := (y : ℝ) ^ θ with hzdef
  set m : ℕ := ⌊z⌋₊ with hm
  have hz0 : 0 ≤ z := by positivity
  have hmz : z / 2 ≤ m := by
    have := Nat.lt_floor_add_one z
    have : (1 : ℝ) ≤ z := by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
    linarith
  have hmN : N₀ ≤ m := by
    have : (N₀ : ℝ) ≤ m := by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
    exact_mod_cast this
  have hmy : m ≤ y := by
    have : z ≤ y := by
      rw [hzdef]
      calc (y : ℝ) ^ θ ≤ (y : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 hθ1.le
        _ = y := Real.rpow_one _
    exact Nat.floor_le_of_le this
  -- the reciprocal sum over the high primes
  have hsplit : primeRecipSum y = primeRecipSum m + ∑ p ∈ hiPs y z, (p : ℝ)⁻¹ := by
    have hhi : hiPs y z = (Ioc m y).filter Nat.Prime := by
      ext p
      simp only [hiPs, ps, mem_filter, mem_range, mem_Ioc, not_le]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨(Nat.floor_lt hz0).2 h3, by omega⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by omega, h3⟩, (Nat.floor_lt hz0).1 h1⟩
    simp only [primeRecipSum, hhi, sum_filter]
    rw [sum_Ioc_consecutive _ (Nat.zero_le m) hmy]
  have hRy := hN₀ y (by omega)
  have hRm := hN₀ m hmN
  simp only [norm_one, mul_one, Real.norm_eq_abs] at hRy hRm
  have hlogm : (θ / 2) * Real.log y ≤ Real.log m := by
    have hm0 : 0 < (m : ℝ) := by
      have : (0 : ℝ) < z / 2 := by
        have : (2 : ℝ) ≤ z := by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
        linarith
      linarith
    have : Real.log (z / 2) ≤ Real.log m := Real.log_le_log (by
      have : (2 : ℝ) ≤ z := by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
      linarith) hmz
    rw [Real.log_div (by positivity) (by norm_num), hzdef, Real.log_rpow (by linarith)] at this
    have : θ * (2 * Real.log 2 / θ) = 2 * Real.log 2 := by field_simp
    nlinarith
  have hlogy : 0 < Real.log y := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : 0 < 2 * Real.log 2 / θ := by positivity
    linarith
  have hdiff : Real.log (Real.log y) - Real.log (Real.log m) ≤ Real.log (2 / θ) := by
    have h1 : Real.log ((θ / 2) * Real.log y) ≤ Real.log (Real.log m) :=
      Real.log_le_log (by positivity) hlogm
    rw [Real.log_mul (by positivity) hlogy.ne', Real.log_div hθ.ne' (by norm_num),
      Real.log_div (by norm_num) hθ.ne'] at *
    linarith
  have hsum : ∑ p ∈ hiPs y z, (p : ℝ)⁻¹ ≤ S₀ := by
    have := abs_le.1 hRy; have := abs_le.1 hRm
    simp only [S₀]; linarith
  -- product ≥ exp(−2 Σ)
  have hprod : Real.exp (-2 * ∑ p ∈ hiPs y z, (p : ℝ)⁻¹) ≤
      ∏ p ∈ hiPs y z, (1 - 1 / (p : ℝ)) := by
    rw [mul_sum, Real.exp_sum]
    apply prod_le_prod (fun _ _ => (Real.exp_pos _).le)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (mem_filter.1 (mem_filter.1 hp).1).2.two_le
    rw [one_div]
    exact one_sub_ge_exp (by positivity) (by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith)
  calc Real.exp (-2 * S₀) ≤ Real.exp (-2 * ∑ p ∈ hiPs y z, (p : ℝ)⁻¹) :=
        Real.exp_le_exp.2 (by linarith)
    _ ≤ _ := hprod

end LeanFormalizations.Erdos385.Exceptional

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Mellin

/-!
# Frequency-side facts about `A(1+it)` for `a` supported on `[X, 4X]`

Continuity and the crude bound `|A(1+it)| ≤ 4`.
-/

open MeasureTheory Complex Set
open scoped FourierTransform

noncomputable section

namespace Erdos385.Parseval

variable {a : ℕ → ℂ} {X : ℝ}

lemma supp_floor (hX : 0 < X) (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) :
    ∀ m, (m = 0 ∨ ⌊4 * X⌋₊ < m) → a m = 0 := by
  rintro m (rfl | hm)
  · exact hsupp 0 (Or.inl (by simpa using hX))
  · exact hsupp m (Or.inr (Nat.floor_lt (by linarith) |>.mp hm))

lemma continuous_LSeries_line (hX : 0 < X)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) :
    Continuous fun t : ℝ ↦ LSeries a (1 + t * I) := by
  simp_rw [LSeries_eq_sum (supp_floor hX hsupp)]
  refine continuous_finsetSum _ fun m _ ↦ continuous_const.mul ?_
  refine Continuous.const_cpow (by fun_prop) (Or.inr fun t h ↦ ?_)
  have := congrArg Complex.re h
  simp at this

lemma norm_LSeries_line_le (hX : 1 ≤ X) (ha1 : ∀ m, ‖a m‖ ≤ 1)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) (t : ℝ) :
    ‖LSeries a (1 + t * I)‖ ≤ 4 := by
  have hX0 : 0 < X := by linarith
  set N := ⌊4 * X⌋₊
  rw [LSeries_eq_sum (supp_floor hX0 hsupp)]
  have hterm : ∀ m ∈ Finset.range (N + 1), ‖a m * (m : ℂ) ^ (-(1 + t * I))‖ ≤
      if X ≤ (m : ℝ) then 1 / X else 0 := by
    intro m _
    by_cases hm : X ≤ (m : ℝ)
    · rw [if_pos hm, norm_mul]
      have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hX0 hm
      rw [norm_natCast_cpow_of_pos (by exact_mod_cast hm0)]
      simp only [neg_re, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, Real.rpow_neg_one]
      calc ‖a m‖ * (m : ℝ)⁻¹ ≤ 1 * X⁻¹ := by
            gcongr
            exact ha1 m
        _ = 1 / X := by ring
    · rw [if_neg hm, hsupp m (Or.inl (not_le.mp hm)), zero_mul, norm_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range (N + 1)).filter (fun m : ℕ ↦ X ≤ (m : ℝ))).card ≤
      (Finset.Icc ⌈X⌉₊ N).card := by
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    simp only [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hm.2, by omega⟩
  rw [Nat.card_Icc] at hcard
  have hceil : ⌈X⌉₊ ≤ N + 1 := by
    have : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    have : (N : ℝ) + 1 > 4 * X := Nat.lt_floor_add_one _
    exact_mod_cast (show (⌈X⌉₊ : ℝ) ≤ N + 1 by linarith)
  have hc : (((Finset.range (N + 1)).filter (fun m : ℕ ↦ X ≤ (m : ℝ))).card : ℝ) ≤ 3 * X + 1 := by
    have h1 : (((Finset.range (N + 1)).filter (fun m : ℕ ↦ X ≤ (m : ℝ))).card : ℝ) ≤
        ((N + 1 - ⌈X⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_sub hceil] at h1
    have : (N : ℝ) ≤ 4 * X := Nat.floor_le (by linarith)
    have : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    push_cast at h1
    linarith
  calc _ ≤ (3 * X + 1) * (1 / X) := by gcongr
    _ ≤ 4 := by rw [mul_one_div, div_le_iff₀ hX0]; linarith

end Erdos385.Parseval

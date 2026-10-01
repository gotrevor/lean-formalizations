/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Sieve

/-!
# Erdős #385, phase E8: a lower bound for elementary symmetric sums

`j! · e_j(x) ≥ (∑ x − (j − 1) m)₊^j` when `0 ≤ x ≤ m` (`esymm_lower`), by induction on the
set: `e_j(s ∪ {a}) = e_j(s) + x_a e_{j−1}(s)` and `c^j − a^j ≤ j (c − a) c^{j−1}`.
Specialized to the pool weight: `poolWeight pool K K ≥ (∑_{q ∈ pool} 1/q − 2K/Y)^K` for a pool
above `Y ≥ 2K` (`poolWeight_ge`).
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open Finset

/-- The key one-step inequality. -/
theorem step_ineq {a c d x : ℝ} {j : ℕ} (ha : 0 ≤ a) (hc0 : 0 ≤ c) (hx : 0 ≤ x)
    (hca : c ≤ a + x) (hcd : c ≤ d) : c ^ (j + 1) ≤ a ^ (j + 1) + (j + 1) * x * d ^ j := by
  have hd0 : 0 ≤ d := hc0.trans hcd
  rcases le_total c a with h | h
  · have : c ^ (j + 1) ≤ a ^ (j + 1) := pow_le_pow_left₀ hc0 h _
    have : 0 ≤ (j + 1 : ℝ) * x * d ^ j := by positivity
    linarith
  · have hj := abs_pow_sub_pow_le c a (j + 1)
    rw [abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ ha h _)), abs_of_nonneg (sub_nonneg.2 h),
      max_eq_left (by rw [abs_of_nonneg ha, abs_of_nonneg hc0]; exact h), abs_of_nonneg hc0,
      Nat.add_sub_cancel] at hj
    have hdc : c ^ j ≤ d ^ j := pow_le_pow_left₀ hc0 hcd _
    push_cast at hj
    have h1 : c - a ≤ x := by linarith
    have h2 : 0 ≤ c - a := by linarith
    have : (c - a) * (j + 1) * c ^ j ≤ x * (j + 1) * d ^ j := by
      gcongr
    nlinarith

/-- The elementary symmetric sum of a weight over a finset. -/
noncomputable def esum (x : ℕ → ℝ) (s : Finset ℕ) (j : ℕ) : ℝ :=
  ∑ T ∈ s.powersetCard j, ∏ q ∈ T, x q

theorem esum_insert (x : ℕ → ℝ) {s : Finset ℕ} {a : ℕ} (ha : a ∉ s) (j : ℕ) :
    esum x (insert a s) (j + 1) = esum x s (j + 1) + x a * esum x s j := by
  classical
  unfold esum
  rw [powersetCard_succ_insert ha, sum_union, sum_image, mul_sum]
  · congr 1
    refine sum_congr rfl fun T hT => ?_
    have : a ∉ T := fun h => ha ((mem_powersetCard.1 hT).1 h)
    rw [prod_insert this]
  · intro T hT T' hT' h
    have h1 : a ∉ T := fun h' => ha ((mem_powersetCard.1 hT).1 h')
    have h2 : a ∉ T' := fun h' => ha ((mem_powersetCard.1 hT').1 h')
    have := congrArg (fun U => U.erase a) h
    simpa [erase_insert h1, erase_insert h2] using this
  · rw [disjoint_left]
    intro T hT hT'
    obtain ⟨U, -, rfl⟩ := mem_image.1 hT'
    exact ha ((mem_powersetCard.1 hT).1 (mem_insert_self _ _))

theorem esum_zero (x : ℕ → ℝ) (s : Finset ℕ) : esum x s 0 = 1 := by
  simp [esum]

theorem esum_nonneg {x : ℕ → ℝ} (hx : ∀ q, 0 ≤ x q) (s : Finset ℕ) (j : ℕ) : 0 ≤ esum x s j :=
  sum_nonneg fun T _ => prod_nonneg fun q _ => hx q

/-- `j! e_j ≥ (∑ x − (j−1) m)₊^j`. -/
theorem esymm_lower {x : ℕ → ℝ} {m : ℝ} (hx : ∀ q, 0 ≤ x q) (hm : 0 ≤ m) (s : Finset ℕ)
    (hxm : ∀ q ∈ s, x q ≤ m) (j : ℕ) :
    max 0 (∑ q ∈ s, x q - (j - 1) * m) ^ j ≤ (j.factorial : ℝ) * esum x s j := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    rcases j with _ | j
    · simp [esum_zero]
    · simp only [sum_empty, zero_sub, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [max_eq_left (by nlinarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j])]
      simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow]
      exact mul_nonneg (by positivity) (esum_nonneg hx _ _)
  | insert a s ha ih =>
    have hxm' : ∀ q ∈ s, x q ≤ m := fun q hq => hxm q (mem_insert_of_mem hq)
    have hxa : x a ≤ m := hxm a (mem_insert_self _ _)
    rcases j with _ | j
    · simp [esum_zero]
    rw [esum_insert x ha, sum_insert ha]
    have ih1 := ih hxm' (j + 1)
    have ih0 := ih hxm' j
    set S := ∑ q ∈ s, x q
    set A0 := max 0 (S - ((j + 1 : ℕ) - 1) * m)
    set C0 := max 0 (x a + S - ((j + 1 : ℕ) - 1) * m)
    set D0 := max 0 (S - (j - 1) * m)
    have hstep : C0 ^ (j + 1) ≤ A0 ^ (j + 1) + (j + 1) * x a * D0 ^ j := by
      apply step_ineq (le_max_left _ _) (le_max_left _ _) (hx a)
      · rcases le_total 0 (S - ((j + 1 : ℕ) - 1) * m) with h | h
        · rw [max_eq_right h]; exact max_le (by linarith [hx a]) (by linarith)
        · rw [max_eq_left h]; exact max_le (by linarith [hx a]) (by linarith)
      · simp only [D0]
        exact max_le_max le_rfl (by push_cast; linarith)
    have hfac : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
      push_cast [Nat.factorial_succ]; ring
    calc C0 ^ (j + 1) ≤ A0 ^ (j + 1) + (j + 1) * x a * D0 ^ j := hstep
      _ ≤ ((j + 1).factorial : ℝ) * esum x s (j + 1) + (j + 1) * x a * (j.factorial * esum x s j) := by
          gcongr
          · exact mul_nonneg (by positivity) (hx a)
      _ = _ := by rw [hfac]; ring

/-- **The pool weight is large.**  `e_K(pool) ≥ (∑_{q ∈ pool} 1/q − 2K/Y)₊^K` for a pool above
`Y ≥ 2K`. -/
theorem poolWeight_ge {pool : Finset ℕ} {K Y : ℕ} (hpool : ∀ q ∈ pool, Y < q) (hKY : 2 * K ≤ Y) :
    max 0 (∑ q ∈ pool, (1 : ℝ) / q - 2 * K / Y) ^ K ≤ poolWeight pool K K := by
  classical
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0; simp [poolWeight]
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  set x : ℕ → ℝ := fun q => max 0 ((K : ℝ) / ((q : ℝ) - K)) with hxdef
  have hx0 : ∀ q, 0 ≤ x q := fun q => le_max_left _ _
  have hxq : ∀ q ∈ pool, x q = (K : ℝ) / ((q : ℝ) - K) := by
    intro q hq
    have : (K : ℝ) < q := by exact_mod_cast (show K < q by have := hpool q hq; omega)
    exact max_eq_right (div_nonneg (Nat.cast_nonneg _) (by linarith))
  have hpw : poolWeight pool K K = esum x pool K := by
    unfold poolWeight esum
    refine sum_congr rfl fun T hT => prod_congr rfl fun q hq => (hxq q ((mem_powersetCard.1 hT).1 hq)).symm
  have hm : (0 : ℝ) ≤ 2 * K / Y := by positivity
  have hxm : ∀ q ∈ pool, x q ≤ 2 * K / Y := by
    intro q hq
    rw [hxq q hq]
    have hq' : (Y : ℝ) < q := by exact_mod_cast hpool q hq
    have hKY' : (2 * K : ℝ) ≤ Y := by exact_mod_cast hKY
    rw [div_le_div_iff₀ (by linarith) hYpos]
    nlinarith [show (0:ℝ) ≤ K from Nat.cast_nonneg K]
  have hsum : (K : ℝ) * ∑ q ∈ pool, (1 : ℝ) / q ≤ ∑ q ∈ pool, x q := by
    rw [mul_sum]
    refine sum_le_sum fun q hq => ?_
    rw [hxq q hq]
    have hq' : (Y : ℝ) < q := by exact_mod_cast hpool q hq
    have hKq : (K : ℝ) < q := by
      have : (2 * K : ℝ) ≤ Y := by exact_mod_cast hKY
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith [show (0:ℝ) ≤ K from Nat.cast_nonneg K])
  have hlow := esymm_lower hx0 hm pool hxm K
  rw [hpw]
  set b := max 0 (∑ q ∈ pool, (1 : ℝ) / q - 2 * K / Y)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hKb : (K : ℝ) * b ≤ max 0 (∑ q ∈ pool, x q - (K - 1) * (2 * K / Y)) := by
    rcases le_total 0 (∑ q ∈ pool, (1 : ℝ) / q - 2 * K / Y) with h | h
    · simp only [b, max_eq_right h]
      refine le_max_of_le_right ?_
      have : (K : ℝ) * (2 * K / Y) ≥ (K - 1) * (2 * K / Y) := by nlinarith
      nlinarith
    · simp only [b, max_eq_left h, mul_zero]; exact le_max_left _ _
  have hKfac : (K.factorial : ℝ) ≤ (K : ℝ) ^ K := by exact_mod_cast Nat.factorial_le_pow K
  have hfacpos : (0 : ℝ) < K.factorial := by exact_mod_cast Nat.factorial_pos K
  have h1 : ((K : ℝ) * b) ^ K ≤ K.factorial * esum x pool K :=
    (pow_le_pow_left₀ (by positivity) hKb K).trans hlow
  rw [mul_pow] at h1
  have he0 := esum_nonneg hx0 pool K
  have : (K : ℝ) ^ K * b ^ K ≤ (K : ℝ) ^ K * esum x pool K := by
    calc (K : ℝ) ^ K * b ^ K ≤ K.factorial * esum x pool K := h1
      _ ≤ (K : ℝ) ^ K * esum x pool K := by gcongr
  exact le_of_mul_le_mul_left this (by positivity)

end LeanFormalizations.Erdos385.QuasiPower

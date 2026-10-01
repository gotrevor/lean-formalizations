/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional

/-!
# Erdős #385, phase E4: McDiarmid for the unblocked-position count (step 3, combinatorial core)

For moduli `m i ≥ 2` and a set `T ⊆ [1, y]`, the count `f(x) = #{a ∈ T : x i ≠ a mod m i ∀ i}`
of positions unblocked by the residue vector `x` has mean `|T| ∏ (1 − 1/m i)` and bounded
differences `2 (y / m i + 1)`, so `McDiarmidFinite` bounds its lower tail.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open LeanFormalizations.Literature Finset

/-- At most `y/m + 1` integers in `[1, y]` lie in a fixed class mod `m`. -/
theorem card_filter_mod_eq_le (y m r : ℕ) (_hm : 0 < m) (T : Finset ℕ) (hT : T ⊆ Icc 1 y) :
    ((T.filter fun a => a % m = r).card : ℝ) ≤ (y : ℝ) / m + 1 := by
  have h1 : (T.filter fun a => a % m = r).card ≤ (range (y / m + 1)).card := by
    apply card_le_card_of_injOn (fun a => a / m)
    · intro a ha
      have := (mem_Icc.1 (hT (mem_filter.1 ha).1)).2
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right this)
    · intro a ha b hb hab
      have h1 := (mem_filter.1 ha).2
      have h2 := (mem_filter.1 hb).2
      simp only at hab
      rw [← Nat.div_add_mod a m, ← Nat.div_add_mod b m, hab, h1, h2]
  rw [card_range] at h1
  have h2 : ((y / m : ℕ) : ℝ) ≤ (y : ℝ) / m := Nat.cast_div_le
  have h3 : ((T.filter fun a => a % m = r).card : ℝ) ≤ ((y / m + 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h3
  linarith

/-- The number of residue vectors avoiding a fixed vector `r` coordinatewise. -/
theorem card_avoid {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (r : ∀ i, Fin (m i)) :
    (univ.filter fun x : (∀ i, Fin (m i)) => ∀ i, x i ≠ r i).card = ∏ i, (m i - 1) := by
  have : (univ.filter fun x : (∀ i, Fin (m i)) => ∀ i, x i ≠ r i) =
      Fintype.piFinset fun i => univ.erase (r i) := by
    ext x; simp
  rw [this, Fintype.card_piFinset]
  simp [card_erase_of_mem]

/-- **McDiarmid applied to the unblocked count.** -/
theorem mcd_count (h3 : McDiarmidFinite) {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : ∀ i, 2 ≤ m i) (y : ℕ) (T : Finset ℕ) (hT : T ⊆ Icc 1 y) (t : ℝ) (ht : 0 < t) :
    ((univ.filter fun x : (∀ i, Fin (m i)) =>
        ((T.filter fun a => ∀ i, (x i : ℕ) ≠ a % m i).card : ℝ) ≤
          T.card * ∏ i, (1 - 1 / (m i : ℝ)) - t).card : ℝ) ≤
      (∏ i, (m i : ℝ)) * Real.exp (-2 * t ^ 2 / ∑ i, (2 * ((y : ℝ) / m i + 1)) ^ 2) := by
  haveI : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, by have := hm i; omega⟩⟩
  set f : (∀ i, Fin (m i)) → ℝ := fun x => ((T.filter fun a => ∀ i, (x i : ℕ) ≠ a % m i).card : ℝ)
    with hf
  -- one direction of the bounded difference
  have hone : ∀ x x' : (∀ i, Fin (m i)), ∀ i, (∀ j, j ≠ i → x j = x' j) →
      f x ≤ f x' + ((y : ℝ) / m i + 1) := by
    intro x x' i hxx
    have hsub : (T.filter fun a => ∀ i, (x i : ℕ) ≠ a % m i) ⊆
        (T.filter fun a => ∀ i, (x' i : ℕ) ≠ a % m i) ∪
          (T.filter fun a => a % m i = (x' i : ℕ)) := by
      intro a ha
      rw [mem_filter] at ha
      by_cases h : ∀ j, (x' j : ℕ) ≠ a % m j
      · exact mem_union_left _ (mem_filter.2 ⟨ha.1, h⟩)
      · push Not at h
        obtain ⟨j, hj⟩ := h
        by_cases hji : j = i
        · subst hji; exact mem_union_right _ (mem_filter.2 ⟨ha.1, hj.symm⟩)
        · exact absurd (by rw [hxx j hji]; exact hj) (ha.2 j)
    have := (card_le_card hsub).trans (card_union_le _ _)
    have hc : (((T.filter fun a => ∀ i, (x i : ℕ) ≠ a % m i).card : ℕ) : ℝ) ≤
        ((T.filter fun a => ∀ i, (x' i : ℕ) ≠ a % m i).card : ℝ) +
          ((T.filter fun a => a % m i = (x' i : ℕ)).card : ℝ) := by exact_mod_cast this
    have := card_filter_mod_eq_le y (m i) (x' i) (by have := hm i; omega) T hT
    simp only [hf]; linarith
  have hbd : ∀ x x' : (∀ i, Fin (m i)), ∀ i, (∀ j, j ≠ i → x j = x' j) →
      |f x - f x'| ≤ 2 * ((y : ℝ) / m i + 1) := by
    intro x x' i hxx
    have h1 := hone x x' i hxx
    have h2 := hone x' x i fun j hj => (hxx j hj).symm
    have : (0 : ℝ) ≤ (y : ℝ) / m i + 1 := by positivity
    rw [abs_le]; constructor <;> linarith
  have key := h3 ι (fun i => Fin (m i)) f (fun i => 2 * ((y : ℝ) / m i + 1)) hbd t ht
  -- the mean
  have hcard : (Fintype.card (∀ i, Fin (m i)) : ℝ) = ∏ i, (m i : ℝ) := by
    rw [Fintype.card_pi]; push_cast; simp
  have hsum : ∑ z, f z = T.card * ∏ i, ((m i : ℝ) - 1) := by
    simp only [hf]
    have : ∀ z : (∀ i, Fin (m i)), ((T.filter fun a => ∀ i, (z i : ℕ) ≠ a % m i).card : ℝ) =
        ∑ a ∈ T, if ∀ i, (z i : ℕ) ≠ a % m i then (1 : ℝ) else 0 := by
      intro z; rw [sum_boole]
    simp_rw [this]
    rw [sum_comm]
    have h2 : ∀ a ∈ T, (∑ z : (∀ i, Fin (m i)), if ∀ i, (z i : ℕ) ≠ a % m i then (1 : ℝ) else 0)
        = ∏ i, ((m i : ℝ) - 1) := by
      intro a _
      rw [sum_boole]
      have hr := card_avoid m (fun i => ⟨a % m i, Nat.mod_lt _ (by have := hm i; omega)⟩)
      have : (univ.filter fun z : (∀ i, Fin (m i)) => ∀ i, (z i : ℕ) ≠ a % m i) =
          (univ.filter fun x : (∀ i, Fin (m i)) =>
            ∀ i, x i ≠ ⟨a % m i, Nat.mod_lt _ (by have := hm i; omega)⟩) := by
        ext x; simp [Fin.ext_iff]
      rw [this, hr]; push_cast
      refine prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (by have := hm i; omega)]; simp
    rw [sum_congr rfl h2, sum_const, nsmul_eq_mul]
  have hmean : (∑ z, f z) / Fintype.card (∀ i, Fin (m i)) = T.card * ∏ i, (1 - 1 / (m i : ℝ)) := by
    rw [hsum, hcard, mul_div_assoc, ← prod_div_distrib]
    congr 1; refine prod_congr rfl fun i _ => ?_
    have : (m i : ℝ) ≠ 0 := by have := hm i; positivity
    field_simp
  rw [hmean, hcard] at key
  exact key

end LeanFormalizations.Erdos385.Exceptional

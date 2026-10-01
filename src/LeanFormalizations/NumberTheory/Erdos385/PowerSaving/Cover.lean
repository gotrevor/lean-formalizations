/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Masked

/-!
# Erdős #385 power saving: maximal separated sets cover (phase E9b)

`exists_separated_cover`: every bounded `E ⊆ ℝ` contains a finite `1`-separated set `S` with
`E ⊆ nearSet S 1`.  (Separated sets in `[−R, R]` inject into `ℤ ∩ [⌊−R⌋, ⌊R⌋]` by `⌊·⌋`; take one
of maximal cardinality.)  This is the pointwise half of `NearSetLeaf`.
-/

namespace Erdos385.Parseval

/-- `1`-separated finite sets. -/
def Separated (S : Finset ℝ) : Prop := ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 1 ≤ |s - s'|

lemma separated_card_le {R : ℝ} {S : Finset ℝ} (hS : Separated S)
    (hSR : ∀ s ∈ S, |s| ≤ R) : S.card ≤ (Finset.Icc ⌊-R⌋ ⌊R⌋).card := by
  refine Finset.card_le_card_of_injOn (fun s => ⌊s⌋) (fun s hs => ?_) (fun s hs s' hs' h => ?_)
  · have := abs_le.1 (hSR s hs)
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Int.floor_mono this.1, Int.floor_mono this.2⟩
  · by_contra hne
    have h1 := hS s hs s' hs' hne
    have := Int.abs_sub_lt_one_of_floor_eq_floor h
    linarith

theorem exists_separated_cover {E : Set ℝ} {R : ℝ} (hE : ∀ t ∈ E, |t| ≤ R) :
    ∃ S : Finset ℝ, (↑S : Set ℝ) ⊆ E ∧ Separated S ∧ E ⊆ nearSet S 1 := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, N = (Finset.Icc ⌊-R⌋ ⌊R⌋).card := ⟨_, rfl⟩
  have hex : ∃ n, ∃ S : Finset ℝ, (↑S : Set ℝ) ⊆ E ∧ Separated S ∧ S.card = N - n :=
    ⟨N, ∅, by simp, by simp [Separated], by simp⟩
  have hfN : Nat.find hex ≤ N := Nat.find_min' hex ⟨∅, by simp, by simp [Separated], by simp⟩
  obtain ⟨S, hSE, hSs, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hSE, hSs, fun t ht => ?_⟩
  by_contra hnot
  have hfar : ∀ s ∈ S, 1 < |t - s| := by
    intro s hs
    by_contra h
    push_neg at h
    exact hnot (Set.mem_biUnion hs (by
      rw [Set.mem_Icc]; constructor <;> linarith [(abs_le.1 h).1, (abs_le.1 h).2]))
  have htS : t ∉ S := fun h => by have := hfar t h; rw [sub_self, abs_zero] at this; linarith
  have hS' : Separated (insert t S) := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact (hfar b hb).le
    · rw [abs_sub_comm]; exact (hfar a ha).le
    · exact hSs a ha b hb hab
  have hle := separated_card_le hS' (fun s hs => by
    rw [Finset.mem_insert] at hs
    rcases hs with rfl | hs
    · exact hE _ ht
    · exact hE s (hSE hs))
  rw [Finset.card_insert_of_notMem htS, ← hN] at hle
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hcard; omega
    · exact h
  have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  exact this ⟨insert t S, by
    rw [Finset.coe_insert]; exact Set.insert_subset ht hSE, hS', by
    rw [Finset.card_insert_of_notMem htS]; omega⟩

end Erdos385.Parseval

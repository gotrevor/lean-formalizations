/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Basic
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.McD
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Count
import LeanFormalizations.NumberTheory.Erdos385.ExceptionalWeak.Sieve

/-!
# Erdős #385, phase E4, step 4 (combinatorial half): the three-way split of the bad set

A bad `n ∈ [5, X]` is either small (`n ≤ R + y`), or has few unblocked positions
(`|uSet y (n mod y#)| < K`, counted class by class), or is sieved by `sieve_count` with
`A ⊆ {1} ∪ uSet` of size `K` and the pool of primes in `(y, R]`.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open LeanFormalizations.Literature LeanFormalizations.Erdos385 Finset

open scoped Classical in
theorem bad_count_le_weak {C : ℝ} (h1 : LSWith C) (hC0 : 0 ≤ C) {X y R j K Q : ℕ} (hy : 1 ≤ y)
    (hPR : primorial y * R ^ j ≤ Q)
    (hden : 0 < (∏ p ∈ ps y, ((p : ℝ) - 1)) * ((pool y R).card.choose j : ℝ) * ((K : ℝ) / R) ^ j) :
    (((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ) ≤
      (R + y : ℝ) + (((range (primorial y)).filter fun s => (uSet y s).card < K).card : ℝ) *
        ((X : ℝ) / primorial y + 1) +
      primorial y * (C * (X + (Q : ℝ) ^ 2) /
        ((∏ p ∈ ps y, ((p : ℝ) - 1)) * ((pool y R).card.choose j : ℝ) * ((K : ℝ) / R) ^ j)) := by
  classical
  set P := primorial y with hP
  have hPpos : 0 < P := primorial_pos y
  set den := (∏ p ∈ ps y, ((p : ℝ) - 1)) * ((pool y R).card.choose j : ℝ) * ((K : ℝ) / R) ^ j
  -- choose `A_s`
  have hA : ∀ s, ∃ A : Finset ℕ, A ⊆ Icc 1 y ∧ (K ≤ (uSet y s).card → A.card = K ∧
      A ⊆ insert 1 (uSet y s)) := by
    intro s
    by_cases hK : K ≤ (uSet y s).card
    · obtain ⟨A, hAs, hAc⟩ := exists_subset_card_eq (s := insert 1 (uSet y s)) (n := K)
        (hK.trans (card_le_card (subset_insert _ _)))
      refine ⟨A, fun a ha => ?_, fun _ => ⟨hAc, hAs⟩⟩
      rcases mem_insert.1 (hAs ha) with rfl | h
      · exact mem_Icc.2 ⟨le_rfl, hy⟩
      · exact (mem_filter.1 h).1
    · exact ⟨∅, empty_subset _, fun h => absurd h hK⟩
  choose A hAsub hAK using hA
  set Sset : ℕ → Finset ℕ := fun s => (Icc 1 X).filter fun n => n % P = s % P ∧
    ∀ q ∈ pool y R, n % q ∉ A s
  set small := (Icc 1 X).filter fun n => n ≤ R + y
  set tail := (range P).filter fun s => (uSet y s).card < K
  have hsplit : ((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n) ⊆ small ∪
      (tail.biUnion fun s => (Icc 1 X).filter fun n => n % P = s) ∪
      (((range P).filter fun s => K ≤ (uSet y s).card).biUnion Sset) := by
    intro n hn
    obtain ⟨hnI, hn5, hb⟩ := mem_filter.1 hn
    by_cases hsm : n ≤ R + y
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hnI, hsm⟩))
    have hU := uSet_mod_primorial y n
    by_cases hK : (uSet y (n % P)).card < K
    · refine mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨n % P, ?_, ?_⟩))
      · exact mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ hPpos), hK⟩
      · exact mem_filter.2 ⟨hnI, rfl⟩
    · refine mem_union_right _ (mem_biUnion.2 ⟨n % P,
        mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ hPpos), by omega⟩, ?_⟩)
      refine mem_filter.2 ⟨hnI, (Nat.mod_mod _ _).symm, fun q hq ha => ?_⟩
      obtain ⟨hcard, hsub⟩ := hAK (n % P) (by omega)
      have hqI := mem_filter.1 hq
      have hmem := hsub ha
      rw [hU] at hmem
      have haI := mem_Icc.1 (hAsub (n % P) ha)
      have hqR := (mem_Ioc.1 hqI.1)
      exact mod_ne_of_bad hn5 hb hqI.2 hqR.1 hmem (by omega) rfl
  have h1' : (small.card : ℝ) ≤ R + y := by
    have : small.card ≤ R + y := by
      calc small.card ≤ (Icc 1 (R + y)).card := card_le_card fun n hn => by
            obtain ⟨h1, h2⟩ := mem_filter.1 hn
            exact mem_Icc.2 ⟨(mem_Icc.1 h1).1, h2⟩
        _ = R + y := by simp
    exact_mod_cast this
  have h2' : ((tail.biUnion fun s => (Icc 1 X).filter fun n => n % P = s).card : ℝ) ≤
      tail.card * ((X : ℝ) / P + 1) := by
    calc _ ≤ ((∑ s ∈ tail, ((Icc 1 X).filter fun n => n % P = s).card : ℕ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _s ∈ tail, ((X : ℝ) / P + 1) := by
          push_cast
          exact sum_le_sum fun s _ => card_filter_mod_eq_le X P s hPpos _ subset_rfl
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  set good := (range P).filter fun s => K ≤ (uSet y s).card
  have h3' : ((good.biUnion Sset).card : ℝ) ≤ P * (C * (X + (Q : ℝ) ^ 2) / den) := by
    calc _ ≤ ((∑ s ∈ good, (Sset s).card : ℕ) : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _s ∈ good, (C * (X + (Q : ℝ) ^ 2) / den) := by
          push_cast
          refine sum_le_sum fun s hs => ?_
          have hK : K ≤ (uSet y s).card := (mem_filter.1 hs).2
          · have := sieve_count_weak h1 (X := X) (Q := Q) (R := R) (j := j) s (A s) (pool y R)
              (hAsub s) (fun q hq => by
                have := mem_filter.1 hq; exact ⟨this.2, (mem_Ioc.1 this.1).1, (mem_Ioc.1 this.1).2⟩)
              hPR
            rw [(hAK s hK).1] at this
            rw [le_div_iff₀ hden]
            exact this
      _ ≤ _ := by
          rw [sum_const, nsmul_eq_mul]
          have : (good.card : ℝ) ≤ P := by
            exact_mod_cast (card_filter_le _ _).trans (card_range P).le
          have : 0 ≤ C * (X + (Q : ℝ) ^ 2) / den := by
            have : (0:ℝ) ≤ C * (X + (Q : ℝ) ^ 2) := by positivity
            positivity
          gcongr
  calc (((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ)
      ≤ ((small ∪ (tail.biUnion fun s => (Icc 1 X).filter fun n => n % P = s) ∪
          (good.biUnion Sset)).card : ℝ) := by exact_mod_cast card_le_card hsplit
    _ ≤ (small.card : ℝ) + (tail.biUnion fun s => (Icc 1 X).filter fun n => n % P = s).card +
          (good.biUnion Sset).card := by
        have h := card_union_le (small ∪ (tail.biUnion fun s => (Icc 1 X).filter fun n => n % P = s))
          (good.biUnion Sset)
        have h' := card_union_le small (tail.biUnion fun s => (Icc 1 X).filter fun n => n % P = s)
        have : ((small ∪ (tail.biUnion fun s => (Icc 1 X).filter fun n => n % P = s) ∪
            (good.biUnion Sset)).card : ℝ) ≤ ((small.card + (tail.biUnion fun s =>
              (Icc 1 X).filter fun n => n % P = s).card + (good.biUnion Sset).card : ℕ) : ℝ) := by
          exact_mod_cast h.trans (by omega)
        push_cast at this
        exact this
    _ ≤ _ := by linarith

end LeanFormalizations.Erdos385.Exceptional

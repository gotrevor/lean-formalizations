/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Sieve
import LeanFormalizations.Literature.Erdos385LargeSieveWeak

/-!
# Erdős #385, phase E4d: the large-sieve count with a constant

Integers `n ≤ X` in a fixed class mod `y#` that avoid a set `A ⊆ [1, y]` of `K` classes mod every
prime of a pool `⊆ (y, R]` number at most `(X + Q²) / L`, where (keeping only the moduli
`d = y# · q₁⋯q_j`, `qᵢ` distinct pool primes, `y# R^j ≤ Q`)
`L ≥ ∏_{p ≤ y} (p − 1) · C(|pool|, j) · (K/R)^j`.  The classes mod `p ≤ y` enter the large sieve
with `ω(p) = p − 1` (all but one class excluded).
-/

namespace LeanFormalizations.Erdos385.Exceptional

open LeanFormalizations.Literature Finset

/-- The arithmetic large sieve with constant `C`. -/
def LSWith (C : ℝ) : Prop :=
  ∀ (M N Q : ℕ) (Ω : ℕ → Finset ℕ) (S : Finset ℕ),
    (∀ p, p.Prime → p ≤ Q → Ω p ⊆ Finset.range p ∧ (Ω p).card < p) →
    (∀ n ∈ S, M < n ∧ n ≤ M + N ∧ ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p) →
    (S.card : ℝ) * (∑ q ∈ (Finset.Icc 1 Q).filter Squarefree,
        ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)) ≤ C * (N + (Q : ℝ) ^ 2)

theorem exists_lsWith (h : ArithLargeSieveWeak) : ∃ C, 1 ≤ C ∧ LSWith C := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 1, le_max_right _ _, fun M N Q Ω S hΩ hS => (hC M N Q Ω S hΩ hS).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Step 2: the large-sieve count.** -/
theorem sieve_count_weak {C : ℝ} (h1 : LSWith C) {X y Q R j : ℕ} (s : ℕ) (A pool : Finset ℕ)
    (hA : A ⊆ Icc 1 y) (hpool : ∀ q ∈ pool, q.Prime ∧ y < q ∧ q ≤ R)
    (hPR : primorial y * R ^ j ≤ Q) :
    (((Icc 1 X).filter fun n => n % primorial y = s % primorial y ∧
        ∀ q ∈ pool, n % q ∉ A).card : ℝ) *
      ((∏ p ∈ ps y, ((p : ℝ) - 1)) * (pool.card.choose j : ℝ) * ((A.card : ℝ) / R) ^ j) ≤
      C * (X + (Q : ℝ) ^ 2) := by
  classical
  set Ω : ℕ → Finset ℕ := fun p =>
    if p ∈ ps y then (range p).erase (s % p) else if p ∈ pool then A else ∅ with hΩ
  set S := (Icc 1 X).filter fun n => n % primorial y = s % primorial y ∧ ∀ q ∈ pool, n % q ∉ A
  have hAcard : A.card ≤ y := by simpa using card_le_card hA
  have hΩp : ∀ p, p.Prime → p ≤ Q → Ω p ⊆ range p ∧ (Ω p).card < p := by
    intro p hp _
    simp only [hΩ]
    split_ifs with h1 h2
    · exact ⟨erase_subset _ _, by rw [card_erase_of_mem (by simp [Nat.mod_lt _ hp.pos])]; simp [hp.pos]⟩
    · have hyp := (hpool p h2).2.1
      refine ⟨fun a ha => mem_range.2 (by have := (mem_Icc.1 (hA ha)).2; omega), by omega⟩
    · exact ⟨empty_subset _, by simp [hp.pos]⟩
  have hS : ∀ n ∈ S, 0 < n ∧ n ≤ 0 + X ∧ ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p := by
    intro n hn
    obtain ⟨hnI, hns, hnq⟩ := mem_filter.1 hn
    refine ⟨by have := (mem_Icc.1 hnI).1; omega, by have := (mem_Icc.1 hnI).2; omega,
      fun p hp _ => ?_⟩
    simp only [hΩ]
    split_ifs with h1 h2
    · have hd : p ∣ primorial y := Finset.dvd_prod_of_mem _ h1
      have : n % p = s % p := by
        rw [← Nat.mod_mod_of_dvd n hd, hns, Nat.mod_mod_of_dvd s hd]
      rw [this]; exact Finset.notMem_erase _ _
    · exact hnq p h2
    · simp
  have key := h1 0 X Q Ω S hΩp hS
  -- lower bound for the sieve weight `L`
  set term : ℕ → ℝ := fun q => ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)
  have hterm_nn : ∀ q ∈ (Icc 1 Q).filter Squarefree, 0 ≤ term q := by
    intro q hq
    refine prod_nonneg fun p hp => ?_
    have hpq : p ≤ Q := (Nat.le_of_mem_primeFactors hp).trans (mem_Icc.1 (mem_filter.1 hq).1).2
    have := (hΩp p (Nat.prime_of_mem_primeFactors hp) hpq).2
    have : ((Ω p).card : ℝ) < p := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  set D : Finset ℕ → ℕ := fun T => ∏ p ∈ ps y ∪ T, p
  have hdisj : ∀ T ∈ pool.powersetCard j, Disjoint (ps y) T := by
    intro T hT
    rw [disjoint_left]
    intro p hp hpT
    have := (hpool p ((mem_powersetCard.1 hT).1 hpT)).2.1
    have := mem_range.1 (mem_filter.1 hp).1
    omega
  have hprimes : ∀ T ∈ pool.powersetCard j, ∀ p ∈ ps y ∪ T, p.Prime := by
    intro T hT p hp
    rcases mem_union.1 hp with h | h
    · exact (mem_filter.1 h).2
    · exact (hpool p ((mem_powersetCard.1 hT).1 h)).1
  have hDinj : Set.InjOn D (pool.powersetCard j) := by
    intro T hT T' hT' hTT
    have h1 := Nat.primeFactors_prod (hprimes T hT)
    have h2 := Nat.primeFactors_prod (hprimes T' hT')
    have : ps y ∪ T = ps y ∪ T' := by rw [← h1, ← h2]; exact congrArg Nat.primeFactors hTT
    ext p
    constructor
    · intro hp
      have : p ∈ ps y ∪ T' := this ▸ mem_union_right _ hp
      rcases mem_union.1 this with h | h
      · exact absurd hp (disjoint_left.1 (hdisj T hT) h)
      · exact h
    · intro hp
      have : p ∈ ps y ∪ T := this.symm ▸ mem_union_right _ hp
      rcases mem_union.1 this with h | h
      · exact absurd hp (disjoint_left.1 (hdisj T' hT') h)
      · exact h
  have hDmem : ∀ T ∈ pool.powersetCard j, D T ∈ (Icc 1 Q).filter Squarefree := by
    intro T hT
    refine mem_filter.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, squarefree_prod_primes (hprimes T hT)⟩
    · exact Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => (hprimes T hT p hp).ne_zero)
    · refine le_trans ?_ hPR
      simp only [D]
      rw [prod_union (hdisj T hT), ← primorial_eq_prod_ps]
      apply Nat.mul_le_mul_left
      have hc := (mem_powersetCard.1 hT).2
      calc ∏ p ∈ T, p ≤ ∏ _p ∈ T, R := prod_le_prod' fun p hp =>
            (hpool p ((mem_powersetCard.1 hT).1 hp)).2.2
        _ = R ^ j := by rw [prod_const, hc]
  set lower : ℝ := (∏ p ∈ ps y, ((p : ℝ) - 1)) * ((A.card : ℝ) / R) ^ j
  have hDterm : ∀ T ∈ pool.powersetCard j, lower ≤ term (D T) := by
    intro T hT
    simp only [term, D]
    rw [Nat.primeFactors_prod (hprimes T hT), prod_union (hdisj T hT)]
    have hnn : 0 ≤ ∏ p ∈ ps y, ((p : ℝ) - 1) := by
      refine prod_nonneg fun p hp => ?_
      have : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.one_lt.le
      linarith
    have hfirst : ∏ p ∈ ps y, ((p : ℝ) - 1) ≤ ∏ p ∈ ps y, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card) := by
      apply le_of_eq
      refine prod_congr rfl fun p hp => ?_
      have hp' := (mem_filter.1 hp).2
      simp only [hΩ]
      rw [if_pos hp, card_erase_of_mem (by simp [Nat.mod_lt _ hp'.pos]), card_range]
      have : (1 : ℕ) ≤ p := hp'.one_lt.le
      push_cast [this]
      ring_nf
    refine mul_le_mul hfirst ?_ ?_ (le_trans hnn hfirst)
    · have hc := (mem_powersetCard.1 hT).2
      rw [← hc, ← prod_const]
      refine prod_le_prod (fun _ _ => by positivity) fun q hq => ?_
      obtain ⟨hqp, hyq, hqR⟩ := hpool q ((mem_powersetCard.1 hT).1 hq)
      have hqps : q ∉ ps y := by
        intro h; have := mem_range.1 (mem_filter.1 h).1; omega
      have hqpool : q ∈ pool := (mem_powersetCard.1 hT).1 hq
      simp only [hΩ, if_neg hqps, if_pos hqpool]
      have hKq : (A.card : ℝ) < q := by exact_mod_cast (show A.card < q by omega)
      have hR : (q : ℝ) ≤ R := by exact_mod_cast hqR
      have hK0 : (0 : ℝ) ≤ A.card := by positivity
      apply div_le_div₀ hK0 le_rfl (by linarith) (by linarith)
    · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  have hL : (pool.card.choose j : ℝ) * lower ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, term q := by
    calc (pool.card.choose j : ℝ) * lower = ∑ _T ∈ pool.powersetCard j, lower := by
          rw [sum_const, card_powersetCard, nsmul_eq_mul]
      _ ≤ ∑ T ∈ pool.powersetCard j, term (D T) := sum_le_sum hDterm
      _ = ∑ q ∈ (pool.powersetCard j).image D, term q := (sum_image hDinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun q hq => by
            obtain ⟨T, hT, rfl⟩ := mem_image.1 hq; exact hDmem T hT)
          fun q hq _ => hterm_nn q hq
  calc (S.card : ℝ) * ((∏ p ∈ ps y, ((p : ℝ) - 1)) * (pool.card.choose j : ℝ) *
        ((A.card : ℝ) / R) ^ j) = S.card * ((pool.card.choose j : ℝ) * lower) := by
        simp only [lower]; ring
    _ ≤ S.card * ∑ q ∈ (Icc 1 Q).filter Squarefree, term q := by gcongr
    _ ≤ _ := key

end LeanFormalizations.Erdos385.Exceptional

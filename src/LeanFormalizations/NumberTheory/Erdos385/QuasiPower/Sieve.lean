/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.ExceptionalWeak.Sieve

/-!
# Erdős #385, phase E8: the large-sieve count with an arbitrary set of fixed residues

Integers `n ≤ X` lying in one fixed class mod every prime of a finite set `E`, and avoiding a set
`A` of `K` classes mod every prime of a pool disjoint from `E`, number at most `C (X + Q²) / L`
with `L ≥ ∏_{p ∈ E} (p − 1) · e_j` where `e_j = ∑_{T ⊆ pool, |T| = j} ∏_{q ∈ T} K/(q − K)`
(keeping the moduli `∏ E · ∏ T`, `∏ E · R^j ≤ Q`).  Generalizes `Exceptional.sieve_count_weak`
(`E = ps y`) and keeps the full weight `e_j` instead of `C(|pool|, j)(K/R)^j`.
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open LeanFormalizations.Erdos385.Exceptional Finset

/-- The `j`-th elementary symmetric weight of a pool with `K` classes per prime. -/
noncomputable def poolWeight (pool : Finset ℕ) (K j : ℕ) : ℝ :=
  ∑ T ∈ pool.powersetCard j, ∏ q ∈ T, (K : ℝ) / ((q : ℝ) - K)

theorem sieve_count_gen {C : ℝ} (h1 : LSWith C) {X Q R j : ℕ} (E : Finset ℕ) (c : ℕ → ℕ)
    (A pool : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (hpool : ∀ q ∈ pool, q.Prime ∧ q ∉ E ∧ q ≤ R) (hA : ∀ q ∈ pool, ∀ a ∈ A, 1 ≤ a ∧ a < q)
    (hQ : (∏ p ∈ E, p) * R ^ j ≤ Q) :
    (((Icc 1 X).filter fun n => (∀ p ∈ E, n % p = c p % p) ∧ ∀ q ∈ pool, n % q ∉ A).card : ℝ) *
      ((∏ p ∈ E, ((p : ℝ) - 1)) * poolWeight pool A.card j) ≤ C * (X + (Q : ℝ) ^ 2) := by
  classical
  set Ω : ℕ → Finset ℕ := fun p =>
    if p ∈ E then (range p).erase (c p % p) else if p ∈ pool then A else ∅ with hΩ
  set S := (Icc 1 X).filter fun n => (∀ p ∈ E, n % p = c p % p) ∧ ∀ q ∈ pool, n % q ∉ A
  have hAq : ∀ q ∈ pool, A.card < q := by
    intro q hq
    have hsub : A ⊆ Ico 1 q := fun a ha => mem_Ico.2 (hA q hq a ha)
    have := card_le_card hsub
    simp only [Nat.card_Ico] at this
    have := (hpool q hq).1.one_lt
    omega
  have hΩp : ∀ p, p.Prime → p ≤ Q → Ω p ⊆ range p ∧ (Ω p).card < p := by
    intro p hp _
    simp only [hΩ]
    split_ifs with h1 h2
    · exact ⟨erase_subset _ _, by rw [card_erase_of_mem (by simp [Nat.mod_lt _ hp.pos])]; simp [hp.pos]⟩
    · exact ⟨fun a ha => mem_range.2 (hA p h2 a ha).2, hAq p h2⟩
    · exact ⟨empty_subset _, by simp [hp.pos]⟩
  have hS : ∀ n ∈ S, 0 < n ∧ n ≤ 0 + X ∧ ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p := by
    intro n hn
    obtain ⟨hnI, hnE, hnq⟩ := mem_filter.1 hn
    refine ⟨by have := (mem_Icc.1 hnI).1; omega, by have := (mem_Icc.1 hnI).2; omega,
      fun p hp _ => ?_⟩
    simp only [hΩ]
    split_ifs with h1 h2
    · rw [hnE p h1]; exact Finset.notMem_erase _ _
    · exact hnq p h2
    · simp
  have key := h1 0 X Q Ω S hΩp hS
  set term : ℕ → ℝ := fun q => ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)
  have hterm_nn : ∀ q ∈ (Icc 1 Q).filter Squarefree, 0 ≤ term q := by
    intro q hq
    refine prod_nonneg fun p hp => ?_
    have hpq : p ≤ Q := (Nat.le_of_mem_primeFactors hp).trans (mem_Icc.1 (mem_filter.1 hq).1).2
    have := (hΩp p (Nat.prime_of_mem_primeFactors hp) hpq).2
    have : ((Ω p).card : ℝ) < p := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  set D : Finset ℕ → ℕ := fun T => ∏ p ∈ E ∪ T, p
  have hdisj : ∀ T ∈ pool.powersetCard j, Disjoint E T := by
    intro T hT
    rw [disjoint_left]
    intro p hp hpT
    exact (hpool p ((mem_powersetCard.1 hT).1 hpT)).2.1 hp
  have hprimes : ∀ T ∈ pool.powersetCard j, ∀ p ∈ E ∪ T, p.Prime := by
    intro T hT p hp
    rcases mem_union.1 hp with h | h
    · exact hE p h
    · exact (hpool p ((mem_powersetCard.1 hT).1 h)).1
  have hDinj : Set.InjOn D (pool.powersetCard j) := by
    intro T hT T' hT' hTT
    have h1 := Nat.primeFactors_prod (hprimes T hT)
    have h2 := Nat.primeFactors_prod (hprimes T' hT')
    have : E ∪ T = E ∪ T' := by rw [← h1, ← h2]; exact congrArg Nat.primeFactors hTT
    ext p
    constructor
    · intro hp
      have : p ∈ E ∪ T' := this ▸ mem_union_right _ hp
      rcases mem_union.1 this with h | h
      · exact absurd hp (disjoint_left.1 (hdisj T hT) h)
      · exact h
    · intro hp
      have : p ∈ E ∪ T := this.symm ▸ mem_union_right _ hp
      rcases mem_union.1 this with h | h
      · exact absurd hp (disjoint_left.1 (hdisj T' hT') h)
      · exact h
  have hDmem : ∀ T ∈ pool.powersetCard j, D T ∈ (Icc 1 Q).filter Squarefree := by
    intro T hT
    refine mem_filter.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, squarefree_prod_primes (hprimes T hT)⟩
    · exact Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => (hprimes T hT p hp).ne_zero)
    · refine le_trans ?_ hQ
      simp only [D]
      rw [prod_union (hdisj T hT)]
      apply Nat.mul_le_mul_left
      have hc := (mem_powersetCard.1 hT).2
      calc ∏ p ∈ T, p ≤ ∏ _p ∈ T, R := prod_le_prod' fun p hp =>
            (hpool p ((mem_powersetCard.1 hT).1 hp)).2.2
        _ = R ^ j := by rw [prod_const, hc]
  have hEterm : ∏ p ∈ E, ((p : ℝ) - 1) =
      ∏ p ∈ E, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card) := by
    refine prod_congr rfl fun p hp => ?_
    have hp' := hE p hp
    simp only [hΩ]
    rw [if_pos hp, card_erase_of_mem (by simp [Nat.mod_lt _ hp'.pos]), card_range]
    have : (1 : ℕ) ≤ p := hp'.one_lt.le
    push_cast [this]
    ring_nf
  have hDterm : ∀ T ∈ pool.powersetCard j,
      (∏ p ∈ E, ((p : ℝ) - 1)) * ∏ q ∈ T, (A.card : ℝ) / ((q : ℝ) - A.card) = term (D T) := by
    intro T hT
    simp only [term, D]
    rw [Nat.primeFactors_prod (hprimes T hT), prod_union (hdisj T hT), hEterm]
    congr 1
    refine prod_congr rfl fun q hq => ?_
    have hqpool : q ∈ pool := (mem_powersetCard.1 hT).1 hq
    have hqE : q ∉ E := (hpool q hqpool).2.1
    simp only [hΩ, if_neg hqE, if_pos hqpool]
  have hL : (∏ p ∈ E, ((p : ℝ) - 1)) * poolWeight pool A.card j ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, term q := by
    calc (∏ p ∈ E, ((p : ℝ) - 1)) * poolWeight pool A.card j
        = ∑ T ∈ pool.powersetCard j, term (D T) := by
          rw [poolWeight, mul_sum]; exact sum_congr rfl hDterm
      _ = ∑ q ∈ (pool.powersetCard j).image D, term q := (sum_image hDinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun q hq => by
            obtain ⟨T, hT, rfl⟩ := mem_image.1 hq; exact hDmem T hT)
          fun q hq _ => hterm_nn q hq
  calc (S.card : ℝ) * ((∏ p ∈ E, ((p : ℝ) - 1)) * poolWeight pool A.card j)
      ≤ S.card * ∑ q ∈ (Icc 1 Q).filter Squarefree, term q := by gcongr
    _ ≤ _ := key

end LeanFormalizations.Erdos385.QuasiPower

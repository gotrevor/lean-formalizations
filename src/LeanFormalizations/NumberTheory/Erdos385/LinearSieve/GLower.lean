/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Selberg

/-!
# `G(ξ) ≥ log ξ` for `ξ < z` (phase E5, step 1b)

`sum_inv_le_prod`: a finite set of positive integers with all prime factors in `T` has
`Σ 1/m ≤ ∏_{p ∈ T} p/(p−1)` (induction on `T`, splitting off the `p`-part).  Grouping `n ≤ ξ` by
its radical `d` then gives `Σ_{n ≤ ξ} 1/n ≤ Σ_{d ∈ L} ∏_{p ∣ d} 1/(p−1) = G`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset

lemma geom_inv_le {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∑ v ∈ range n, (1 / (p : ℝ)) ^ v ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hx0 : 0 ≤ 1 / (p : ℝ) := by positivity
  rw [geom_sum_eq hx1.ne]
  have : (p : ℝ) / ((p : ℝ) - 1) = 1 / (1 - 1 / p) := by field_simp
  rw [this, show ((1 / (p : ℝ)) ^ n - 1) / (1 / p - 1) = (1 - (1 / (p : ℝ)) ^ n) / (1 - 1 / p) by
      rw [← neg_div_neg_eq]; ring_nf]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have := pow_nonneg hx0 n
  linarith

theorem sum_inv_le_prod (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ≠ 0 ∧ m.primeFactors ⊆ T) :
    ∑ m ∈ S, 1 / (m : ℝ) ≤ ∏ p ∈ T, (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  induction T using Finset.induction_on generalizing S with
  | empty =>
    simp only [prod_empty]
    have : S ⊆ {1} := by
      intro m hm
      obtain ⟨h0, h1⟩ := hS m hm
      simp only [subset_empty, Nat.primeFactors_eq_empty] at h1
      simp; omega
    calc ∑ m ∈ S, 1 / (m : ℝ) ≤ ∑ m ∈ ({1} : Finset ℕ), 1 / (m : ℝ) :=
          sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | insert p T hpT ih =>
    have hp : p.Prime := hT p (mem_insert_self _ _)
    have hT' : ∀ q ∈ T, q.Prime := fun q hq => hT q (mem_insert_of_mem hq)
    set φ : ℕ → ℕ × ℕ := fun m => (m.factorization p, m / p ^ m.factorization p)
    set V := S.sup (fun m => m.factorization p)
    set S' := S.image (fun m => m / p ^ m.factorization p)
    have hφinj : Set.InjOn φ S := by
      intro a ha b hb hab
      simp only [φ, Prod.mk.injEq] at hab
      calc a = p ^ a.factorization p * (a / p ^ a.factorization p) :=
            (Nat.ordProj_mul_ordCompl_eq_self a p).symm
        _ = p ^ b.factorization p * (b / p ^ b.factorization p) := by rw [hab.2, hab.1]
        _ = b := Nat.ordProj_mul_ordCompl_eq_self b p
    have hS' : ∀ m ∈ S', m ≠ 0 ∧ m.primeFactors ⊆ T := by
      intro m hm
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hm
      obtain ⟨h0, h1⟩ := hS a ha
      refine ⟨(Nat.ordCompl_pos p h0).ne', fun q hq => ?_⟩
      have hq' := Nat.primeFactors_mono (Nat.ordCompl_dvd a p) h0 hq
      have hqp : q ≠ p := by
        rintro rfl
        exact Nat.not_dvd_ordCompl hp h0 (Nat.dvd_of_mem_primeFactors hq)
      rcases mem_insert.mp (h1 hq') with h | h
      · exact absurd h hqp
      · exact h
    calc ∑ m ∈ S, 1 / (m : ℝ)
        = ∑ x ∈ S.image φ, (1 / (p : ℝ)) ^ x.1 * (1 / (x.2 : ℝ)) := by
          rw [sum_image hφinj]
          refine sum_congr rfl fun m hm => ?_
          have h0 := (hS m hm).1
          conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
          push_cast
          rw [one_div_pow, ← one_div_mul_one_div]
      _ ≤ ∑ x ∈ range (V + 1) ×ˢ S', (1 / (p : ℝ)) ^ x.1 * (1 / (x.2 : ℝ)) := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro x hx
          obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
          simp only [mem_product, mem_range]
          exact ⟨Nat.lt_succ_of_le (le_sup (f := fun m => m.factorization p) hm),
            mem_image_of_mem _ hm⟩
      _ = (∑ v ∈ range (V + 1), (1 / (p : ℝ)) ^ v) * ∑ m ∈ S', 1 / (m : ℝ) := by
          rw [sum_mul_sum, sum_product]
      _ ≤ (p : ℝ) / ((p : ℝ) - 1) * ∏ q ∈ T, (q : ℝ) / ((q : ℝ) - 1) := by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          apply mul_le_mul (geom_inv_le hp _) (ih hT' S' hS')
            (sum_nonneg fun _ _ => by positivity) (div_nonneg (by positivity) (by linarith))
      _ = ∏ q ∈ insert p T, (q : ℝ) / ((q : ℝ) - 1) := by rw [prod_insert hpT]

/-- **`G(ξ) ≥ log ξ`** when every `d ≤ ξ` is a level divisor (`ξ < z`). -/
theorem log_le_selG {z ξ : ℕ} (hξz : ξ < z) : Real.log ξ ≤ selG z ξ := by
  classical
  have hH : Real.log ξ ≤ ∑ n ∈ Icc 1 ξ, 1 / (n : ℝ) := by
    have := log_le_harmonic_floor (ξ : ℝ) (Nat.cast_nonneg ξ)
    rw [Nat.floor_natCast, harmonic_eq_sum_Icc] at this
    simpa using this
  refine hH.trans ?_
  set rad : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors, p
  have hradpf : ∀ n, (rad n).primeFactors = n.primeFactors := fun n =>
    Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp
  have hmaps : ∀ n ∈ Icc 1 ξ, rad n ∈ levelL z ξ := by
    intro n hn
    obtain ⟨h1, hn⟩ := mem_Icc.mp hn
    simp only [levelL, mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, (primorial_pos _).ne'⟩, (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)).trans hn⟩
    unfold primorial
    refine prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
    simp only [mem_filter, mem_range]
    have := Nat.le_of_mem_primeFactors hp
    exact ⟨by omega, Nat.prime_of_mem_primeFactors hp⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  unfold selG
  refine sum_le_sum fun d hd => ?_
  have hdvd : d ∣ primorial (z - 1) := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
  have hsq : Squarefree d := (Erdos385.Brun.squarefree_primorial _).squarefree_of_dvd hdvd
  have hd0 : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  have hdeq : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  set F := (Icc 1 ξ).filter (fun n => rad n = d)
  have hfib : ∀ n ∈ F, d ∣ n ∧ n ≠ 0 ∧ n.primeFactors = d.primeFactors := by
    intro n hn
    obtain ⟨hn1, hr⟩ := mem_filter.mp hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn1).1; omega
    refine ⟨hr ▸ Nat.prod_primeFactors_dvd n, hn0, ?_⟩
    rw [← hr, hradpf]
  have hinj : Set.InjOn (fun n => n / d) (F : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    rw [← Nat.mul_div_cancel' (hfib a ha).1, ← Nat.mul_div_cancel' (hfib b hb).1, hab]
  have hS : ∀ m ∈ F.image (fun n => n / d), m ≠ 0 ∧ m.primeFactors ⊆ d.primeFactors := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨h1, h2, h3⟩ := hfib n hn
    refine ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1) hd0).ne', ?_⟩
    rw [← h3]; exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd h1) h2
  have key := sum_inv_le_prod d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) _ hS
  rw [sum_image hinj] at key
  calc ∑ n ∈ F, 1 / (n : ℝ) = (1 / d) * ∑ n ∈ F, 1 / ((n / d : ℕ) : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun n hn => ?_
        obtain ⟨h1, h2, _⟩ := hfib n hn
        conv_lhs => rw [← Nat.mul_div_cancel' h1]
        push_cast; rw [one_div_mul_one_div]
    _ ≤ (1 / d) * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1) := by
        rw [hdeq, one_div, ← prod_inv_distrib, ← prod_mul_distrib]
        refine prod_congr rfl fun p hp => ?_
        have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        field_simp

end LeanFormalizations.Erdos385.LinearSieve

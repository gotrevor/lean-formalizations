/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Buchstab

/-!
# Rough numbers `Φ(N, z) = #{1 ≤ k ≤ N : p ∣ k ⇒ p ≥ z}` (phase E5, input to `omega_le`)

`Φ` is the sieve problem `lo = 1`, `r ≡ 0`, so `Φ ≤ S⁺`.  Its Buchstab identity is *forward*
(all terms nonnegative and of the same shape): `Φ(N, w) = Φ(N, z) + Σ_{w ≤ p < z} Φ(⌊N/p⌋, p)`,
and `Φ(N, z) ≥ π(N) − π(z − 1)` (primes `≥ z` survive).
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset

/-- The rough-number count. -/
noncomputable def rough (N z : ℕ) : ℕ := sift 1 N (fun _ => 0) z

lemma rough_le_siftMax (N z : ℕ) : rough N z ≤ siftMax N z := le_siftMax _ _ _ _

lemma survives_zero_iff (z : ℕ) (k : ℤ) :
    Survives (fun _ => 0) z k ↔ ∀ q, q.Prime → q < z → ¬ (q : ℤ) ∣ k := by
  simp [Survives]

/-- `S(A_p, p) = Φ(⌊N/p⌋, p)` for the rough problem. -/
lemma hit_rough (N : ℕ) {p : ℕ} (hp : p.Prime) : hit 1 N (fun _ => 0) p = rough (N / p) p := by
  classical
  unfold hit rough sift
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  symm
  refine card_bij (fun m _ => (p : ℤ) * m) ?_ ?_ ?_
  · intro m hm
    simp only [mem_filter, mem_Ico] at hm ⊢
    obtain ⟨⟨h1, h2⟩, hs⟩ := hm
    have hNp : ((N / p : ℕ) : ℤ) * p ≤ N := by exact_mod_cast Nat.div_mul_le_self N p
    refine ⟨⟨by nlinarith, by nlinarith⟩, ?_, by simp⟩
    rw [survives_zero_iff] at hs ⊢
    intro q hq hqp hdiv
    rcases (Int.Prime.dvd_mul' hq hdiv) with h | h
    · have : q ∣ p := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hq hp).mp this; omega
    · exact hs q hq hqp h
  · intro m1 _ m2 _ h
    exact mul_left_cancel₀ hp0.ne' h
  · intro k hk
    simp only [mem_filter, mem_Ico] at hk
    obtain ⟨⟨h1, h2⟩, hs, hdiv⟩ := hk
    simp only [sub_zero] at hdiv
    obtain ⟨m, rfl⟩ := hdiv
    refine ⟨m, ?_, rfl⟩
    simp only [mem_filter, mem_Ico]
    have hm1 : 1 ≤ m := by
      by_contra h; push Not at h; nlinarith
    have hmN : m * p ≤ N := by nlinarith
    have hmN' : m ≤ ((N / p : ℕ) : ℤ) := by
      have hm0 : 0 ≤ m := by linarith
      lift m to ℕ using hm0
      have : m * p ≤ N := by exact_mod_cast hmN
      exact_mod_cast (Nat.le_div_iff_mul_le hp.pos).mpr this
    refine ⟨⟨hm1, by linarith⟩, ?_⟩
    rw [survives_zero_iff] at hs ⊢
    intro q hq hqp hd
    exact hs q hq hqp (Dvd.dvd.mul_left hd _)

/-- **Forward Buchstab identity** for rough numbers. -/
theorem rough_buchstab (N : ℕ) {w z : ℕ} (hwz : w ≤ z) :
    rough N w = rough N z + ∑ p ∈ (Ico w z).filter Nat.Prime, rough (N / p) p := by
  unfold rough
  rw [sift_buchstab 1 N _ hwz]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  exact hit_rough N (mem_filter.mp hp).2

/-- Primes in `[z, N]` survive. -/
theorem primes_le_rough (N z : ℕ) :
    ((Icc z N).filter Nat.Prime).card ≤ rough N z := by
  classical
  unfold rough sift
  refine card_le_card_of_injOn (fun p => (p : ℤ)) ?_ (fun a _ b _ h => by simpa using h)
  intro p hp
  simp only [coe_filter, Set.mem_setOf_eq, mem_Icc] at hp
  simp only [coe_filter, mem_Ico, Set.mem_setOf_eq]
  obtain ⟨⟨hzp, hpN⟩, hpp⟩ := hp
  refine ⟨⟨by exact_mod_cast hpp.one_lt.le, by omega⟩, ?_⟩
  rw [survives_zero_iff]
  intro q hq hqz hd
  have : q ∣ p := by exact_mod_cast hd
  have := (Nat.prime_dvd_prime_iff_eq hq hpp).mp this
  omega

end LeanFormalizations.Erdos385.LinearSieve

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Rigidity

/-!
# Erdős #385, phase E4: the unblocked positions `U(s)` and the forbidden classes (step 1)

`uSet y n` is the set of `a ∈ [1, y]` with `n ≢ a (mod p)` for every prime `p ≤ y`; it depends
only on `n mod y#`.  For bad `n`, each prime `q ∈ (y, n − a)` and each `a ∈ {1} ∪ uSet y n` give
`n ≢ a (mod q)`: otherwise `n − a` is composite with no prime factor `≤ a`.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open LeanFormalizations.Erdos385

/-- Positions `a ∈ [1, y]` not blocked by any prime `p ≤ y`. -/
def uSet (y n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun a => ∀ p ∈ (Finset.Iic y).filter Nat.Prime, n % p ≠ a % p

theorem uSet_mod_primorial (y n : ℕ) : uSet y (n % primorial y) = uSet y n := by
  unfold uSet
  congr 1
  ext a
  refine forall₂_congr fun p hp => ?_
  have hp' := Finset.mem_filter.1 hp
  have hdvd : p ∣ primorial y := by
    apply Finset.dvd_prod_of_mem
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := Finset.mem_Iic.1 hp'.1; omega, hp'.2⟩
  rw [Nat.mod_mod_of_dvd _ hdvd]

/-- **Step 1: forbidden classes.** -/
theorem mod_ne_of_bad {y n q a : ℕ} (hn : 5 ≤ n) (hb : Bad n) (hq : q.Prime) (hyq : y < q)
    (ha : a ∈ insert 1 (uSet y n)) (hlt : q + a < n) : n % q ≠ a := by
  intro hmod
  have ha1 : 1 ≤ a := by
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact le_rfl
    · exact (Finset.mem_Icc.1 (Finset.mem_filter.1 h).1).1
  have haq : a < q := by
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hq.one_lt
    · have := (Finset.mem_Icc.1 (Finset.mem_filter.1 h).1).2; omega
  have hdvd : q ∣ n - a := by
    have := Nat.div_add_mod n q
    refine ⟨n / q, ?_⟩
    omega
  have hcomp : Composite (n - a) := by
    refine ⟨by omega, fun hpr => ?_⟩
    rcases (Nat.dvd_prime hpr).1 hdvd with h | h
    · exact hq.one_lt.ne' h
    · omega
  have hmin := (bad_iff_forall_sub hn).1 hb a ha1 (by omega) hcomp
  rcases Finset.mem_insert.1 ha with rfl | h
  · have := Nat.Prime.two_le (Nat.minFac_prime (n := n - 1) (by omega)); omega
  · have hm := Finset.mem_filter.1 h
    have hay := (Finset.mem_Icc.1 hm.1).2
    set p := (n - a).minFac
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpd : p ∣ n - a := Nat.minFac_dvd _
    apply hm.2 p (Finset.mem_filter.2 ⟨Finset.mem_Iic.2 (by omega), hpp⟩)
    have h1 : (n - a + a) % p = a % p := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpd]; simp
    rwa [Nat.sub_add_cancel (by omega)] at h1

end LeanFormalizations.Erdos385.Exceptional

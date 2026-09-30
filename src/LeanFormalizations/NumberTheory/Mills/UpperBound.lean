/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# An explicit upper bound on Mills' constant, without RH

`lower_bound` gives `1.3063778838 < ξ` unconditionally; the matching `< 1.3063778839` needs RH
(`lower_bound_of_RH`).  Without RH the best available is astronomically weak but explicit,
from Dudek's explicit cube-gap theorem (`Literature.Dudek2016`, a hypothesis like the others).

## Proof plan

Write `X = exp 33.3` and `E = exp X = exp(exp 33.3)`, and `N₀ = ⌈E⌉₊`.

1. `Dudek2016` is exactly `PrimeBetweenCubesFrom N₀`: for `n ≥ N₀` we have `E ≤ N₀ ≤ n`.
2. Bertrand (`Nat.exists_prime_lt_and_le_two_mul`) gives a prime `p` with `N₀ < p ≤ 2 N₀`
   (applied at `M = max N₀ 2 = N₀`, legal since `E ≥ 34`).
3. `exists_mills_cube_lt_of_primeBetweenCubes` (Basic.lean) starts the nested-interval chain at
   the chosen prime `p` and takes a cube root, so the digit at `n = 1` is `p` itself:
   it returns a Mills `A > 1` with `A³ < p + 1`.
4. `p + 1 ≤ 2 N₀ + 1 ≤ 2(E + 1) + 1 = 2E + 3 ≤ 3E`, while `(2 exp(X/3))³ = 8 exp X = 8E`.
   Since `3E < 8E`, comparing cubes gives `A < 2 exp(X/3)`.
5. A least Mills number `ξ` exists (`exists_least_of_exists`) and `ξ ≤ A`.
-/
import LeanFormalizations.NumberTheory.Mills.LowerBound
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- **The least Mills number exists and is below `2 · exp(exp(33.3) / 3)`**, from Dudek's
explicit cube-gap theorem.  No RH. -/
theorem exists_minMills_lt_of_dudek (h : Dudek2016) :
    ∃ A, IsMinMills A ∧ A < 2 * Real.exp (Real.exp 33.3 / 3) := by
  set X : ℝ := Real.exp 33.3 with hX
  set E : ℝ := Real.exp X with hEdef
  set N₀ : ℕ := ⌈E⌉₊ with hN₀
  -- `E` is enormous; all we need is `34 ≤ E`
  have hX34 : (34 : ℝ) ≤ X := by
    have := Real.add_one_le_exp (33.3 : ℝ); rw [hX]; norm_num at this ⊢; linarith
  have hE34 : (34 : ℝ) ≤ E := by
    have := Real.add_one_le_exp X; rw [hEdef]; linarith
  -- step 1
  have hpbc : PrimeBetweenCubesFrom N₀ := by
    intro n hn
    exact h n (le_trans (Nat.le_ceil E) (by exact_mod_cast hn))
  have hN2 : (2 : ℕ) ≤ N₀ := by
    have hc := Nat.le_ceil E
    have : ((2:ℕ) : ℝ) ≤ ((N₀ : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hmax : max N₀ 2 = N₀ := max_eq_left hN2
  -- step 2: Bertrand
  obtain ⟨p, hp, hplo, hphi⟩ := Nat.exists_prime_lt_and_le_two_mul N₀ (by omega)
  -- step 3
  obtain ⟨A, hA1, hA, hAcube⟩ :=
    exists_mills_cube_lt_of_primeBetweenCubes hpbc hp (by rw [hmax]; omega)
  -- step 4
  have hNE : (N₀ : ℝ) ≤ E + 1 := le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hpR : (p : ℝ) ≤ 2 * (N₀ : ℝ) := by exact_mod_cast hphi
  have hA3 : A ^ 3 < 3 * E := by
    have : (p : ℝ) + 1 ≤ 3 * E := by linarith
    linarith
  have hexp3 : (2 * Real.exp (X / 3)) ^ 3 = 8 * E := by
    have h1 : Real.exp (X / 3) ^ 3 = E := by
      rw [pow_succ, pow_succ, pow_one, ← Real.exp_add, ← Real.exp_add, hEdef]
      congr 1; ring
    rw [mul_pow, h1]; norm_num
  have hAlt : A < 2 * Real.exp (X / 3) := by
    refine lt_of_pow_lt_pow_left₀ 3 (by positivity) ?_
    rw [hexp3]; linarith
  -- step 5
  obtain ⟨ξ, hξ⟩ := exists_least_of_exists ⟨A, hA1, hA⟩
  exact ⟨ξ, hξ, lt_of_le_of_lt (hξ.2 ⟨hA1, hA⟩) hAlt⟩

/-- The same bound for any least Mills number (the least element is unique). -/
theorem minMills_lt_of_dudek (h : Dudek2016) {A : ℝ} (hA : IsMinMills A) :
    A < 2 * Real.exp (Real.exp 33.3 / 3) := by
  obtain ⟨B, hB, hlt⟩ := exists_minMills_lt_of_dudek h
  rw [hA.unique hB]
  exact hlt

end LeanFormalizations.Mills

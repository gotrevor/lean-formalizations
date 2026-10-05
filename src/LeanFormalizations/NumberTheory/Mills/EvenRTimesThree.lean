/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# `ξ(r·3^k − 1)` for even `r`: the cubic 3-adic route is silent

Saito proves `ξ(r·3^k − 1)` transcendental only for `r ≥ 4.003·10¹⁴` (arXiv:2508.16068,
Theorem 1.9(C)), by size.  For even `r` our arithmetic route (Theorem E, `ShiftedMillsAll`) breaks:
the limit points carry `ζ_k^(r·3^m)`, and `x ↦ x^r` is not injective on the Teichmüller roots, so
the class `f ≡ (X − 1)(X + 1)² (mod 3)` survives the congruence step (`PROOF-THEOREM-E.md`,
Variants).

Probe (2026-10-05, coefficients `|a|, |b|, |c| ≤ 12`, `3 ∤ c`, `r ∈ {2, 4, 8, 10}`, window test
`tr C^(r·3^n − 1) ≡ ±1 (mod 3^(max(1, n/3 − 1)))` for `4 ≤ n < 40`): 164 cubic Pisot survivors.
The first, `X³ − 2X² − X − 1 ≡ (X − 1)(X + 1)² (mod 3)` (Pisot, `β ≈ 2.5468`), has
`v₃(tr C^(2·3^n − 1) + 1) = n + 2` exactly for `1 ≤ n ≤ 15`.  Every survivor checked has small hit
primes (here `q = 2, 7, 13, 23`: each divides `tr C^(2·3^n − 1)` along a residue class of `n`), so
the even-`r` variant reduces to the cubic case of a hit-prime statement, like the `5/9` wall
(`ShiftRigidityUnipotent.HitPrime`).
-/

namespace LeanFormalizations.Mills.EvenRTimesThree

/-- Companion matrix of `X³ − 2X² − X − 1`. -/
def C : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 1; 0, 1, 2]

theorem C_three : C ^ 3 = (2 : ℤ) • C ^ 2 + C + 1 := by decide

/-- The trace sequence of `C` by its recurrence `t_(k+3) = 2t_(k+2) + t_(k+1) + t_k`. -/
def tq : ℕ → ℤ × ℤ × ℤ
  | 0 => (3, 2, 6)
  | k + 1 => let t := tq k; (t.2.1, t.2.2, 2 * t.2.2 + t.2.1 + t.1)

theorem tq_eq (k : ℕ) : tq k = ((C ^ k).trace, (C ^ (k + 1)).trace, (C ^ (k + 2)).trace) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h3 : C ^ (k + 3) = (2 : ℤ) • C ^ (k + 2) + C ^ (k + 1) + C ^ k := by
      rw [pow_add, C_three]
      simp only [mul_add, mul_smul_comm, ← pow_add, mul_one, ← pow_succ]
    rw [tq, ih]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show _ = (C ^ (k + 3)).trace
    rw [h3]
    simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

/-- **Native-checked range**: `tr C^(2·3^n − 1) ≡ −1 (mod 3^(n+2))` for `1 ≤ n ≤ 8`. -/
theorem tq_mod : ∀ n ∈ Finset.Icc 1 8, ((tq (2 * 3 ^ n - 1)).1 + 1) % 3 ^ (n + 2) = 0 := by
  native_decide

theorem trace_congr_le_eight {n : ℕ} (h1 : 1 ≤ n) (h8 : n ≤ 8) :
    (3 : ℤ) ^ (n + 2) ∣ (C ^ (2 * 3 ^ n - 1)).trace + 1 := by
  have h := tq_mod n (Finset.mem_Icc.2 ⟨h1, h8⟩)
  rw [tq_eq] at h
  exact Int.dvd_of_emod_eq_zero h

/-- **Believed (~95%, numerics to `n = 15`)**: the congruence for every `n ≥ 1`, so the window and
the Teichmüller limit identity of the cubic route hold with `ω = −1` along `r = 2`. -/
theorem trace_congr (n : ℕ) (hn : 1 ≤ n) :
    (3 : ℤ) ^ (n + 2) ∣ (C ^ (2 * 3 ^ n - 1)).trace + 1 := by
  sorry

end LeanFormalizations.Mills.EvenRTimesThree

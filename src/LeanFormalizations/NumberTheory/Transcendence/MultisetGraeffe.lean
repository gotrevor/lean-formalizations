/-
# The Graeffe identity for elementary symmetric functions

Step 3 of the Dubickas "no-gap" route (`PROBE-DUBICKAS-NOGAP.md`) needs the effect of *squaring*
every element of a multiset on its elementary symmetric functions:

    (−1)^k · eₖ(s²) = Σ_{i+j = 2k} (−1)^i · eᵢ(s) · e_j(s).

This is the coefficient form of `∏(1 − z X)·∏(1 + z X) = ∏(1 − z² X²)`.  The proof runs through
the generating polynomial `genPoly s = ∏_{z ∈ s} (1 − z·X)`, whose `k`-th coefficient is
`(−1)^k eₖ(s)`, and mathlib's `Polynomial.expand R 2` (`= · ∘ X²`).

## Status: SORRY-FREE
-/
import Mathlib

namespace LeanFormalizations.Transcendence

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- `eₖ(a ::ₘ s) = eₖ(s) + a · e_{k−1}(s)`. -/
theorem Multiset.esymm_cons (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  exact congrArg _ (Multiset.map_congr rfl fun t _ => by simp)

theorem Multiset.esymm_zero' (s : Multiset R) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

/-- The generating polynomial `∏_{z ∈ s} (1 − z·X)`. -/
noncomputable def genPoly (s : Multiset R) : R[X] := (s.map fun z => 1 - C z * X).prod

@[simp] theorem genPoly_zero : genPoly (0 : Multiset R) = 1 := by simp [genPoly]

theorem genPoly_cons (a : R) (s : Multiset R) :
    genPoly (a ::ₘ s) = (1 - C a * X) * genPoly s := by
  simp [genPoly]

/-- **Vieta for `genPoly`**: its `k`-th coefficient is `(−1)^k eₖ(s)`. -/
theorem genPoly_coeff (s : Multiset R) (k : ℕ) :
    (genPoly s).coeff k = (-1) ^ k * s.esymm k := by
  induction s using Multiset.induction generalizing k with
  | empty =>
      match k with
      | 0 => simp [Multiset.esymm_zero']
      | (n + 1) => simp [Multiset.esymm, coeff_one]
  | cons a s ih =>
      rw [genPoly_cons, sub_mul, one_mul, coeff_sub]
      match k with
      | 0 => simp [Multiset.esymm_zero', ih]
      | (n + 1) =>
          rw [Multiset.esymm_cons, ih (n + 1), mul_comm (C a) X, mul_assoc, coeff_X_mul,
            coeff_C_mul, ih n]
          ring

/-- `∏(1 − z X)·∏(1 + z X) = ∏(1 − z² X²)`. -/
theorem expand_genPoly_map_sq (s : Multiset R) :
    (expand R 2) (genPoly (s.map (· ^ 2))) = genPoly s * genPoly (s.map Neg.neg) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.map_cons, genPoly_cons, genPoly_cons, genPoly_cons, map_mul,
        ih]
      have h1 : (expand R 2) (1 - C (a ^ 2) * X) = 1 - C a * X * (1 - C (-a) * X)
          - C (-a) * X * (1 - C a * X) - C a * X * (C (-a) * X) := by
        simp only [map_sub, map_one, map_mul, expand_C, expand_X, map_neg, map_pow]
        ring
      rw [h1]
      ring

/-- **The Graeffe identity**: `(−1)^k eₖ(s²) = Σ_{i+j=2k} (−1)^i eᵢ(s) e_j(s)`. -/
theorem esymm_map_sq (s : Multiset R) (k : ℕ) :
    (-1 : R) ^ k * (s.map (· ^ 2)).esymm k
      = ∑ p ∈ Finset.antidiagonal (2 * k), (-1) ^ p.1 * s.esymm p.1 * s.esymm p.2 := by
  have h1 : (genPoly (s.map (· ^ 2))).coeff k
      = ((expand R 2) (genPoly (s.map (· ^ 2)))).coeff (2 * k) := by
    rw [coeff_expand_mul' (by norm_num)]
  rw [← genPoly_coeff, h1, expand_genPoly_map_sq, coeff_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [genPoly_coeff, genPoly_coeff, Multiset.esymm_neg]
  have h2 : ((-1 : R)) ^ p.2 * (-1) ^ p.2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (s.esymm p.1 * s.esymm p.2 * (-1 : R) ^ p.1) * h2

end LeanFormalizations.Transcendence

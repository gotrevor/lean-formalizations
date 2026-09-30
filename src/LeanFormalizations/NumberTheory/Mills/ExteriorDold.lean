/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.GaussCongruenceProof

/-!
# Phase 50: the Dold congruence for every characteristic-polynomial coefficient (Theorem A, step 2)

Phase 49 proved `p^(k+1) ∣ tr A^(p^(k+1)) − tr A^(p^k)` for every integer matrix `A`
(`GaussCongruenceProof.gaussCongruenceTrace_holds`).  Here we upgrade it to the whole
characteristic polynomial:

  `χ_(A^(p^(k+1))) ≡ χ_(A^(p^k))  (mod p^(k+1))`, coefficientwise,

and deduce the Cayley–Hamilton corollary `χ_(A^(p^k))(A^(p^(k+1))) ≡ 0 (mod p^(k+1))`, which is what
makes `σ : q(B) ↦ q(B^p)` a well-defined ring endomorphism of `(ℤ/p^(k+1))[B]`, `B = A^(p^k)`
(Theorem A route, step 3; see `ROADMAP-PRIME-TOWERS.md` §4a).

## Route (exterior powers / compound matrices)
1. For `j ≤ n`, the `j`-th **compound matrix** `Λʲ M`, indexed by the `j`-subsets `s` of `Fin n`
   (`Finset.powersetCard j univ`, or mathlib's `powersetCard` subtype used by
   `Module.Basis.exteriorPower`), has entries `det M[s, t]` (the `s × t` minor).
   Either define it directly, or take `LinearMap.toMatrix` of `exteriorPower.map j (toLin' M)` in the
   basis `(Pi.basisFun ℤ (Fin n)).exteriorPower` (`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`).
2. **Multiplicativity** `Λʲ(MN) = Λʲ M · Λʲ N` (Cauchy–Binet).  Via the exterior-power route it is
   functoriality of `exteriorPower.map`; via the direct route it is Cauchy–Binet, which mathlib
   may lack — prefer the exterior-power route if the matrix-entry identification (step 3) is cheap.
   Consequently `Λʲ(M^N) = (Λʲ M)^N`.
3. **Trace = principal minors:** `tr Λʲ M = Σ_(|s| = j) det M[s, s]`, the diagonal entries.
4. `Matrix.charpoly_coeff_eq_sum_minors`: `M.charpoly.coeff (n − j) = (−1)^j · Σ_(|s|=j) det M[s,s]`.
5. Apply `gaussCongruenceTrace_holds` to `Λʲ A` (reindexed to `Fin m` by `Fintype.equivFin`; trace is
   invariant under `Matrix.reindex`).  Coefficients of index `> n` are `0` on both sides.
6. Corollary: `χ_(A^(p^(k+1)))(A^(p^(k+1))) = 0` (`Matrix.aeval_self_charpoly`), and the two
   polynomials differ by `p^(k+1)·(integer polynomial)`.

Frozen: the two statements below; all earlier statements; `Literature/`.  No `private`.
Helpers are public; add as many as needed.
-/

namespace LeanFormalizations.Mills.ExteriorDold

open Matrix Polynomial

/-- **Dold congruence for every coefficient of the characteristic polynomial.** -/
theorem charpoly_coeff_prime_pow_congr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {p : ℕ}
    (hp : p.Prime) (k j : ℕ) :
    (p : ℤ) ^ (k + 1) ∣ (A ^ (p ^ (k + 1))).charpoly.coeff j - (A ^ (p ^ k)).charpoly.coeff j := by
  sorry

/-- **Cayley–Hamilton across one Frobenius step:** `χ_B(B^p) ≡ 0 (mod p^(k+1))` for `B = A^(p^k)`. -/
theorem aeval_charpoly_prime_pow_congr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) (i j : Fin n) :
    (p : ℤ) ^ (k + 1) ∣ (Polynomial.aeval (A ^ (p ^ (k + 1))) (A ^ (p ^ k)).charpoly) i j := by
  sorry

end LeanFormalizations.Mills.ExteriorDold

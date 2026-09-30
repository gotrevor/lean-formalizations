/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.GaussCongruenceProof
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Reindex

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

open Matrix Polynomial Set

noncomputable section

variable {R : Type*} [CommRing R] {n j : ℕ}

/-! ## The compound matrix as the matrix of an exterior power -/

noncomputable def extBasis (R : Type*) [CommRing R] (n j : ℕ) :
    Module.Basis (powersetCard (Fin n) j) R (⋀[R]^j (Fin n → R)) :=
  (Pi.basisFun R (Fin n)).exteriorPower j

noncomputable def compound (j : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    Matrix (powersetCard (Fin n) j) (powersetCard (Fin n) j) R :=
  LinearMap.toMatrix (extBasis R n j) (extBasis R n j) (exteriorPower.map j (Matrix.toLin' M))

theorem compound_apply (M : Matrix (Fin n) (Fin n) R) (s t : powersetCard (Fin n) j) :
    compound j M s t = (M.submatrix (powersetCard.ofFinEmbEquiv.symm s)
      (powersetCard.ofFinEmbEquiv.symm t)).det := by
  rw [compound, LinearMap.toMatrix_apply, extBasis, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose (M.submatrix _ _)]
  congr 1
  ext a b
  simp [Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.mulVec_single]


theorem compound_mul (M N : Matrix (Fin n) (Fin n) R) :
    compound j (M * N) = compound j M * compound j N := by
  rw [compound, compound, compound, Matrix.toLin'_mul, exteriorPower.map_comp,
    LinearMap.toMatrix_comp (extBasis R n j) (extBasis R n j) (extBasis R n j)]

theorem compound_one : compound j (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [compound, Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

theorem compound_pow (M : Matrix (Fin n) (Fin n) R) (N : ℕ) :
    compound j (M ^ N) = (compound j M) ^ N := by
  induction N with
  | zero => simpa using compound_one
  | succ m ih => rw [pow_succ, pow_succ, compound_mul, ih]

theorem trace_compound (M : Matrix (Fin n) (Fin n) R) :
    (compound j M).trace
      = ∑ s ∈ Finset.univ.powersetCard j,
        (M.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det := by
  have hdiag : ∀ s : powersetCard (Fin n) j, compound j M s s
      = (M.submatrix (Subtype.val : ↥(s : Finset (Fin n)) → Fin n)
          (Subtype.val : ↥(s : Finset (Fin n)) → Fin n)).det := by
    intro s
    rw [compound_apply]
    have he : (Subtype.val : ↥(s : Finset (Fin n)) → Fin n) ∘
        (powersetCard.orderIsoOfFin s).toEquiv = powersetCard.ofFinEmbEquiv.symm s := by
      funext i
      simp [powersetCard.orderIsoOfFin, powersetCard.ofFinEmbEquiv_symm_apply]
    rw [← Matrix.det_submatrix_equiv_self (powersetCard.orderIsoOfFin s).toEquiv
      (M.submatrix (Subtype.val : ↥(s : Finset (Fin n)) → Fin n) Subtype.val),
      Matrix.submatrix_submatrix, he]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hdiag]
  rw [← Finset.sum_coe_sort (Finset.univ.powersetCard j)]
  exact Fintype.sum_equiv
    (Equiv.subtypeEquivRight (fun s => by simp [Finset.mem_powersetCard])) _ _ (fun a => rfl)

theorem trace_reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (X : Matrix α α R) : (Matrix.reindex e e X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact (Fintype.sum_equiv e _ _ (fun a => by simp)).symm

/-- The Gauss congruence for the sum of the principal `j × j` minors. -/
theorem gauss_minors {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {p : ℕ} (hp : p.Prime) (k j : ℕ) :
    (p : ℤ) ^ (k + 1) ∣ (compound j (A ^ (p ^ (k + 1)))).trace
      - (compound j (A ^ (p ^ k))).trace := by
  classical
  set m := Fintype.card (powersetCard (Fin n) j) with hm
  set e : powersetCard (Fin n) j ≃ Fin m := Fintype.equivFin _ with he
  set C : Matrix (Fin m) (Fin m) ℤ := Matrix.reindex e e (compound j A) with hC
  have hpow : ∀ N : ℕ, (compound j (A ^ N)).trace = (C ^ N).trace := by
    intro N
    rw [hC, show (Matrix.reindex e e (compound j A) : Matrix (Fin m) (Fin m) ℤ)
        = Matrix.reindexAlgEquiv ℤ ℤ e (compound j A) from rfl, ← map_pow,
      Matrix.coe_reindexAlgEquiv, trace_reindex, compound_pow]
  rw [hpow, hpow]
  exact GaussCongruenceProof.gaussCongruenceTrace_holds m C p k hp

theorem charpoly_coeff_eq_trace_compound {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (jj : ℕ)
    (h : jj ≤ n) : M.charpoly.coeff (n - jj) = (-1) ^ jj * (compound jj M).trace := by
  rw [trace_compound]
  have := M.charpoly_coeff_eq_sum_minors jj (by simpa using h)
  simpa using this

theorem charpoly_coeff_congr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {p : ℕ}
    (hp : p.Prime) (k j : ℕ) :
    (p : ℤ) ^ (k + 1) ∣ (A ^ (p ^ (k + 1))).charpoly.coeff j - (A ^ (p ^ k)).charpoly.coeff j := by
  rcases le_or_gt j n with hj | hj
  · have hjj : n - (n - j) = j := by omega
    have h1 := charpoly_coeff_eq_trace_compound (A ^ (p ^ (k + 1))) (n - j) (by omega)
    have h2 := charpoly_coeff_eq_trace_compound (A ^ (p ^ k)) (n - j) (by omega)
    rw [hjj] at h1 h2
    rw [h1, h2, ← mul_sub]
    exact Dvd.dvd.mul_left (gauss_minors A hp k (n - j)) _
  · have hz : ∀ M : Matrix (Fin n) (Fin n) ℤ, M.charpoly.coeff j = 0 := by
      intro M
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [M.charpoly_natDegree_eq_dim]
      simpa using hj
    simp [hz]

theorem dvd_aeval_entry {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (q : Polynomial ℤ) (d : ℤ)
    (h : ∀ i, d ∣ q.coeff i) (a b : Fin n) : d ∣ (Polynomial.aeval M q) a b := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum, Matrix.sum_apply]
  refine Finset.dvd_sum (fun i _ => ?_)
  rw [← Algebra.smul_def, Matrix.smul_apply, smul_eq_mul]
  exact Dvd.dvd.mul_right (h i) _

theorem aeval_charpoly_congr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) (a b : Fin n) :
    (p : ℤ) ^ (k + 1) ∣ (Polynomial.aeval (A ^ (p ^ (k + 1))) (A ^ (p ^ k)).charpoly) a b := by
  set B := A ^ (p ^ (k + 1)) with hB
  have hz : Polynomial.aeval B B.charpoly = 0 := Matrix.aeval_self_charpoly B
  have hsplit : Polynomial.aeval B (A ^ (p ^ k)).charpoly
      = Polynomial.aeval B ((A ^ (p ^ k)).charpoly - B.charpoly) := by
    rw [map_sub, hz, sub_zero]
  rw [hsplit]
  refine dvd_aeval_entry _ _ _ (fun i => ?_) a b
  rw [Polynomial.coeff_sub]
  have h := (charpoly_coeff_congr A hp k i).neg_right
  rw [neg_sub] at h
  exact h

/-- **Dold congruence for every coefficient of the characteristic polynomial.** -/
theorem charpoly_coeff_prime_pow_congr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {p : ℕ}
    (hp : p.Prime) (k j : ℕ) :
    (p : ℤ) ^ (k + 1) ∣ (A ^ (p ^ (k + 1))).charpoly.coeff j - (A ^ (p ^ k)).charpoly.coeff j :=
  charpoly_coeff_congr A hp k j

/-- **Cayley–Hamilton across one Frobenius step:** `χ_B(B^p) ≡ 0 (mod p^(k+1))` for `B = A^(p^k)`. -/
theorem aeval_charpoly_prime_pow_congr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) (i j : Fin n) :
    (p : ℤ) ^ (k + 1) ∣ (Polynomial.aeval (A ^ (p ^ (k + 1))) (A ^ (p ^ k)).charpoly) i j :=
  aeval_charpoly_congr A hp k i j

end

end LeanFormalizations.Mills.ExteriorDold

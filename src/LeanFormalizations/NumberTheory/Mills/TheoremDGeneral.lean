/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDQuadratic

/-!
# Phase 56 (multi-phase): Theorem D in every degree — Saito's Problem 1.7 for `R(n) = c^n + s`

**Target.**  Let `α > 1` be a Pisot number of degree `d ≥ 2`: a root of a monic irreducible
`f ∈ ℤ[X]` whose other complex roots have modulus `< 1`.  Let `c` be a prime with `c ∤ f(0)`, and
`s` with `α^s > d + 1`.  Then `⌊α^(c^n + s)⌋` is **not prime for infinitely many `n`**.
Corollary (degree 3, Saito's "especially"): the plastic number `ρ` (`ρ³ = ρ + 1`), for every prime `c`,
with `s = 5` (`ρ⁵ ≈ 4.08 > 4`).

Paper proof: `PROOF-THEOREM-D.md` draft 2 (the one-automorphism size argument; with `c ∤ f(0)` every
root is a `c`-unit, so no automorphism is needed).

## Route: generalize phase 55 (read `HANDOFF-2026-09-30-phase55-complete.md` first)
Phase 55 found that the whole `c`-adic → archimedean transfer is **integer polynomial equations +
Nullstellensatz + integrality** (`TheoremDQuadratic.exists_complex_zero_of_all_levels`, which is
already stated for a general finite variable set `σ`).  For degree `d`:
1. **Floor = trace + offset.**  `⌊α^N⌋ = tr C^N + ε_N`, `ε_N ∈ {0, −1}`, for large `N` (`C` the
   companion matrix of `f`; `tr C^N = Σ_k α_k^N`; `δ_N = Σ_(k≥2) α_k^N` is real and `→ 0`; if
   `δ_N = 0` then `α^N ∈ ℤ`, impossible for `d ≥ 2` since its conjugates would have modulus `> 1`).
2. **Filter, stuck alternation, good indices unbounded:** as in phases 44/55, with `GL_d(𝔽_p)`.
3. **Window:** at a good `n`, `p_n^i ≡ 1 (mod c^(e_n))` for some `1 ≤ i ≤ d`, `e_n → ∞`.
4. **Pigeonhole** on (the residue of `n` mod the Teichmüller period `D`, which divides
   `lcm_(f ≤ d)(c^f − 1)`-related data; the pair `(i, ε)`).
5. **Integer system at every level `k`:** variables `x₀, …, x_(d−1)` (for `T = Σ x_j C^j`) and `w`,
   with equations `T^Q = I` (`Q = |GL_d(𝔽_c)|`), `w^(i·m) = 1` for a suitable `m` (or `w^i = 1` after
   the window's lifting), and `tr(T·C^s) = w − ε`.  Integer solutions mod `c^k` for every `k` come
   from `T ≡ C^(c^n)` (phase 47/55 torsion congruence) and `w ≡ p_n`.
6. **Transfer:** `exists_complex_zero_of_all_levels` gives a complex solution.
7. **Size:** over ℂ, `T = P(C)` with `P(X) = Σ x_j X^j`, and `C` is diagonalizable with eigenvalues
   `α_k` (distinct: `f` separable), so `tr(T C^s) = Σ_k u_k α_k^s` with `u_k = P(α_k)`, `u_k^Q = 1`,
   and `|w| = 1`.  So `α^s ≤ |w − ε| + Σ_(k≥2) |α_k|^s < 2 + (d − 1) = d + 1`: contradiction.
   (Avoid diagonalization if easier: `u_k = P(α_k)` satisfies `u_k^Q = 1` because `P(X)^Q − 1` is
   divisible by `f` over ℂ... it vanishes at the matrix `C`, whose minimal polynomial is `f`.)

**Decomposing into named sub-lemmas is progress**; generalize phase-55 lemmas rather than copying
them where it is cheap.  Do not change phase 55's frozen statement.

Frozen: the two statements below; all earlier statements; `Literature/`.  No `private`.
(Window encoding hint: at level `k`, `p_n ≡ ω (mod c^k)` with `ω` a `c`-adic root of unity; use the
integer Teichmüller residue `w`, `w^(c−1) ≡ 1` (`c` odd) or `w² ≡ 1` (`c = 2`), as the extra variable.)
-/

namespace LeanFormalizations.Mills.TheoremDGeneral

open Filter Polynomial

/-! ## The spectral bridge (the new content of this phase)

Phase 55 did steps 6–7 by explicit `2 × 2` formulas.  In degree `d` the structural replacement is a
**Vandermonde conjugation**: if `f` is monic of degree `d` with `d` distinct complex roots
`e 0, …, e (d-1)`, then the row vector `(1, z, …, z^(d-1))` is a left eigenvector of the companion
matrix `compM ℂ f` with eigenvalue `z` for every root `z`, i.e.

`vandermonde e * compM ℂ f = diagonal e * vandermonde e`,

and `vandermonde e` is invertible.  Consequently `compM ℂ f` is diagonalised by `vandermonde e`,
which yields *both* facts the size argument needs:
`tr (g(C) · C^s) = Σ_k g(e k) · (e k)^s` and `g(C)^Q = 1 → (g (e k))^Q = 1`.
No diagonalisability theory, no field embeddings.
-/

/-- The companion matrix of a monic integer polynomial `f`, read in any commutative ring. -/
def compM (R : Type*) [CommRing R] (f : ℤ[X]) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
  Matrix.of fun i j =>
    (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) -
      (if (j : ℕ) + 1 = f.natDegree then ((f.coeff i : ℤ) : R) else 0)

/-- Ring homomorphisms commute with `compM` (its entries are integers). -/
theorem compM_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : ℤ[X]) :
    (compM R f).map φ = compM S f := by
  ext i j
  simp only [compM, Matrix.map_apply, Matrix.of_apply, map_sub, map_intCast]
  split_ifs <;> simp

/-- **The left eigenvector.**  For a root `z` of `f` (monic), the row `(1, z, …, z^(d-1))` satisfies
`row · C = z · row`, coordinate `j` of which is `∑ i, z^i · C i j = z^(j+1)`. -/
theorem sum_pow_mul_compM {R : Type*} [CommRing R] (f : ℤ[X]) (hmon : f.Monic) (z : R)
    (hz : (f.map (Int.castRingHom R)).eval z = 0) (j : Fin f.natDegree) :
    ∑ i : Fin f.natDegree, z ^ (i : ℕ) * compM R f i j = z ^ ((j : ℕ) + 1) := by
  have hsplit : ∀ i : Fin f.natDegree, z ^ (i : ℕ) * compM R f i j
      = (if (i : ℕ) = (j : ℕ) + 1 then z ^ ((j : ℕ) + 1) else 0)
        - (if (j : ℕ) + 1 = f.natDegree then ((f.coeff i : ℤ) : R) * z ^ (i : ℕ) else 0) := by
    intro i
    simp only [compM, Matrix.of_apply]
    split_ifs with h₁ h₂ h₂ <;> simp_all <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib]
  by_cases hj : (j : ℕ) + 1 = f.natDegree
  · -- no index equals `j + 1 = d`; the second sum is `eval z f - z^d = -z^d`
    have h1 : (∑ i : Fin f.natDegree, if (i : ℕ) = (j : ℕ) + 1 then z ^ ((j : ℕ) + 1) else 0)
        = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have : (i : ℕ) ≠ (j : ℕ) + 1 := by have := i.2; omega
      simp [this]
    have h2 : (∑ i : Fin f.natDegree,
          if (j : ℕ) + 1 = f.natDegree then ((f.coeff i : ℤ) : R) * z ^ (i : ℕ) else 0)
        = - z ^ ((j : ℕ) + 1) := by
      simp only [if_pos hj]
      have hle : (f.map (Int.castRingHom R)).natDegree < f.natDegree + 1 :=
        lt_of_le_of_lt Polynomial.natDegree_map_le (by omega)
      have hev := Polynomial.eval_eq_sum_range' hle z
      rw [hz] at hev
      simp only [Polynomial.coeff_map, Int.coe_castRingHom, eq_intCast] at hev
      rw [Finset.sum_range_succ, hmon.coeff_natDegree] at hev
      rw [hj, Fin.sum_univ_eq_sum_range (fun i => ((f.coeff i : ℤ) : R) * z ^ i) f.natDegree]
      push_cast at hev
      linear_combination -hev
    rw [h1, h2]; ring
  · have hlt : (j : ℕ) + 1 < f.natDegree := by have := j.2; omega
    have h1 : (∑ i : Fin f.natDegree, if (i : ℕ) = (j : ℕ) + 1 then z ^ ((j : ℕ) + 1) else 0)
        = z ^ ((j : ℕ) + 1) := by
      rw [Finset.sum_eq_single_of_mem (⟨(j : ℕ) + 1, hlt⟩ : Fin f.natDegree)
        (Finset.mem_univ _) ?_]
      · simp
      · intro i _ hi
        have : (i : ℕ) ≠ (j : ℕ) + 1 := by
          intro h; exact hi (Fin.ext h)
        simp [this]
    simp [h1, hj]


/-! ### Conjugation helpers -/

/-- If `V A = B V` with `V` invertible then `V A^m = B^m V`. -/
theorem conj_pow {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (V A B : Matrix n n R) (h : V * A = B * V) (m : ℕ) : V * A ^ m = B ^ m * V := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc V * A ^ (m + 1) = (V * A ^ m) * A := by rw [pow_succ, Matrix.mul_assoc]
        _ = B ^ m * (V * A) := by rw [ih, Matrix.mul_assoc]
        _ = B ^ (m + 1) * V := by rw [h, pow_succ, Matrix.mul_assoc]

/-- Conjugate matrices have equal traces. -/
theorem conj_trace {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (V A B : Matrix n n R) (hV : IsUnit V.det) (h : V * A = B * V) : A.trace = B.trace := by
  have hA : A = V⁻¹ * (B * V) := by
    rw [← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul V hV, Matrix.one_mul]
  rw [hA, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv V hV, Matrix.mul_one]

/-- `V A = B V` with `V` invertible and `A = 1` forces `B = 1`. -/
theorem conj_eq_one {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (V B : Matrix n n R) (hV : IsUnit V.det) (h : V * 1 = B * V) : B = 1 := by
  rw [Matrix.mul_one] at h
  have hB : B = V * V⁻¹ :=
    calc B = B * (V * V⁻¹) := by rw [Matrix.mul_nonsing_inv V hV, Matrix.mul_one]
      _ = (B * V) * V⁻¹ := by rw [Matrix.mul_assoc]
      _ = V * V⁻¹ := by rw [← h]
  rw [hB, Matrix.mul_nonsing_inv V hV]

/-! ### The Vandermonde conjugation -/

/-- The general element of the algebra generated by the companion matrix: `T = ∑_j x_j C^j`. -/
def polyMat (R : Type*) [CommRing R] (f : ℤ[X]) (x : Fin f.natDegree → R) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
  ∑ j : Fin f.natDegree, x j • compM R f ^ (j : ℕ)

/-- Its spectral value at a root: `P(z) = ∑_j x_j z^j`. -/
def polyVal {R : Type*} [CommRing R] {d : ℕ} (x : Fin d → R) (z : R) : R :=
  ∑ j : Fin d, x j * z ^ (j : ℕ)

theorem polyMat_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : ℤ[X])
    (x : Fin f.natDegree → R) : (polyMat R f x).map φ = polyMat S f (fun j => φ (x j)) := by
  classical
  rw [polyMat, polyMat]
  rw [show ((∑ j : Fin f.natDegree, x j • compM R f ^ (j : ℕ)).map φ)
      = ∑ j : Fin f.natDegree, ((x j • compM R f ^ (j : ℕ)).map φ) from by
    ext i k; simp [Matrix.sum_apply, Matrix.map_apply]]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i k
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  congr 1
  have : ((compM R f ^ (j : ℕ)).map φ) i k = (compM S f ^ (j : ℕ)) i k := by
    rw [show (compM R f ^ (j : ℕ)).map φ = ((compM R f).map φ) ^ (j : ℕ) from
      (RingHom.mapMatrix φ).map_pow (compM R f) (j : ℕ) ▸ rfl, compM_map]
  simpa [Matrix.map_apply] using this

/-- **The diagonalising identity.**  `vandermonde e · C = diagonal e · vandermonde e`. -/
theorem vandermonde_mul_compM {R : Type*} [CommRing R] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → R)
    (he : ∀ i, (f.map (Int.castRingHom R)).eval (e i) = 0) :
    Matrix.vandermonde e * compM R f = Matrix.diagonal e * Matrix.vandermonde e := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  simp only [Matrix.vandermonde_apply]
  rw [sum_pow_mul_compM f hmon (e i) (he i) j]
  ring

/-- `∑_j x_j (diagonal e)^j = diagonal (P(e ·))`. -/
theorem sum_smul_diagonal_pow {R : Type*} [CommRing R] {d : ℕ} (x e : Fin d → R) :
    ∑ j : Fin d, x j • (Matrix.diagonal e) ^ (j : ℕ)
      = Matrix.diagonal (fun i => polyVal x (e i)) := by
  classical
  ext i k
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases h : i = k
  · subst h
    simp only [polyVal, Matrix.smul_apply, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
      smul_eq_mul]
    rfl
  · simp [h, Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ h]

/-- **The Vandermonde conjugation for a general algebra element.** -/
theorem vandermonde_mul_polyMat {R : Type*} [CommRing R] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → R)
    (he : ∀ i, (f.map (Int.castRingHom R)).eval (e i) = 0) (x : Fin f.natDegree → R) :
    Matrix.vandermonde e * polyMat R f x
      = Matrix.diagonal (fun i => polyVal x (e i)) * Matrix.vandermonde e := by
  classical
  rw [polyMat, Finset.mul_sum, ← sum_smul_diagonal_pow x e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_pow _ _ _ (vandermonde_mul_compM f hmon e he) (j : ℕ)]


/-! ### The two payoff lemmas -/

/-- The Vandermonde matrix of distinct elements of a field is invertible. -/
theorem vandermonde_isUnit_det {K : Type*} [Field K] {d : ℕ} (e : Fin d → K)
    (hinj : Function.Injective e) : IsUnit (Matrix.vandermonde e).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.1 hj
  exact sub_ne_zero_of_ne fun h => (ne_of_gt hij) (hinj h)

/-- **Payoff 1 (the trace).**  `tr (P(C) · C^s) = ∑_k P(e k) · (e k)^s`. -/
theorem trace_polyMat_mul_compM_pow {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (hinj : Function.Injective e) (x : Fin f.natDegree → K) (s : ℕ) :
    (polyMat K f x * compM K f ^ s).trace = ∑ i, polyVal x (e i) * e i ^ s := by
  classical
  set V := Matrix.vandermonde e with hV
  have hconj : V * (polyMat K f x * compM K f ^ s)
      = Matrix.diagonal (fun i => polyVal x (e i) * e i ^ s) * V := by
    calc V * (polyMat K f x * compM K f ^ s)
        = (V * polyMat K f x) * compM K f ^ s := by rw [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => polyVal x (e i)) * (V * compM K f ^ s) := by
            rw [vandermonde_mul_polyMat f hmon e he x, Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => polyVal x (e i))
            * (Matrix.diagonal e ^ s * V) := by
            rw [conj_pow _ _ _ (vandermonde_mul_compM f hmon e he) s]
      _ = Matrix.diagonal (fun i => polyVal x (e i) * e i ^ s) * V := by
            rw [← Matrix.mul_assoc, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
            rfl
  rw [conj_trace V _ _ (vandermonde_isUnit_det e hinj) hconj, Matrix.trace_diagonal]

/-- **Payoff 2 (roots of unity).**  If `P(C)^Q = 1` then every `P(e k)` is a `Q`-th root of 1. -/
theorem polyVal_pow_eq_one {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (hinj : Function.Injective e) (x : Fin f.natDegree → K) {Q : ℕ}
    (hQ : polyMat K f x ^ Q = 1) (i : Fin f.natDegree) : polyVal x (e i) ^ Q = 1 := by
  classical
  set V := Matrix.vandermonde e with hV
  have hpow := conj_pow V (polyMat K f x) (Matrix.diagonal (fun i => polyVal x (e i)))
    (vandermonde_mul_polyMat f hmon e he x) Q
  rw [hQ] at hpow
  have hd : (Matrix.diagonal (fun i => polyVal x (e i))) ^ Q = 1 :=
    conj_eq_one V _ (vandermonde_isUnit_det e hinj) hpow
  rw [Matrix.diagonal_pow] at hd
  have := congrArg (fun M : Matrix (Fin f.natDegree) (Fin f.natDegree) K => M i i) hd
  simpa using this

/-- **Theorem D, every degree** (all roots `c`-units). -/
theorem floor_pow_prime_pow_add_not_prime_general (f : ℤ[X]) (hmon : f.Monic)
    (hirr : Irreducible f) (hdeg : 2 ≤ f.natDegree) {α : ℝ} (hroot : aeval α f = 0)
    (hα : 1 < α)
    (hpisot : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1)
    {c : ℕ} (hc : c.Prime) (hc0 : ¬ (c : ℤ) ∣ f.coeff 0)
    {s : ℕ} (hs : (f.natDegree : ℝ) + 1 < α ^ s) :
    ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime := by
  sorry

/-- **Degree 3 (Saito's "especially"):** the plastic number, every prime `c`, shift `5`. -/
theorem plastic_floor_pow_prime_pow_add_not_prime {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hρ1 : 1 < ρ)
    {c : ℕ} (hc : c.Prime) :
    ∃ᶠ n in atTop, ¬ (⌊ρ ^ (c ^ n + 5)⌋₊).Prime := by
  sorry

end LeanFormalizations.Mills.TheoremDGeneral

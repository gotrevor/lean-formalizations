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

open Filter Polynomial LeanFormalizations.Mills.ThreeAdic

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


/-! ### Step 1a: the trace sequence and the root enumeration -/

/-- The integer trace sequence `V_N = tr(C^N)`; for `d = 2` this is `lucasV`. -/
def traceSeq (f : ℤ[X]) (N : ℕ) : ℤ := (compM ℤ f ^ N).trace

theorem traceSeq_cast {R : Type*} [CommRing R] (f : ℤ[X]) (N : ℕ) :
    ((traceSeq f N : ℤ) : R) = (compM R f ^ N).trace := by
  have hmap : (compM ℤ f ^ N).map (Int.castRingHom R) = compM R f ^ N := by
    rw [show (compM ℤ f ^ N).map (Int.castRingHom R)
        = ((compM ℤ f).map (Int.castRingHom R)) ^ N from
      (RingHom.mapMatrix (Int.castRingHom R)).map_pow (compM ℤ f) N ▸ rfl, compM_map]
  rw [← hmap, traceSeq, Matrix.trace, Matrix.trace]
  simp [Matrix.diag, Matrix.map_apply]

/-- **Step 1a.**  `V_N = ∑_k (e k)^N`: the trace of the companion power is the power sum of the
roots.  (Immediate from the Vandermonde conjugation.) -/
theorem traceSeq_eq_root_sum {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (hinj : Function.Injective e) (N : ℕ) :
    ((traceSeq f N : ℤ) : K) = ∑ i, (e i) ^ N := by
  rw [traceSeq_cast]
  have hconj := conj_pow (Matrix.vandermonde e) (compM K f) (Matrix.diagonal e)
    (vandermonde_mul_compM f hmon e he) N
  rw [conj_trace _ _ _ (vandermonde_isUnit_det e hinj) hconj, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  rfl

/-- **The root enumeration.**  A monic irreducible integer polynomial of degree `d ≥ 1` has an
injective enumeration `e : Fin d → ℂ` of its complex roots hitting every root (irreducibility gives
separability, so there are exactly `d` of them). -/
theorem exists_root_enum (f : ℤ[X]) (hmon : f.Monic) (hirr : Irreducible f) :
    ∃ e : Fin f.natDegree → ℂ, Function.Injective e ∧
      (∀ i, (f.map (Int.castRingHom ℂ)).eval (e i) = 0) ∧
      ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).eval z = 0 → ∃ i, e i = z := by
  classical
  set fC := f.map (Int.castRingHom ℂ) with hfCdef
  have hfC0 : fC ≠ 0 := (hmon.map (Int.castRingHom ℂ)).ne_zero
  have hnd : fC.natDegree = f.natDegree := hmon.natDegree_map _
  have hcard : fC.roots.card = f.natDegree := by
    rw [← hnd]; exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits fC)
  -- separability, via irreducibility over `ℚ`
  have hsepQ : (f.map (Int.castRingHom ℚ)).Separable := by
    have hirrQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
      (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).1 hirr
    exact hirrQ.separable
  have hsepC : fC.Separable := by
    have hcomp : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
      RingHom.ext fun n => by simp
    have hfe : fC = (f.map (Int.castRingHom ℚ)).map (Rat.castHom ℂ) := by
      rw [Polynomial.map_map, hcomp]
    rw [hfe]
    exact hsepQ.map
  have hnodup : fC.roots.Nodup := Polynomial.nodup_roots hsepC
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S = fC.roots.toFinset := ⟨_, rfl⟩
  have hScard : S.card = f.natDegree := by
    rw [hS, Multiset.toFinset_card_of_nodup hnodup, hcard]
  have hSroot : ∀ z ∈ S, fC.eval z = 0 := by
    intro z hz
    rw [hS, Multiset.mem_toFinset] at hz
    exact Polynomial.isRoot_of_mem_roots hz
  have hSmem : ∀ z : ℂ, fC.eval z = 0 → z ∈ S := by
    intro z hz
    rw [hS, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hfC0).2 hz
  set E := S.equivFin with hE
  refine ⟨fun i => (E.symm (Fin.cast hScard.symm i) : ℂ), ?_, ?_, ?_⟩
  · intro i j hij
    have := E.symm.injective (Subtype.ext hij)
    exact Fin.cast_injective _ this
  · intro i
    exact hSroot _ (E.symm (Fin.cast hScard.symm i)).2
  · intro z hz
    refine ⟨Fin.cast hScard (E ⟨z, hSmem z hz⟩), ?_⟩
    simp


/-! ### Step 1b: the floor is the trace up to an offset in `{0, -1}` -/

/-- **Step 1b.**  If `α` is the distinguished root and all other roots have modulus `< 1`, then
`⌊α^N⌋ ∈ {V_N, V_N - 1}` for all large `N`: the tail power sum `δ_N = ∑_(i ≠ i₀) (e i)^N` tends to
`0`, and `α^N = V_N - δ_N`. -/
theorem eventually_floor_eq_traceSeq (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → ℂ) (he : ∀ i, (f.map (Int.castRingHom ℂ)).eval (e i) = 0)
    (hinj : Function.Injective e) {α : ℝ} {i₀ : Fin f.natDegree} (hi₀ : e i₀ = (α : ℂ))
    (hsmall : ∀ i, i ≠ i₀ → ‖e i‖ < 1) :
    ∀ᶠ N in atTop, ⌊α ^ N⌋ = traceSeq f N ∨ ⌊α ^ N⌋ = traceSeq f N - 1 := by
  classical
  have htend : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.univ.erase i₀, ‖e i‖ ^ N) atTop (nhds 0) := by
    have h : ∀ i ∈ Finset.univ.erase i₀,
        Tendsto (fun N : ℕ => ‖e i‖ ^ N) atTop (nhds 0) := by
      intro i hi
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (hsmall i (Finset.ne_of_mem_erase hi))
    simpa using tendsto_finset_sum (Finset.univ.erase i₀) h
  have heven : ∀ᶠ N : ℕ in atTop, (∑ i ∈ Finset.univ.erase i₀, ‖e i‖ ^ N) < 1 :=
    htend.eventually_lt_const one_pos
  filter_upwards [heven] with N hN
  have hsum : ((traceSeq f N : ℤ) : ℂ) = ∑ i, e i ^ N :=
    traceSeq_eq_root_sum f hmon e he hinj N
  have hsplit : ∑ i, e i ^ N = (α : ℂ) ^ N + ∑ i ∈ Finset.univ.erase i₀, e i ^ N := by
    rw [← hi₀]
    exact (Finset.add_sum_erase _ (fun i => e i ^ N) (Finset.mem_univ i₀)).symm
  have hnormle : ‖∑ i ∈ Finset.univ.erase i₀, e i ^ N‖
      ≤ ∑ i ∈ Finset.univ.erase i₀, ‖e i‖ ^ N :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => by rw [norm_pow])
  have hreal : |((traceSeq f N : ℤ) : ℝ) - α ^ N| < 1 := by
    have hcast : (((((traceSeq f N : ℤ) : ℝ) - α ^ N : ℝ)) : ℂ)
        = ∑ i ∈ Finset.univ.erase i₀, e i ^ N := by
      push_cast
      rw [hsum, hsplit]
      push_cast
      ring
    have h2 := congrArg norm hcast
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    rw [h2]
    exact lt_of_le_of_lt hnormle hN
  rw [abs_lt] at hreal
  have h1 : (traceSeq f N - 1 : ℤ) ≤ ⌊α ^ N⌋ := Int.le_floor.2 (by push_cast; linarith [hreal.1])
  have h2 : ⌊α ^ N⌋ < traceSeq f N + 1 := Int.floor_lt.2 (by push_cast; linarith [hreal.2])
  omega


/-! ### The transfer, for an arbitrary finite family of equations

Phase 55's `TheoremDQuadratic.exists_complex_zero_of_all_levels` is stated for exactly three
polynomials; degree `d` needs `d² + 2` of them (the entries of `T^Q - I`, plus the root-of-unity
equation for `w` and the trace equation).  Same proof, with a `Fintype`-indexed family. -/

/-- **Nullstellensatz + integrality, finite family.**  A finite family of integer polynomials with a
common zero modulo `c^k` for every `k` has a common complex zero. -/
theorem exists_complex_zero_of_family {σ ι : Type*} [Finite σ] [Fintype ι] {c : ℕ} (hc : 2 ≤ c)
    (F : ι → MvPolynomial σ ℤ)
    (hlev : ∀ k : ℕ, ∃ p : σ → ℤ, ∀ i, (c : ℤ) ^ k ∣ MvPolynomial.eval p (F i)) :
    ∃ q : σ → ℂ, ∀ i, MvPolynomial.eval₂ (Int.castRingHom ℂ) q (F i) = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ with hφ
  set G : ι → MvPolynomial σ ℚ := fun i => (F i).map φ with hG
  have hbridge : ∀ (q : MvPolynomial σ ℤ) (x : σ → ℂ),
      MvPolynomial.aeval x (q.map φ) = MvPolynomial.eval₂ (Int.castRingHom ℂ) x q := by
    intro q x
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  have hzl : MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range G)) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨i, hi⟩ := hcon x
    have hxi := hx (G i) (Ideal.subset_span ⟨i, rfl⟩)
    rw [hG] at hxi
    exact hi (by rw [← hbridge]; exact hxi)
  have htop : Ideal.span (Set.range G) = ⊤ := by
    have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) (Ideal.span (Set.range G))
    rw [hzl, MvPolynomial.vanishingIdeal_empty] at h
    exact Ideal.radical_eq_top.1 h.symm
  have hone : (1 : MvPolynomial σ ℚ) ∈ Ideal.span (Set.range G) := htop ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 hone
  choose D hD hDz using fun i => TheoremDQuadratic.exists_denominator (g i)
  set Dp : ℤ := ∏ i, D i with hDp
  have hDpne : Dp ≠ 0 := by
    rw [hDp]; exact Finset.prod_ne_zero_iff.2 fun i _ => hD i
  have hdvd : ∀ k : ℕ, (c : ℤ) ^ k ∣ Dp := by
    intro k
    obtain ⟨p, hp⟩ := hlev k
    choose m hm using fun i => hp i
    choose z hz using fun i => hDz i p
    refine ⟨∑ i, (∏ j ∈ Finset.univ.erase i, D j) * z i * m i, ?_⟩
    have hpt : ∀ q : MvPolynomial σ ℤ,
        MvPolynomial.eval (fun t => ((p t : ℤ) : ℚ)) (q.map φ)
          = ((MvPolynomial.eval p q : ℤ) : ℚ) := by
      intro q
      rw [MvPolynomial.eval_map]
      exact (MvPolynomial.eval₂_comp φ p q).symm
    have heval : (1 : ℚ) = ∑ i, MvPolynomial.eval (fun t => ((p t : ℤ) : ℚ)) (g i)
        * ((MvPolynomial.eval p (F i) : ℤ) : ℚ) := by
      have h := congrArg (MvPolynomial.eval (fun t => ((p t : ℤ) : ℚ))) hg
      rw [map_one, map_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hG, hpt (F i)]
    have hid : (∏ i, (D i : ℚ))
        = (c : ℚ) ^ k * ∑ i, (∏ j ∈ Finset.univ.erase i, (D j : ℚ)) * (z i : ℚ) * (m i : ℚ) := by
      rw [Finset.mul_sum]
      calc (∏ i, (D i : ℚ)) = (∏ i, (D i : ℚ)) * 1 := by ring
        _ = ∑ i, (∏ t, (D t : ℚ)) * (MvPolynomial.eval (fun t => ((p t : ℤ) : ℚ)) (g i)
              * ((MvPolynomial.eval p (F i) : ℤ) : ℚ)) := by rw [heval, Finset.mul_sum]
        _ = ∑ i, (c : ℚ) ^ k
              * ((∏ j ∈ Finset.univ.erase i, (D j : ℚ)) * (z i : ℚ) * (m i : ℚ)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hprod : (∏ t, (D t : ℚ))
                = (D i : ℚ) * ∏ j ∈ Finset.univ.erase i, (D j : ℚ) :=
              (Finset.mul_prod_erase _ (fun t => (D t : ℚ)) (Finset.mem_univ i)).symm
            have hFi : ((MvPolynomial.eval p (F i) : ℤ) : ℚ) = (c : ℚ) ^ k * (m i : ℚ) := by
              rw [hm i]; push_cast; ring
            rw [hprod, hFi]
            linear_combination
              ((∏ j ∈ Finset.univ.erase i, (D j : ℚ)) * (c : ℚ) ^ k * (m i : ℚ)) * (hz i)
    have hcast : ((Dp : ℤ) : ℚ)
        = ((((c : ℤ) ^ k * ∑ i, (∏ j ∈ Finset.univ.erase i, D j) * z i * m i : ℤ)) : ℚ) := by
      push_cast [hDp]
      exact hid
    exact_mod_cast hcast
  obtain ⟨k, hk⟩ : ∃ k : ℕ, |Dp| < (c : ℤ) ^ k := by
    refine ⟨(|Dp|).toNat + 1, ?_⟩
    calc |Dp| < ((|Dp|).toNat + 1 : ℕ) := by
          have := Int.toNat_of_nonneg (abs_nonneg Dp); push_cast; omega
      _ ≤ (2 : ℤ) ^ ((|Dp|).toNat + 1) := by exact_mod_cast Nat.lt_two_pow_self.le
      _ ≤ (c : ℤ) ^ ((|Dp|).toNat + 1) := by
          refine pow_le_pow_left₀ (by norm_num) ?_ _
          exact_mod_cast hc
  have := Int.le_of_dvd (abs_pos.2 hDpne) ((dvd_abs _ _).2 (hdvd k))
  omega


/-! ### Step 2a: the companion matrix is invertible mod `c` when `c ∤ f(0)`

Phase 55 computed `det (compMat a b) = b` by hand.  In degree `d` the determinant is
`(-1)^d f(0)`, but computing it is unnecessary: over a field it is enough that `C *ᵥ u = 0` forces
`u = 0`, and the kernel computation is a two-step cascade — the `i = 0` row gives
`f(0) · u_(d-1) = 0`, and then row `j + 1` gives `u_j = 0`. -/
theorem compM_det_ne_zero {K : Type*} [Field K] (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (h0 : ((f.coeff 0 : ℤ) : K) ≠ 0) : (compM K f).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set last : Fin f.natDegree := ⟨f.natDegree - 1, by omega⟩ with hlastdef
  have hjlast : ∀ j : Fin f.natDegree, ((j : ℕ) + 1 = f.natDegree) ↔ j = last := by
    intro j
    refine ⟨fun h => Fin.ext ?_, fun h => ?_⟩
    · simp only [hlastdef]; omega
    · subst h; simp only [hlastdef]; omega
  have hmv : ∀ i : Fin f.natDegree, ∑ j : Fin f.natDegree, compM K f i j * u j = 0 := by
    intro i
    have := congrFun hu i
    simpa [Matrix.mulVec, dotProduct] using this
  -- the `i = 0` row
  have hlast0 : u last = 0 := by
    have h := hmv ⟨0, by omega⟩
    have hrw : ∀ j : Fin f.natDegree,
        compM K f ⟨0, by omega⟩ j * u j
          = - (if j = last then ((f.coeff 0 : ℤ) : K) * u j else 0) := by
      intro j
      have hz : ¬ ((0 : ℕ) = (j : ℕ) + 1) := by omega
      by_cases hj : j = last
      · subst hj
        simp only [compM, Matrix.of_apply, if_neg hz, if_pos ((hjlast last).2 rfl), if_pos rfl]
        push_cast
        ring
      · have hne : ¬ ((j : ℕ) + 1 = f.natDegree) := fun h => hj ((hjlast j).1 h)
        simp [compM, hz, hne, hj]
    rw [Finset.sum_congr rfl (fun j _ => hrw j), Finset.sum_neg_distrib,
      Finset.sum_ite_eq' Finset.univ last (fun j => ((f.coeff 0 : ℤ) : K) * u j)] at h
    simp only [if_pos (Finset.mem_univ last)] at h
    have : ((f.coeff 0 : ℤ) : K) * u last = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left h0
  -- the remaining rows
  have hterm : ∀ i j : Fin f.natDegree,
      compM K f i j * u j = (if (i : ℕ) = (j : ℕ) + 1 then u j else 0) := by
    intro i j
    by_cases hj : j = last
    · subst hj; simp [compM, hlast0]
    · have hne : ¬ ((j : ℕ) + 1 = f.natDegree) := fun h => hj ((hjlast j).1 h)
      simp [compM, hne]
  have hall : ∀ j : Fin f.natDegree, u j = 0 := by
    intro j
    by_cases hj : j = last
    · subst hj; exact hlast0
    · have hne : (j : ℕ) + 1 ≠ f.natDegree := fun h => hj ((hjlast j).1 h)
      have hlt : (j : ℕ) + 1 < f.natDegree := by have := j.2; omega
      have h := hmv ⟨(j : ℕ) + 1, hlt⟩
      rw [Finset.sum_congr rfl (fun k _ => hterm ⟨(j : ℕ) + 1, hlt⟩ k)] at h
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_] at h
      · simpa using h
      · intro k _ hk
        simp only [Fin.val_mk, add_left_inj]
        exact if_neg (fun (hh : (j:ℕ) = (k:ℕ)) => hk (Fin.ext hh.symm))
  exact hu0 (funext hall)

/-! ### Step 2b: the Teichmüller congruence for `GL_d` -/

theorem glCard_pos {d p : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p) : 0 < glCard d p := by
  rw [glCard]
  refine Finset.prod_pos fun i _ => ?_
  have : p ^ (i : ℕ) < p ^ d := Nat.pow_lt_pow_right (by omega) i.isLt
  omega

/-- `C^(Q·c^n) ≡ I (mod c^(n+1))` for `Q = |GL_d(𝔽_c)|`. -/
theorem compM_pow_congr_one (f : ℤ[X]) (hd : 1 ≤ f.natDegree) {c : ℕ} (hc : c.Prime)
    (hc0 : ¬ (c : ℤ) ∣ f.coeff 0) (n : ℕ) :
    ∀ i j, (c : ℤ) ^ (n + 1) ∣
      ((compM ℤ f ^ glCard f.natDegree c) ^ (c ^ n) - 1) i j := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hbase : ∀ i j, (c : ℤ) ∣ (compM ℤ f ^ glCard f.natDegree c - 1) i j := by
    set φ : ℤ →+* ZMod c := Int.castRingHom (ZMod c) with hφ
    have hD : φ.mapMatrix (compM ℤ f) = compM (ZMod c) f := by
      simpa [RingHom.mapMatrix_apply] using compM_map φ f
    have hdetD : IsUnit (compM (ZMod c) f).det := by
      refine Ne.isUnit (compM_det_ne_zero f hd ?_)
      simpa [hφ, ZMod.intCast_zmod_eq_zero_iff_dvd] using hc0
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det (compM (ZMod c) f)).2 hdetD
    have hcard : Nat.card (GL (Fin f.natDegree) (ZMod c)) = glCard f.natDegree c := by
      rw [Matrix.card_GL_field]; simp [glCard, ZMod.card]
    have huQ : u ^ glCard f.natDegree c = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have hDQ : compM (ZMod c) f ^ glCard f.natDegree c = 1 := by
      have := congrArg (fun v : GL (Fin f.natDegree) (ZMod c) =>
        (v : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod c))) huQ
      simpa [hu] using this
    intro i j
    have h0 : ((((compM ℤ f ^ glCard f.natDegree c - 1) i j : ℤ)) : ZMod c) = 0 := by
      have hz : φ.mapMatrix (compM ℤ f ^ glCard f.natDegree c - 1) = 0 := by
        rw [map_sub, map_pow, hD, hDQ, map_one, sub_self]
      have h2 := congrFun (congrFun hz i) j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply, hφ] using h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
      intro i j
      have hcomm : Commute ((compM ℤ f ^ glCard f.natDegree c) ^ (c ^ n))
          (1 : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ) := Commute.one_right _
      have := TeichmullerCongruence.pow_congr_lift hcomm (e := n + 1) (by omega) ih i j
      rwa [one_pow, ← pow_mul, ← pow_succ] at this


/-! ### Step 2c: Cayley–Hamilton for the companion matrix

Every power `C^N` lies in the `ℤ`-span of `I, C, …, C^(d-1)`: this is what makes the torsion
system finite-dimensional (phase 55's `torsionPair` in degree 2).  The proof is the cyclic-vector
argument: `C^j *ᵥ e₀ = e_j` for `j < d`, and `C *ᵥ e_(d-1) = -(f.coeff ·)`, so two matrices
commuting with `C` and agreeing on `e₀` are equal. -/

/-- `(M *ᵥ e_j) i = M i j`. -/
theorem mulVec_single_one {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R) (j i : n) : Matrix.mulVec M (Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `C^m *ᵥ e₀ = e_m` for `m < d`. -/
theorem compM_pow_mulVec_e0 {R : Type*} [CommRing R] (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (m : ℕ) (hm : m < f.natDegree) :
    Matrix.mulVec (compM R f ^ m) (Pi.single (⟨0, by omega⟩ : Fin f.natDegree) 1)
      = Pi.single (⟨m, hm⟩ : Fin f.natDegree) 1 := by
  induction m with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ m ih =>
      have hm' : m < f.natDegree := by omega
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih hm']
      funext i
      rw [mulVec_single_one]
      have hne : ¬ ((m : ℕ) + 1 = f.natDegree) := by omega
      simp only [compM, Matrix.of_apply, Fin.val_mk, if_neg hne, sub_zero]
      by_cases h : (i : ℕ) = m + 1
      · have hi : i = (⟨m + 1, hm⟩ : Fin f.natDegree) := Fin.ext h
        subst hi
        simp
      · rw [if_neg h]
        have hne2 : i ≠ (⟨m + 1, hm⟩ : Fin f.natDegree) := fun hh => h (by rw [hh])
        simp [Pi.single_apply, hne2]

/-- `C *ᵥ e_(d-1) = -(f.coeff ·)`: the feedback column. -/
theorem compM_mulVec_last {R : Type*} [CommRing R] (f : ℤ[X]) (hd : 1 ≤ f.natDegree) :
    Matrix.mulVec (compM R f) (Pi.single (⟨f.natDegree - 1, by omega⟩ : Fin f.natDegree) 1)
      = fun i : Fin f.natDegree => -((f.coeff (i : ℕ) : ℤ) : R) := by
  funext i
  rw [mulVec_single_one]
  have hlast : (f.natDegree - 1) + 1 = f.natDegree := by omega
  have hne : ¬ ((i : ℕ) = f.natDegree - 1 + 1) := by have := i.2; omega
  simp only [compM, Matrix.of_apply, Fin.val_mk, if_neg hne, if_pos hlast, zero_sub]


/-- Two matrices commuting with `C` and agreeing on `e₀` are equal: `e₀` is a cyclic vector. -/
theorem eq_of_commute_of_mulVec_e0 {R : Type*} [CommRing R] (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (M N : Matrix (Fin f.natDegree) (Fin f.natDegree) R)
    (hM : Commute (compM R f) M) (hN : Commute (compM R f) N)
    (h : Matrix.mulVec M (Pi.single (⟨0, by omega⟩ : Fin f.natDegree) 1)
      = Matrix.mulVec N (Pi.single (⟨0, by omega⟩ : Fin f.natDegree) 1)) : M = N := by
  have key : ∀ (P : Matrix (Fin f.natDegree) (Fin f.natDegree) R),
      Commute (compM R f) P → ∀ j : Fin f.natDegree,
      Matrix.mulVec P (Pi.single j 1)
        = Matrix.mulVec (compM R f ^ (j : ℕ))
            (Matrix.mulVec P (Pi.single (⟨0, by omega⟩ : Fin f.natDegree) 1)) := by
    intro P hP j
    have hej : (Pi.single j (1 : R))
        = Matrix.mulVec (compM R f ^ (j : ℕ))
            (Pi.single (⟨0, by omega⟩ : Fin f.natDegree) 1) := by
      rw [compM_pow_mulVec_e0 f hd (j : ℕ) j.2]
    rw [hej, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    exact (hP.pow_left (j : ℕ)).symm
  ext i j
  have h1 := key M hM j
  have h2 := key N hN j
  have : Matrix.mulVec M (Pi.single j 1) = Matrix.mulVec N (Pi.single j 1) := by
    rw [h1, h2, h]
  have h3 := congrFun this i
  rwa [mulVec_single_one, mulVec_single_one] at h3

theorem commute_compM_polyMat {R : Type*} [CommRing R] (f : ℤ[X]) (x : Fin f.natDegree → R) :
    Commute (compM R f) (polyMat R f x) := by
  rw [polyMat]
  refine Commute.sum_right _ _ _ fun j _ => ?_
  exact (Commute.refl (compM R f)).pow_right (j : ℕ) |>.smul_right (x j)

theorem compM_pow_apply_zero {R : Type*} [CommRing R] (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (j i : Fin f.natDegree) :
    (compM R f ^ (j : ℕ)) i (⟨0, by omega⟩ : Fin f.natDegree) = if i = j then (1 : R) else 0 := by
  rw [← mulVec_single_one (compM R f ^ (j : ℕ)) (⟨0, by omega⟩ : Fin f.natDegree) i,
    compM_pow_mulVec_e0 f hd (j : ℕ) j.2]
  by_cases hij : i = j
  · subst hij; simp
  · have hne : ¬ ((i : ℕ) = (j : ℕ)) := fun hh => hij (Fin.ext hh)
    simp [Pi.single_apply, hij, hne]

theorem polyMat_mulVec_e0 {R : Type*} [CommRing R] (f : ℤ[X]) (hd : 1 ≤ f.natDegree)
    (x : Fin f.natDegree → R) :
    Matrix.mulVec (polyMat R f x) (Pi.single (⟨0, by omega⟩ : Fin f.natDegree) 1) = x := by
  classical
  funext i
  rw [mulVec_single_one, polyMat, Matrix.sum_apply]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
    show (x j • compM R f ^ (j : ℕ)) i (⟨0, by omega⟩ : Fin f.natDegree)
        = (if i = j then x j else 0) from by
      rw [Matrix.smul_apply, compM_pow_apply_zero f hd j i]
      by_cases hij : i = j <;> simp [hij])]
  simp

/-- **Cayley–Hamilton for the companion matrix**: `C^d = -∑_(j<d) f.coeff j · C^j`. -/
theorem compM_pow_natDegree {R : Type*} [CommRing R] (f : ℤ[X]) (hd : 1 ≤ f.natDegree) :
    compM R f ^ f.natDegree = polyMat R f (fun j => -((f.coeff (j : ℕ) : ℤ) : R)) := by
  refine eq_of_commute_of_mulVec_e0 f hd _ _
    ((Commute.refl (compM R f)).pow_right _) (commute_compM_polyMat f _) ?_
  rw [polyMat_mulVec_e0 f hd]
  have hd1 : compM R f ^ f.natDegree = compM R f * compM R f ^ (f.natDegree - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hd1, ← Matrix.mulVec_mulVec, compM_pow_mulVec_e0 f hd (f.natDegree - 1) (by omega)]
  exact compM_mulVec_last f hd

/-- Every power of `C` is a `ℤ`-combination of `I, C, …, C^(d-1)`. -/
theorem exists_coords (f : ℤ[X]) (hd : 1 ≤ f.natDegree) (N : ℕ) :
    ∃ x : Fin f.natDegree → ℤ, compM ℤ f ^ N = polyMat ℤ f x := by
  classical
  set S := Submodule.span ℤ (Set.range (fun j : Fin f.natDegree => compM ℤ f ^ (j : ℕ))) with hS
  have hmem : ∀ x : Fin f.natDegree → ℤ, polyMat ℤ f x ∈ S := by
    intro x
    rw [polyMat]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hstep : ∀ M ∈ S, M * compM ℤ f ∈ S := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [← pow_succ]
        by_cases hj : (j : ℕ) + 1 = f.natDegree
        · rw [hj, compM_pow_natDegree f hd]; exact hmem _
        · exact Submodule.subset_span ⟨⟨(j : ℕ) + 1, by have := j.2; omega⟩, rfl⟩
    | zero => simp
    | add y z _ _ ihy ihz => rw [add_mul]; exact Submodule.add_mem _ ihy ihz
    | smul a y _ ih => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ _ ih
  have hpow : compM ℤ f ^ N ∈ S := by
    induction N with
    | zero =>
        have : (1 : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ)
            = compM ℤ f ^ ((⟨0, by omega⟩ : Fin f.natDegree) : ℕ) := by simp
        rw [pow_zero, this]
        exact Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
    | succ N ih => rw [pow_succ]; exact hstep _ ih
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hpow
  exact ⟨cc, hcc.symm⟩


/-! ### Step 5: the integer system at every level, and the complex solution -/

theorem trace_polyMat_mul {R : Type*} [CommRing R] (f : ℤ[X]) (x : Fin f.natDegree → R) (s : ℕ) :
    (polyMat R f x * compM R f ^ s).trace
      = ∑ j, x j * ((traceSeq f ((j : ℕ) + s) : ℤ) : R) := by
  rw [polyMat, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, ← pow_add, ← traceSeq_cast]
  simp [smul_eq_mul]

/-- A ring hom pushed through an entry of `T^Q - 1`. -/
theorem map_polyMat_pow_sub_one {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : ℤ[X]) (x : Fin f.natDegree → R) (Q : ℕ) (i j : Fin f.natDegree) :
    φ ((polyMat R f x ^ Q - 1) i j)
      = (polyMat S f (fun t => φ (x t)) ^ Q - 1) i j := by
  have hh : RingHom.mapMatrix φ (polyMat R f x ^ Q - 1)
      = polyMat S f (fun t => φ (x t)) ^ Q - 1 := by
    rw [map_sub, map_pow, map_one, RingHom.mapMatrix_apply, polyMat_map]
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hh i) j

/-- **Steps 5–6.**  If, at every level `k`, some `n ≥ k` and some integer `w` with `w^m ≡ 1` satisfy
`V(c^n + s) ≡ w - ε (mod c^k)`, then the system has a *complex* solution: a `Q`-torsion element
`T = P(C)` of the algebra, a root of unity `w`, and the trace identity. -/
theorem exists_spectral_solution (f : ℤ[X]) (hd : 1 ≤ f.natDegree) {c : ℕ} (hc : c.Prime)
    (hc0 : ¬ (c : ℤ) ∣ f.coeff 0) {s m : ℕ} {ε : ℤ}
    (hcong : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ w : ℤ, (c : ℤ) ^ k ∣ w ^ m - 1 ∧
        (c : ℤ) ^ k ∣ traceSeq f (c ^ n + s) - (w - ε)) :
    ∃ (x : Fin f.natDegree → ℂ) (w : ℂ),
      polyMat ℂ f x ^ glCard f.natDegree c = 1 ∧ w ^ m = 1 ∧
      (polyMat ℂ f x * compM ℂ f ^ s).trace = w - (ε : ℂ) := by
  classical
  set d := f.natDegree with hdd
  set Q := glCard f.natDegree c with hQ
  set σ := Option (Fin d) with hσ
  set Xv : Fin d → MvPolynomial σ ℤ := fun j => MvPolynomial.X (some j) with hXv
  set W : MvPolynomial σ ℤ := MvPolynomial.X none with hW
  set Fsys : ((Fin d × Fin d) ⊕ Bool) → MvPolynomial σ ℤ :=
    Sum.elim (fun ij => (polyMat (MvPolynomial σ ℤ) f Xv ^ Q - 1) ij.1 ij.2)
      (fun b => if b then W ^ m - ((1 : ℤ) : MvPolynomial σ ℤ)
        else (∑ j, Xv j * ((traceSeq f ((j : ℕ) + s) : ℤ) : MvPolynomial σ ℤ)) - W
          + ((ε : ℤ) : MvPolynomial σ ℤ)) with hFsys
  -- evaluation of the system at an integer point
  have hevalZ : ∀ p : σ → ℤ,
      (∀ i j : Fin d, MvPolynomial.eval p (Fsys (Sum.inl (i, j)))
        = (polyMat ℤ f (fun t => p (some t)) ^ Q - 1) i j) ∧
      MvPolynomial.eval p (Fsys (Sum.inr true)) = (p none) ^ m - 1 ∧
      MvPolynomial.eval p (Fsys (Sum.inr false))
        = (∑ j, p (some j) * traceSeq f ((j : ℕ) + s)) - p none + ε := by
    intro p
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · have := map_polyMat_pow_sub_one (MvPolynomial.eval p) f Xv Q i j
      simpa [hFsys, hXv] using this
    · simp [hFsys, hW]
    · simp [hFsys, hXv, hW]
  -- evaluation at a complex point
  have hevalC : ∀ q : σ → ℂ,
      (∀ i j : Fin d, MvPolynomial.eval₂ (Int.castRingHom ℂ) q (Fsys (Sum.inl (i, j)))
        = (polyMat ℂ f (fun t => q (some t)) ^ Q - 1) i j) ∧
      MvPolynomial.eval₂ (Int.castRingHom ℂ) q (Fsys (Sum.inr true)) = (q none) ^ m - 1 ∧
      MvPolynomial.eval₂ (Int.castRingHom ℂ) q (Fsys (Sum.inr false))
        = (∑ j, q (some j) * ((traceSeq f ((j : ℕ) + s) : ℤ) : ℂ)) - q none + (ε : ℂ) := by
    intro q
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · have := map_polyMat_pow_sub_one (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) q) f Xv Q i j
      simpa [hFsys, hXv, ← MvPolynomial.coe_eval₂Hom] using this
    · simp [hFsys, hW, ← MvPolynomial.coe_eval₂Hom]
    · simp [hFsys, hXv, hW, ← MvPolynomial.coe_eval₂Hom]
  -- the levels
  have hlev : ∀ k : ℕ, ∃ p : σ → ℤ, ∀ i, (c : ℤ) ^ k ∣ MvPolynomial.eval p (Fsys i) := by
    intro k
    obtain ⟨n, hnk, w, hw, hV⟩ := hcong k
    obtain ⟨x, hx⟩ := exists_coords f hd (c ^ n)
    refine ⟨fun o => Option.elim o w x, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hevalZ (fun o => Option.elim o w x)
    intro i
    rcases i with ⟨i, j⟩ | b
    · rw [h1 i j]
      have hpow : polyMat ℤ f x ^ Q = (compM ℤ f ^ Q) ^ (c ^ n) := by
        rw [← hx, ← pow_mul, ← pow_mul, Nat.mul_comm]
      have hmat := compM_pow_congr_one f hd hc hc0 n i j
      rw [← hpow] at hmat
      exact dvd_trans (pow_dvd_pow (c : ℤ) (by omega)) hmat
    · rcases b with _ | _
      · rw [h3]
        have htr : (∑ j, x j * traceSeq f ((j : ℕ) + s)) = traceSeq f (c ^ n + s) := by
          have := trace_polyMat_mul f x s
          rw [← hx, ← pow_add] at this
          exact this.symm
        simp only [Option.elim]
        rw [htr]
        have : traceSeq f (c ^ n + s) - w + ε = traceSeq f (c ^ n + s) - (w - ε) := by ring
        rw [this]
        exact hV
      · rw [h2]; exact hw
  obtain ⟨q, hq⟩ := exists_complex_zero_of_family (σ := σ) hc.two_le Fsys hlev
  obtain ⟨h1, h2, h3⟩ := hevalC q
  refine ⟨fun t => q (some t), q none, ?_, ?_, ?_⟩
  · have : polyMat ℂ f (fun t => q (some t)) ^ Q - 1 = 0 := by
      ext i j
      rw [← h1 i j, hq (Sum.inl (i, j))]
      simp
    exact sub_eq_zero.1 this
  · have := hq (Sum.inr true)
    rw [h2] at this
    exact sub_eq_zero.1 this
  · have := hq (Sum.inr false)
    rw [h3] at this
    rw [trace_polyMat_mul]
    linear_combination this


/-! ### Step 7: the archimedean contradiction -/

theorem norm_eq_one_of_pow_eq_one {z : ℂ} {Q : ℕ} (hQ : 1 ≤ Q) (h : z ^ Q = 1) : ‖z‖ = 1 := by
  have hn : ‖z‖ ^ Q = 1 := by rw [← norm_pow, h, norm_one]
  rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
  · exact absurd hn (by
      have := pow_lt_one₀ (norm_nonneg z) hlt (by omega : Q ≠ 0)
      exact ne_of_lt this)
  · exact heq
  · exact absurd hn (by
      have := one_lt_pow₀ hgt (by omega : Q ≠ 0)
      exact (ne_of_lt this).symm)

/-- **Step 7 (the size argument).**  A `Q`-torsion `T = P(C)` with `tr(T C^s) = w - ε`, `w` a root
of unity and `|ε| ≤ 1`, forces `α^s ≤ 2 + (d - 1) = d + 1`. -/
theorem not_exists_spectral_of_large (f : ℤ[X]) (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : 2 ≤ f.natDegree) {α : ℝ} (hα : 1 < α)
    (hroot : (f.map (Int.castRingHom ℂ)).eval (α : ℂ) = 0)
    (hpisot : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1)
    {c : ℕ} (hc : c.Prime) {s : ℕ} (hs : (f.natDegree : ℝ) + 1 < α ^ s)
    {m : ℕ} (hm : 1 ≤ m) {ε : ℤ} (hε : |ε| ≤ 1)
    (x : Fin f.natDegree → ℂ) (w : ℂ)
    (hT : polyMat ℂ f x ^ glCard f.natDegree c = 1) (hw : w ^ m = 1)
    (htr : (polyMat ℂ f x * compM ℂ f ^ s).trace = w - (ε : ℂ)) : False := by
  classical
  have hd : 1 ≤ f.natDegree := by omega
  obtain ⟨e, hinj, he, hsurj⟩ := exists_root_enum f hmon hirr
  obtain ⟨i₀, hi₀⟩ := hsurj (α : ℂ) hroot
  have hfC0 : (f.map (Int.castRingHom ℂ)) ≠ 0 := (hmon.map (Int.castRingHom ℂ)).ne_zero
  have hsmall : ∀ k, k ≠ i₀ → ‖e k‖ < 1 := by
    intro k hk
    refine hpisot (e k) ((Polynomial.mem_roots hfC0).2 (he k)) ?_
    rw [← hi₀]
    exact fun hh => hk (hinj hh)
  -- the spectral form of the trace
  have hsp : ∑ k, polyVal x (e k) * e k ^ s = w - (ε : ℂ) := by
    rw [← trace_polyMat_mul_compM_pow f hmon e he hinj x s]; exact htr
  -- every `P(e k)` has modulus one
  have hQ1 : 1 ≤ glCard f.natDegree c := glCard_pos hd hc.two_le
  have hunit : ∀ k, ‖polyVal x (e k)‖ = 1 := fun k =>
    norm_eq_one_of_pow_eq_one hQ1 (polyVal_pow_eq_one f hmon e he hinj x hT k)
  -- split off the distinguished root
  have hsplit : polyVal x (e i₀) * e i₀ ^ s
      = (w - (ε : ℂ)) - ∑ k ∈ Finset.univ.erase i₀, polyVal x (e k) * e k ^ s := by
    rw [← hsp, ← Finset.add_sum_erase _ (fun k => polyVal x (e k) * e k ^ s)
      (Finset.mem_univ i₀)]
    ring
  -- the two sides' norms
  have hlhs : ‖polyVal x (e i₀) * e i₀ ^ s‖ = α ^ s := by
    rw [norm_mul, hunit i₀, one_mul, hi₀, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have htail : ‖∑ k ∈ Finset.univ.erase i₀, polyVal x (e k) * e k ^ s‖
      ≤ (f.natDegree : ℝ) - 1 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hb : ∀ k ∈ Finset.univ.erase i₀, ‖polyVal x (e k) * e k ^ s‖ ≤ 1 := by
      intro k hk
      rw [norm_mul, hunit k, one_mul, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (le_of_lt (hsmall k (Finset.ne_of_mem_erase hk)))
    have := Finset.sum_le_sum hb
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin] at this
    refine le_trans this ?_
    rw [nsmul_eq_mul, mul_one]
    have : ((f.natDegree - 1 : ℕ) : ℝ) = (f.natDegree : ℝ) - 1 := by
      have : (1 : ℕ) ≤ f.natDegree := hd
      push_cast [this]; ring
    rw [this]
  have hwε : ‖w - (ε : ℂ)‖ ≤ 2 := by
    have h1 : ‖w‖ = 1 := norm_eq_one_of_pow_eq_one hm hw
    have h2 : ‖(ε : ℂ)‖ ≤ 1 := by
      rw [show ((ε : ℤ) : ℂ) = ((ε : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      obtain ⟨ha, hb⟩ := abs_le.1 hε
      constructor
      · exact_mod_cast ha
      · exact_mod_cast hb
    calc ‖w - (ε : ℂ)‖ ≤ ‖w‖ + ‖(ε : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have hfinal : α ^ s ≤ (f.natDegree : ℝ) + 1 := by
    rw [← hlhs, hsplit]
    calc ‖(w - (ε : ℂ)) - ∑ k ∈ Finset.univ.erase i₀, polyVal x (e k) * e k ^ s‖
        ≤ ‖w - (ε : ℂ)‖ + ‖∑ k ∈ Finset.univ.erase i₀, polyVal x (e k) * e k ^ s‖ :=
          norm_sub_le _ _
      _ ≤ 2 + ((f.natDegree : ℝ) - 1) := by linarith
      _ = (f.natDegree : ℝ) + 1 := by ring
  linarith


/-! ### Steps 1c–1d: growth, the filter and the stuck alternation (degree `d`) -/

/-- Beyond a threshold the floors of `α^N` strictly increase: `α^(N+1) ≥ α^N + 1` once
`α^N (α - 1) ≥ 1`.  (In degree `d` one cannot ask for `α ≥ φ`: the plastic number is smaller.) -/
theorem exists_floor_strictMono {α : ℝ} (hα : 1 < α) :
    ∃ N₀ : ℕ, ∀ N M : ℕ, N₀ ≤ N → N < M → ⌊α ^ N⌋ < ⌊α ^ M⌋ := by
  have hten : Tendsto (fun N : ℕ => α ^ N) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hα
  obtain ⟨N₀, hN₀⟩ := (hten.eventually_ge_atTop (1 / (α - 1))).exists_forall_of_atTop
  refine ⟨N₀, fun N M hN hNM => ?_⟩
  have hα0 : (0 : ℝ) < α := by linarith
  have hstep : α ^ N + 1 ≤ α ^ (N + 1) := by
    have h1 : 1 / (α - 1) ≤ α ^ N := hN₀ N hN
    have h2 : 1 ≤ α ^ N * (α - 1) := by
      rw [div_le_iff₀ (by linarith)] at h1
      linarith
    have : α ^ (N + 1) = α ^ N * α := by ring
    rw [this]; nlinarith
  have hmono : α ^ (N + 1) ≤ α ^ M := pow_le_pow_right₀ (le_of_lt hα) (by omega)
  have : (⌊α ^ N⌋ : ℤ) + 1 ≤ ⌊α ^ M⌋ := by
    have h3 : (⌊α ^ N⌋ : ℝ) + 1 ≤ α ^ M := by
      have := Int.floor_le (α ^ N)
      linarith
    exact Int.le_floor.2 (by push_cast; linarith)
  omega

/-- The floors along `c^n + s` exceed any bound eventually. -/
theorem exists_floor_gt {α : ℝ} (hα : 1 < α) {c : ℕ} (hc : 2 ≤ c) (s : ℕ) (B : ℤ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → B < ⌊α ^ (c ^ n + s)⌋ := by
  have hten : Tendsto (fun N : ℕ => α ^ N) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hα
  have hle : ∀ n : ℕ, n ≤ c ^ n + s := by
    intro n
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ n ≤ c ^ n := Nat.pow_le_pow_left hc n
    omega
  have hcomp : Tendsto (fun n : ℕ => α ^ (c ^ n + s)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) hten
    exact pow_le_pow_right₀ (le_of_lt hα) (hle n)
  obtain ⟨n₀, hn₀⟩ := (hcomp.eventually_gt_atTop ((B : ℝ) + 1)).exists_forall_of_atTop
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hn₀ n hn
  have : (B : ℝ) + 1 < α ^ (c ^ n + s) := h
  have := Int.le_floor.2 (show ((B + 1 : ℤ) : ℝ) ≤ α ^ (c ^ n + s) by push_cast; linarith)
  omega

theorem orderOf_dvd_glCard_d {d p : ℕ} (hp : p.Prime) (D : GL (Fin d) (ZMod p)) :
    orderOf D ∣ glCard d p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GL (Fin d) (ZMod p)) = glCard d p := by
    rw [Matrix.card_GL_field]; simp [glCard, ZMod.card]
  rw [← hcard]
  exact orderOf_dvd_natCard D

/-- Trace congruence from an order bound. -/
theorem traceSeq_congr_of_order (f : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (hpdet : ¬ (p : ℤ) ∣ (compM ℤ f).det) {M : ℕ}
    (hord : ∀ D : GL (Fin f.natDegree) (ZMod p),
      (D : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod p)) =
        (Int.castRingHom (ZMod p)).mapMatrix (compM ℤ f) → orderOf D ∣ M)
    {N N' : ℕ} (hle : N ≤ N') (hdvd : M ∣ N' - N) :
    (p : ℤ) ∣ traceSeq f N' - traceSeq f N :=
  TheoremDGround.dvd_trace_sub_of_orderOf_dvd (compM ℤ f) hp hpdet hle
    (fun D hD => (hord D hD).trans hdvd)

/-- **The filter.**  With `A = v_c(M) ≤ n`, the values `V(c^(n+kj) + s)` are all congruent to
`V(c^n + s)` mod `p`, for a fixed period `j ≥ 1`. -/
theorem traceSeq_stuck_period (f : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (hpdet : ¬ (p : ℤ) ∣ (compM ℤ f).det) {c : ℕ} (hc : c.Prime) {M : ℕ} (hM0 : 0 < M)
    (hord : ∀ D : GL (Fin f.natDegree) (ZMod p),
      (D : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod p)) =
        (Int.castRingHom (ZMod p)).mapMatrix (compM ℤ f) → orderOf D ∣ M)
    {n : ℕ} (hA : M.factorization c ≤ n) (s : ℕ) :
    ∃ j, 1 ≤ j ∧ ∀ k, 1 ≤ k →
      (p : ℤ) ∣ traceSeq f (c ^ (n + k * j) + s) - traceSeq f (c ^ n + s) := by
  set A := M.factorization c with hAdef
  set o := M / c ^ A with hodef
  have hsplit : c ^ A * o = M := by
    rw [hAdef, hodef]; exact Nat.ordProj_mul_ordCompl_eq_self M c
  have hcno : ¬ c ∣ o := by rw [hodef, hAdef]; exact Nat.not_dvd_ordCompl hc hM0.ne'
  have hopos : 0 < o := by
    rcases Nat.eq_zero_or_pos o with h | h
    · rw [h, mul_zero] at hsplit; omega
    · exact h
  have hcop : Nat.Coprime c o := (Nat.Prime.coprime_iff_not_dvd hc).2 hcno
  refine ⟨o.totient, Nat.totient_pos.2 hopos, fun k hk => ?_⟩
  have hpow : c ^ (k * o.totient) % o = 1 % o := by
    have h1 : c ^ o.totient ≡ 1 [MOD o] := Nat.ModEq.pow_totient hcop
    have := h1.pow k
    rw [← pow_mul, one_pow] at this
    rw [mul_comm k o.totient]
    exact this
  obtain ⟨Y, hY⟩ : ∃ Y, c ^ (k * o.totient) = Y + 1 := by
    have : 1 ≤ c ^ (k * o.totient) := Nat.one_le_pow _ _ hc.pos
    exact ⟨c ^ (k * o.totient) - 1, by omega⟩
  have hoY : o ∣ Y := by
    have h2 : Nat.ModEq o 1 (c ^ (k * o.totient)) := hpow.symm
    have h3 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ c ^ (k * o.totient))).1 h2
    rw [hY] at h3
    simpa using h3
  have hNN : c ^ (n + k * o.totient) + s - (c ^ n + s) = c ^ n * Y := by
    rw [pow_add, hY]; ring_nf; omega
  have hle : c ^ n + s ≤ c ^ (n + k * o.totient) + s := by
    have : c ^ n ≤ c ^ (n + k * o.totient) :=
      Nat.pow_le_pow_right hc.one_le (by omega)
    omega
  refine traceSeq_congr_of_order f hp hpdet hord hle ?_
  rw [hNN, ← hsplit]
  exact Nat.mul_dvd_mul (pow_dvd_pow c hA) hoY

/-- **Step 1d (the stuck alternation).**  At a stuck `n` the offset `ε` alternates along an
arithmetic progression: otherwise the prime `p_n` divides the strictly larger prime `p_(n+kj)`. -/
theorem stuck_alternation_general (f : ℤ[X]) {α : ℝ} (hα : 1 < α) {c : ℕ} (hc : c.Prime)
    {s n₀ : ℕ} (ε : ℕ → Bool) (off : Bool → ℤ)
    (hoff : ∀ m, n₀ ≤ m → ⌊α ^ (c ^ m + s)⌋ = traceSeq f (c ^ m + s) + off (ε m))
    (hprime : ∀ m, n₀ ≤ m → (⌊α ^ (c ^ m + s)⌋₊).Prime)
    (hpdet : ∀ m, n₀ ≤ m → ¬ ((⌊α ^ (c ^ m + s)⌋₊ : ℕ) : ℤ) ∣ (compM ℤ f).det)
    (hgrow : ∀ m m', n₀ ≤ m → m < m' → ⌊α ^ (c ^ m + s)⌋ < ⌊α ^ (c ^ m' + s)⌋)
    {n : ℕ} (hn : n₀ ≤ n)
    (hstuck : padicValNat c (glCard f.natDegree (⌊α ^ (c ^ n + s)⌋₊)) ≤ n) :
    ∃ j, 1 ≤ j ∧ ∀ k, 1 ≤ k → ε (n + k * j) ≠ ε n := by
  classical
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hfl : ∀ m : ℕ, ((⌊α ^ (c ^ m + s)⌋₊ : ℕ) : ℤ) = ⌊α ^ (c ^ m + s)⌋ := fun m =>
    Int.natCast_floor_eq_floor (by positivity)
  have hPp : (⌊α ^ (c ^ n + s)⌋₊).Prime := hprime n hn
  have hord : ∀ D : GL (Fin f.natDegree) (ZMod (⌊α ^ (c ^ n + s)⌋₊)),
      (D : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod (⌊α ^ (c ^ n + s)⌋₊))) =
        (Int.castRingHom (ZMod (⌊α ^ (c ^ n + s)⌋₊))).mapMatrix (compM ℤ f) →
        orderOf D ∣ glCard f.natDegree (⌊α ^ (c ^ n + s)⌋₊) :=
    fun D _ => orderOf_dvd_glCard_d hPp D
  have hA : (glCard f.natDegree (⌊α ^ (c ^ n + s)⌋₊)).factorization c ≤ n := by
    rwa [Nat.factorization_def _ hc]
  have hQpos : 0 < glCard f.natDegree (⌊α ^ (c ^ n + s)⌋₊) := by
    rcases Nat.eq_zero_or_pos f.natDegree with h | h
    · rw [glCard, h]; simp
    · exact glCard_pos h hPp.two_le
  obtain ⟨j, hj1, hjd⟩ :=
    traceSeq_stuck_period f hPp (hpdet n hn) hc hQpos hord hA s
  refine ⟨j, hj1, fun k hk => ?_⟩
  intro heq
  have hmn : n < n + k * j := by
    have : 1 ≤ k * j := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hm0 : n₀ ≤ n + k * j := by omega
  have he1 := hoff (n + k * j) hm0
  have he2 := hoff n hn
  have hdvd : ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) ∣
      ⌊α ^ (c ^ (n + k * j) + s)⌋ - ⌊α ^ (c ^ n + s)⌋ := by
    rw [he1, he2, heq]
    simpa using hjd k hk
  rw [← hfl (n + k * j), ← hfl n] at hdvd
  have hQp : (⌊α ^ (c ^ (n + k * j) + s)⌋₊).Prime := hprime _ hm0
  have hPQ : ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) ∣ ((⌊α ^ (c ^ (n + k * j) + s)⌋₊ : ℕ) : ℤ) := by
    have := dvd_add hdvd (dvd_refl ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ))
    simpa using this
  have hnat : (⌊α ^ (c ^ n + s)⌋₊) ∣ (⌊α ^ (c ^ (n + k * j) + s)⌋₊) := by exact_mod_cast hPQ
  have heqPQ := (Nat.prime_dvd_prime_iff_eq hPp hQp).1 hnat
  have hlt := hgrow n (n + k * j) hn hmn
  rw [← hfl n, ← hfl (n + k * j), heqPQ] at hlt
  exact lt_irrefl _ hlt


/-! ### Step 1f: pigeonhole over a finite type -/

/-- If arbitrarily late `n` carry *some* value of a finite type, one value carries arbitrarily
late `n`. -/
theorem exists_val_frequently {T : Type*} [Fintype T] {Q : ℕ → T → Prop}
    (h : ∀ m : ℕ, ∃ n, m ≤ n ∧ ∃ t, Q n t) : ∃ t, ∀ m : ℕ, ∃ n, m ≤ n ∧ Q n t := by
  classical
  by_contra hcon
  push_neg at hcon
  choose bd hbd using hcon
  obtain ⟨n, hn, t, hQ⟩ := h (Finset.univ.sup bd)
  exact hbd t n (le_trans (Finset.le_sup (Finset.mem_univ t)) hn) hQ

/-- Reading the real root of `f` as a root of `f` over `ℂ`. -/
theorem eval_map_complex_of_aeval {f : ℤ[X]} {α : ℝ} (hroot : aeval α f = 0) :
    (f.map (Int.castRingHom ℂ)).eval ((α : ℝ) : ℂ) = 0 := by
  have h1 : Polynomial.eval₂ (Int.castRingHom ℝ) α f = 0 := by
    simpa [Polynomial.aeval_def] using hroot
  have h2 := Polynomial.hom_eval₂ f (Int.castRingHom ℝ) Complex.ofRealHom α
  rw [h1, map_zero] at h2
  have hcomp : (Complex.ofRealHom).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext fun n => by simp
  rw [Polynomial.eval_map, ← hcomp]
  exact h2.symm

/-- `det C ≠ 0` when `f(0) ≠ 0`. -/
theorem compM_det_ne_zero_int (f : ℤ[X]) (hd : 1 ≤ f.natDegree) (h0 : f.coeff 0 ≠ 0) :
    (compM ℤ f).det ≠ 0 := by
  intro h
  refine compM_det_ne_zero (K := ℚ) f hd (by simpa using h0) ?_
  have hmap : (compM ℤ f).map (Int.castRingHom ℚ) = compM ℚ f := compM_map _ f
  have := RingHom.map_det (Int.castRingHom ℚ) (compM ℤ f)
  rw [RingHom.mapMatrix_apply, hmap] at this
  rw [← this, h, map_zero]

/-- **Theorem D, every degree** (all roots `c`-units). -/
theorem floor_pow_prime_pow_add_not_prime_general (f : ℤ[X]) (hmon : f.Monic)
    (hirr : Irreducible f) (hdeg : 2 ≤ f.natDegree) {α : ℝ} (hroot : aeval α f = 0)
    (hα : 1 < α)
    (hpisot : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1)
    {c : ℕ} (hc : c.Prime) (hc0 : ¬ (c : ℤ) ∣ f.coeff 0)
    {s : ℕ} (hs : (f.natDegree : ℝ) + 1 < α ^ s) :
    ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime := by
  classical
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 hcon
  set d := f.natDegree with hdd
  have hd : 1 ≤ d := by omega
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hfl : ∀ m : ℕ, ((⌊α ^ (c ^ m + s)⌋₊ : ℕ) : ℤ) = ⌊α ^ (c ^ m + s)⌋ := fun m =>
    Int.natCast_floor_eq_floor (by positivity)
  have hcoeff0 : f.coeff 0 ≠ 0 := by
    intro h; rw [h] at hc0; exact hc0 (dvd_zero _)
  have hdet0 : (compM ℤ f).det ≠ 0 := compM_det_ne_zero_int f hd hcoeff0
  -- the root enumeration, with `α` distinguished
  have hrootC := eval_map_complex_of_aeval hroot
  obtain ⟨e, hinj, he, hsurj⟩ := exists_root_enum f hmon hirr
  obtain ⟨i₀, hi₀⟩ := hsurj _ hrootC
  have hfC0 : (f.map (Int.castRingHom ℂ)) ≠ 0 := (hmon.map (Int.castRingHom ℂ)).ne_zero
  have hsmall : ∀ k, k ≠ i₀ → ‖e k‖ < 1 := by
    intro k hk
    refine hpisot (e k) ((Polynomial.mem_roots hfC0).2 (he k)) ?_
    rw [← hi₀]
    exact fun hh => hk (hinj hh)
  -- thresholds
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    (eventually_floor_eq_traceSeq f hmon e he hinj hi₀ hsmall)
  obtain ⟨N₂, hN₂⟩ := exists_floor_strictMono hα
  obtain ⟨N₃, hN₃⟩ := exists_floor_gt hα hc.two_le s (|(compM ℤ f).det| + (c : ℤ) + 1)
  have hcm : ∀ m : ℕ, m ≤ c ^ m + s := by
    intro m
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ m ≤ c ^ m := Nat.pow_le_pow_left hc.two_le m
    omega
  set n₀ := max (max n₁ N₃) (max N₁ N₂) with hn₀def
  have hprime : ∀ m, n₀ ≤ m → (⌊α ^ (c ^ m + s)⌋₊).Prime := by
    intro m hm
    have := hn₁ m (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm)
    simpa using this
  have hbig : ∀ m, n₀ ≤ m → |(compM ℤ f).det| + (c : ℤ) + 1 < ⌊α ^ (c ^ m + s)⌋ := fun m hm =>
    hN₃ m (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm)
  have hpdet : ∀ m, n₀ ≤ m → ¬ ((⌊α ^ (c ^ m + s)⌋₊ : ℕ) : ℤ) ∣ (compM ℤ f).det := by
    intro m hm hdvd
    have h1 := Int.le_of_dvd (abs_pos.2 hdet0) ((dvd_abs _ _).2 hdvd)
    have h2 := hbig m hm
    rw [← hfl m] at h2
    omega
  have hnec : ∀ m, n₀ ≤ m → (⌊α ^ (c ^ m + s)⌋₊) ≠ c := by
    intro m hm heq
    have h2 := hbig m hm
    rw [← hfl m, heq] at h2
    have : (0 : ℤ) ≤ |(compM ℤ f).det| := abs_nonneg _
    omega
  have hgrow : ∀ m m', n₀ ≤ m → m < m' → ⌊α ^ (c ^ m + s)⌋ < ⌊α ^ (c ^ m' + s)⌋ := by
    intro m m' hm hmm
    refine hN₂ _ _ ?_ ?_
    · exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm) (hcm m)
    · have : c ^ m < c ^ m' := Nat.pow_lt_pow_right hc.one_lt hmm
      omega
  -- the offset
  set εf : ℕ → Bool := fun m => decide (⌊α ^ (c ^ m + s)⌋ = traceSeq f (c ^ m + s)) with hεfdef
  set off : Bool → ℤ := fun b => if b then 0 else -1 with hoffdef
  have hoff : ∀ m, n₀ ≤ m → ⌊α ^ (c ^ m + s)⌋ = traceSeq f (c ^ m + s) + off (εf m) := by
    intro m hm
    have hNm : N₁ ≤ c ^ m + s :=
      le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm) (hcm m)
    rcases hN₁ (c ^ m + s) hNm with h | h
    · have hεt : εf m = true := by rw [hεfdef]; exact decide_eq_true h
      have hz : off (εf m) = 0 := by rw [hεt, hoffdef]; simp
      rw [hz]; omega
    · have hne : ⌊α ^ (c ^ m + s)⌋ ≠ traceSeq f (c ^ m + s) := by omega
      have hεt : εf m = false := by rw [hεfdef]; exact decide_eq_false hne
      have hz : off (εf m) = -1 := by rw [hεt, hoffdef]; simp
      rw [hz]; omega
  -- good indices are unbounded
  have hgood := TheoremDQuadratic.good_unbounded (ε := εf)
    (Stuck := fun n => padicValNat c (glCard d (⌊α ^ (c ^ n + s)⌋₊)) ≤ n) (n₀ := n₀)
    (fun n hn hstuck =>
      stuck_alternation_general f hα hc εf off hoff hprime hpdet hgrow hn hstuck)
  -- the window at each good index, with datum in a fixed finite set
  have hwin : ∀ m : ℕ, ∃ n, m ≤ n ∧ ∃ t : Fin (d + 1) × Bool,
      1 ≤ (t.1 : ℕ) ∧ (c : ℤ) ^ (n / d) ∣ ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) ^ (t.1 : ℕ) - 1
        ∧ εf n = t.2 ∧ n₀ ≤ n := by
    intro m
    obtain ⟨n, hn0, hnm, hns⟩ := hgood m
    obtain ⟨i, hi1, hid, hidvd⟩ := TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard
      hc (hprime n hn0) (hnec n hn0) hd (not_le.1 hns)
    exact ⟨n, hnm, (⟨i, by omega⟩, εf n), by simpa using hi1, by simpa using hidvd, rfl, hn0⟩
  obtain ⟨t, hfreq⟩ := exists_val_frequently hwin
  -- the congruence hypothesis, at every level
  have hcong : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ w : ℤ, (c : ℤ) ^ k ∣ w ^ (t.1 : ℕ) - 1 ∧
      (c : ℤ) ^ k ∣ traceSeq f (c ^ n + s) - (w - off t.2) := by
    intro k
    obtain ⟨n, hn, h1, hdvd, hε, hn0⟩ := hfreq (k * d + k)
    refine ⟨n, by omega, ((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ), ?_, ?_⟩
    · refine dvd_trans (pow_dvd_pow (c : ℤ) ?_) hdvd
      have : k * d ≤ n := by omega
      exact Nat.le_div_iff_mul_le (by omega) |>.2 (by omega)
    · have hh := hoff n hn0
      rw [hε] at hh
      have hzero : traceSeq f (c ^ n + s) - (((⌊α ^ (c ^ n + s)⌋₊ : ℕ) : ℤ) - off t.2) = 0 := by
        rw [hfl n]
        omega
      rw [hzero]
      exact dvd_zero _
  -- the spectral solution, and the size contradiction
  obtain ⟨x, w, hT, hw, htr⟩ := exists_spectral_solution f hd hc hc0 hcong
  exact not_exists_spectral_of_large f hmon hirr hdeg hα hrootC hpisot hc hs
    (by have : 1 ≤ (t.1 : ℕ) := by
          obtain ⟨n, _, h1, _⟩ := hfreq 0
          exact h1
        exact this)
    (by rw [hoffdef]; rcases t.2 with _ | _ <;> simp) x w hT hw htr

/-- **Degree 3 (Saito's "especially"):** the plastic number, every prime `c`, shift `5`. -/
theorem plastic_floor_pow_prime_pow_add_not_prime {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hρ1 : 1 < ρ)
    {c : ℕ} (hc : c.Prime) :
    ∃ᶠ n in atTop, ¬ (⌊ρ ^ (c ^ n + 5)⌋₊).Prime := by
  sorry

end LeanFormalizations.Mills.TheoremDGeneral

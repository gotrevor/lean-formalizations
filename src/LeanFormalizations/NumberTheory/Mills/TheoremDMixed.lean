/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDGeneral

/-!
# Phase 57: Theorem D in full (`PROOF-THEOREM-D.md` draft 2) — some root a `c`-unit suffices

Phase 56 proved Theorem D when **every** root of `f` is a `c`-unit (`c ∤ f(0)`).  The paper proof
needs only that **some** root is (`f ≢ X^d (mod c)`).  The excluded class `f ≡ X^d (mod c)` is
provably invisible to the method (Proposition D′), so this is the method's full reach.

## Route (extend phase 56)
1. **Limit matrix with non-unit roots.**  `T := C^(c^n)` (for `n` large, along a class) satisfies
   `T^(Q+1) ≡ T (mod c^k)` instead of `T^Q ≡ I`: on unit eigen-directions it is Teichmüller
   (`u^Q = 1`), on non-unit ones it tends to `0`.  Also `tr(T^Q) ≡ m (mod c^k)`, where
   `1 ≤ m ≤ d` is the number of unit roots (the rank of the idempotent `T^Q`; `m ≥ 1` exactly because
   `f ≢ X^d (mod c)`; `m` = degree of the largest factor of `f mod c` coprime to `X`, i.e.
   `d − (multiplicity of X in f mod c)`).  Encode both, plus the window equation, as the integer
   system at level `k`, exactly as phase 56 does.
2. **Transfer** (phase 55/56 Nullstellensatz): a complex solution `(x_j, w)`, `T = P(C)`, with
   eigenvalues `u_k = P(α_k) ∈ {0} ∪ μ_Q` and exactly `m ≥ 1` of them nonzero (`Σ u_k^Q = m`).
3. **One automorphism** (the new step): pick `k*` with `u_(k*) ≠ 0` and `σ ∈ Aut(ℂ)` with
   `σ(α_(k*)) = α` (`f` irreducible over `ℚ`, so `Gal` is transitive on the roots; extend to `ℂ`
   via `IsAlgClosed` lifting, e.g. `IsAlgClosed.lift` / `AlgEquiv` extension of the splitting field,
   or `Polynomial.Gal` + `Complex` automorphism extension).  `σ` applied to the complex solution
   is again a solution of the same *integer* system (`MvPolynomial.eval` commutes with ring homs:
   phase 55's `torsionPair_map` pattern), now with a nonzero eigenvalue at `α`.
4. **Size:** `α^s ≤ |w − ε| + Σ_(k≥2) |α_k|^s < d + 1`, contradiction (phase 56's final step).

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
Decomposing into named sub-lemmas is progress.
-/

namespace LeanFormalizations.Mills.TheoremDMixed

open Filter Polynomial LeanFormalizations.Mills.ThreeAdic
  LeanFormalizations.Mills.TheoremDGeneral

/-! ### Step 0: eventual periodicity of powers in a finite monoid

The mixed case has no `Q` with `C^Q ≡ I (mod c)` — `C mod c` need not be invertible.  What survives
is *eventual* periodicity in the finite monoid `Mat_d(𝔽_c)`: there are `a, Q ≥ 1` with
`D^(a+Q) = D^a`, and then `D^L` is idempotent for `L := a·Q`. -/

/-- Eventual periodicity of the powers of an element of a finite monoid. -/
theorem exists_period {M : Type*} [Monoid M] [Finite M] (D : M) :
    ∃ a Q : ℕ, 1 ≤ a ∧ 1 ≤ Q ∧ D ^ (a + Q) = D ^ a := by
  obtain ⟨i, j, hij, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => D ^ (n + 1))
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨i + 1, j - i, by omega, by omega, ?_⟩
    have hrw : i + 1 + (j - i) = j + 1 := by omega
    rw [hrw]; exact hEq.symm
  · refine ⟨j + 1, i - j, by omega, by omega, ?_⟩
    have hrw : j + 1 + (i - j) = i + 1 := by omega
    rw [hrw]; exact hEq

/-- Past the pre-period the powers are `Q`-periodic. -/
theorem pow_add_period {M : Type*} [Monoid M] {D : M} {a Q : ℕ}
    (h : D ^ (a + Q) = D ^ a) (t u : ℕ) : D ^ (a + t + u * Q) = D ^ (a + t) := by
  induction u with
  | zero => simp
  | succ u ih =>
      have hrw : a + t + (u + 1) * Q = (a + Q) + (t + u * Q) := by ring
      rw [hrw, pow_add, h, ← pow_add, ← ih]
      congr 1
      ring

/-- **The idempotent power.**  With `L := a·Q` every positive multiple of `L` gives the same
element, so `D^L` is idempotent. -/
theorem pow_mul_period {M : Type*} [Monoid M] {D : M} {a Q : ℕ} (ha : 1 ≤ a) (hQ : 1 ≤ Q)
    (h : D ^ (a + Q) = D ^ a) {j : ℕ} (hj : 1 ≤ j) : D ^ (a * Q * j) = D ^ (a * Q) := by
  have hbase : D ^ (a * Q) = D ^ (a + (a * Q - a)) := by
    congr 1
    have : a ≤ a * Q := Nat.le_mul_of_pos_right a hQ
    omega
  have hgoal : a * Q * j = a + (a * Q - a) + (a * (j - 1)) * Q := by
    have h1 : a ≤ a * Q := Nat.le_mul_of_pos_right a hQ
    have h3 : a + (a * Q - a) = a * Q := by omega
    rw [h3]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hgoal, pow_add_period h, hbase]

/-! ### Step 0b: the companion matrix is nilpotent only for `f ≡ X^d`

This is where the hypothesis `f ≢ X^d (mod c)` enters, and it is the *only* place it is used:
the idempotent `D^L` is nonzero exactly because `D = C mod c` is not nilpotent. -/

/-- The companion matrix is a root of `f` read over `K` (Cayley–Hamilton, from the cyclic
vector `e₀`). -/
theorem aeval_compM_self {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (hd : 1 ≤ f.natDegree) :
    Polynomial.aeval (compM K f) (f.map (Int.castRingHom K)) = 0 := by
  classical
  set g := f.map (Int.castRingHom K) with hg
  have hgm : g.Monic := hmon.map _
  have hgd : g.natDegree = f.natDegree := hmon.natDegree_map _
  have hlt : g.natDegree < f.natDegree + 1 := by omega
  rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range_succ]
  have hcd : g.coeff f.natDegree = 1 := by
    have := hgm.coeff_natDegree
    rwa [hgd] at this
  rw [hcd, one_smul]
  rw [compM_pow_natDegree f hd, polyMat]
  rw [← Fin.sum_univ_eq_sum_range (fun i => g.coeff i • compM K f ^ i) f.natDegree]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hcj : g.coeff (j : ℕ) = ((f.coeff (j : ℕ) : ℤ) : K) := by
    rw [hg, Polynomial.coeff_map]; rfl
  rw [hcj]
  module

/-- Anything annihilating the companion matrix is a multiple of `f mod c`. -/
theorem dvd_of_aeval_compM_eq_zero {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (hd : 1 ≤ f.natDegree) (r : K[X]) (h : Polynomial.aeval (compM K f) r = 0) :
    (f.map (Int.castRingHom K)) ∣ r := by
  classical
  set g := f.map (Int.castRingHom K) with hg
  have hgm : g.Monic := hmon.map _
  have hgd : g.natDegree = f.natDegree := hmon.natDegree_map _
  set ρ := r %ₘ g with hρ
  have hdec : ρ + g * (r /ₘ g) = r := Polynomial.modByMonic_add_div r g
  have hz : Polynomial.aeval (compM K f) ρ = 0 := by
    have := congrArg (Polynomial.aeval (compM K f)) hdec
    rw [map_add, map_mul, aeval_compM_self f hmon hd, zero_mul, add_zero, h] at this
    exact this
  have hdegρ : ρ.natDegree < f.natDegree := by
    rcases eq_or_ne ρ 0 with h0 | h0
    · rw [h0]; simp only [Polynomial.natDegree_zero]; omega
    · have hlt : ρ.degree < g.degree := Polynomial.degree_modByMonic_lt r hgm
      have : ρ.natDegree < g.natDegree :=
        Polynomial.natDegree_lt_natDegree h0 hlt
      omega
  have hpm : Polynomial.aeval (compM K f) ρ
      = polyMat K f (fun j : Fin f.natDegree => ρ.coeff (j : ℕ)) := by
    rw [Polynomial.aeval_eq_sum_range' (by omega : ρ.natDegree < f.natDegree), polyMat,
      ← Fin.sum_univ_eq_sum_range (fun i => ρ.coeff i • compM K f ^ i) f.natDegree]
  have hcoeff : ∀ j : Fin f.natDegree, ρ.coeff (j : ℕ) = 0 := by
    have := polyMat_mulVec_e0 f hd (fun j : Fin f.natDegree => ρ.coeff (j : ℕ))
    rw [← hpm, hz] at this
    intro j
    have h2 := congrFun this.symm j
    simpa using h2
  have hρ0 : ρ = 0 := by
    refine Polynomial.ext fun i => ?_
    rcases lt_or_ge i f.natDegree with hi | hi
    · simpa using hcoeff ⟨i, hi⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [← hdec, hρ0, zero_add]
  exact Dvd.intro _ rfl

/-- **The nilpotency criterion.**  A vanishing power of the companion matrix forces
`f ≡ X^d (mod c)`. -/
theorem map_eq_X_pow_of_compM_pow_eq_zero {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (hd : 1 ≤ f.natDegree) {M : ℕ} (hM : compM K f ^ M = 0) :
    f.map (Int.castRingHom K) = Polynomial.X ^ f.natDegree := by
  classical
  set g := f.map (Int.castRingHom K) with hg
  have hgm : g.Monic := hmon.map _
  have hgd : g.natDegree = f.natDegree := hmon.natDegree_map _
  have hdvd : g ∣ (Polynomial.X : K[X]) ^ M := by
    refine dvd_of_aeval_compM_eq_zero f hmon hd _ ?_
    rw [map_pow, Polynomial.aeval_X, hM]
  obtain ⟨i, hiM, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X M).1 hdvd
  have heq : g = (Polynomial.X : K[X]) ^ i :=
    Polynomial.eq_of_monic_of_associated hgm (Polynomial.monic_X_pow i) hassoc
  have hid : i = f.natDegree := by
    have := congrArg Polynomial.natDegree heq
    rw [hgd, Polynomial.natDegree_X_pow] at this
    exact this.symm
  rw [heq, hid]


/-! ### Step 1: the mixed limit matrix

`T := C^(L·c^n)` replaces phase 56's `C^(Q·c^n)`.  It is no longer `Q`-torsion — on the
non-unit eigen-directions it tends to `0` — but it satisfies `T^(Q+1) = T`, and the idempotent
`T^Q` is *nonzero*, which is recorded by the single polynomial equation `det (1 - T^Q) = 0`.
Using the determinant rather than `tr (T^Q) = m` is what removes the need for the Hensel
factorization of `f mod c` and for any rank computation. -/


/-- Ring homs commute with matrix powers. -/
theorem map_matrix_pow {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Matrix n n R) (N : ℕ) : (M ^ N).map φ = (M.map φ) ^ N := by
  simpa [RingHom.mapMatrix_apply] using map_pow (RingHom.mapMatrix φ) M N

/-- Ring homs commute with matrix subtraction. -/
theorem map_matrix_sub {n R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M N : Matrix n n R) : (M - N).map φ = M.map φ - N.map φ := by
  ext i j; simp [Matrix.map_apply]

/-- Idempotents in `ZMod (c^k)` are trivial (`c` prime). -/
theorem zmod_idem_eq_zero_or_one {c : ℕ} (hc : c.Prime) (k : ℕ) (t : ZMod (c ^ k))
    (h : t * t = t) : t = 0 ∨ t = 1 := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ZMod (c ^ k)) = t :=
    ⟨ZMod.cast t, ZMod.intCast_zmod_cast t⟩
  have hp : Prime (c : ℤ) := Int.prime_iff_natAbs_prime.2 (by simpa using hc)
  have hdvd : (c : ℤ) ^ k ∣ z * (z - 1) := by
    have h0 : ((z * (z - 1) : ℤ) : ZMod (c ^ k)) = 0 := by
      push_cast
      rw [hz]
      linear_combination h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (c ^ k)).1 h0
    exact_mod_cast this
  by_cases hcz : (c : ℤ) ∣ z
  · refine Or.inl ?_
    have hnot : ¬ (c : ℤ) ∣ (z - 1) := by
      intro hh
      have : (c : ℤ) ∣ 1 := by
        have := dvd_sub hcz hh
        simpa using this
      exact hp.not_unit (isUnit_of_dvd_one this)
    have := hp.pow_dvd_of_dvd_mul_right k hnot hdvd
    rw [← hz]
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd z (c ^ k)).2 (by exact_mod_cast this)
    exact h2
  · refine Or.inr ?_
    have := hp.pow_dvd_of_dvd_mul_left k hcz hdvd
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - 1) (c ^ k)).2 (by exact_mod_cast this)
    push_cast at h2
    rw [hz] at h2
    linear_combination h2

/-- A nonzero idempotent matrix makes `1 - E` singular, over a ring with no nontrivial
idempotents. -/
theorem det_one_sub_eq_zero_of_idem {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (hR : ∀ t : R, t * t = t → t = 0 ∨ t = 1)
    {E : Matrix n n R} (hE : E * E = E) (hne : E ≠ 0) : (1 - E).det = 0 := by
  have hsq : (1 - E) * (1 - E) = 1 - E := by
    have : (1 - E) * (1 - E) = 1 - E - E + E * E := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      simp [Matrix.one_mul, Matrix.mul_one]
      abel
    rw [this, hE]
    abel
  have hdet : (1 - E).det * (1 - E).det = (1 - E).det := by
    rw [← Matrix.det_mul, hsq]
  rcases hR _ hdet with h0 | h1
  · exact h0
  · exfalso
    have hu : IsUnit (1 - E) := (Matrix.isUnit_iff_isUnit_det (1 - E)).2 (by rw [h1]; exact isUnit_one)
    obtain ⟨u, hu'⟩ := hu
    have hEz : E * (1 - E) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hE, sub_self]
    rw [← hu'] at hEz
    have hEeq : E = E * ((u : Matrix n n R) * (↑u⁻¹ : Matrix n n R)) := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    rw [← mul_assoc, hEz, zero_mul] at hEeq
    exact hne hEeq

/-- One `c`-power step of the lifting-the-exponent congruence, iterated. -/
theorem pow_c_pow_congr {d c : ℕ} {A B : Matrix (Fin d) (Fin d) ℤ} (hcomm : Commute A B)
    (h : ∀ i j, (c : ℤ) ∣ (A - B) i j) (n : ℕ) :
    ∀ i j, (c : ℤ) ^ (n + 1) ∣ (A ^ (c ^ n) - B ^ (c ^ n)) i j := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      intro i j
      have hc2 : Commute (A ^ (c ^ n)) (B ^ (c ^ n)) := hcomm.pow_pow _ _
      have := TeichmullerCongruence.pow_congr_lift hc2 (e := n + 1) (by omega) ih i j
      rwa [← pow_mul, ← pow_mul, ← pow_succ] at this

/-- `S^(Q+1) = S` makes `S^Q` idempotent. -/
theorem pow_idem_of_pow_succ {M : Type*} [Monoid M] {S : M} {Q : ℕ} (hQ : 1 ≤ Q)
    (h : S ^ (Q + 1) = S) : S ^ Q * S ^ Q = S ^ Q := by
  have key : ∀ j, 1 ≤ j → S ^ (Q + j) = S ^ j := by
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have : Q + (j' + 1) = (Q + 1) + j' := by ring
    rw [this, pow_add, h, ← pow_succ']
  rw [← pow_add]
  exact key Q hQ

/-- **The mixed limit matrix.**  There are `Q ≥ 1` and a threshold `n₀` such that for every
`ν ≥ n₀` the matrix `T := C^(c^ν)` satisfies `T^(Q+1) ≡ T` and `det (1 - T^Q) ≡ 0` modulo
`c^(ν - n₀ + 1)`.  The second congruence says that the idempotent `T^Q` is nonzero, i.e. that
*some* root of `f` is a `c`-unit — and it holds precisely because `f ≢ X^d (mod c)`.

The exponent is a pure power `c^ν` (not `L·c^ν`), because the frozen statement is about
`⌊α^(c^n+s)⌋`: the pre-period `a` of `D = C mod c` is absorbed by taking `ν ≥ a`, since
`c^ν ≥ a` already, and the *level* — not the exponent — is what the lifting buys. -/
theorem exists_mixed_limit (f : ℤ[X]) (hmon : f.Monic) (hd : 1 ≤ f.natDegree) {c : ℕ}
    (hc : c.Prime) (hunit : f.map (Int.castRingHom (ZMod c)) ≠ X ^ f.natDegree) :
    ∃ Q n₀ : ℕ, 1 ≤ Q ∧ ∀ ν : ℕ, n₀ ≤ ν →
      (∀ i j, (c : ℤ) ^ (ν - n₀ + 1) ∣
          ((compM ℤ f ^ (c ^ ν)) ^ (Q + 1) - compM ℤ f ^ (c ^ ν)) i j) ∧
      (c : ℤ) ^ (ν - n₀ + 1) ∣ (1 - (compM ℤ f ^ (c ^ ν)) ^ Q).det := by
  classical
  haveI : Fact c.Prime := ⟨hc⟩
  set D := compM (ZMod c) f with hD
  obtain ⟨a, Q, ha, hQ, hper⟩ := exists_period D
  have hn₀ : a ≤ c ^ a :=
    le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hc.two_le a)
  refine ⟨Q, a, hQ, ?_⟩
  -- past the pre-period, only the residue of the exponent mod `Q` matters
  have hper2 : ∀ N u : ℕ, a ≤ N → D ^ (N + u * Q) = D ^ N := by
    intro N u hN
    have hNa : N = a + (N - a) := by omega
    rw [hNa]
    exact pow_add_period hper (N - a) u
  have hDL : ∀ ν : ℕ, a ≤ c ^ ν → D ^ (c ^ ν * Q) = D ^ (a * Q) := by
    intro ν hν
    have hrw : c ^ ν * Q = a * Q + (c ^ ν - a) * Q := by
      have h1 : a + (c ^ ν - a) = c ^ ν := by omega
      calc c ^ ν * Q = (a + (c ^ ν - a)) * Q := by rw [h1]
        _ = a * Q + (c ^ ν - a) * Q := by ring
    rw [hrw]
    exact hper2 (a * Q) (c ^ ν - a) (Nat.le_mul_of_pos_right a hQ)
  have hDLne : D ^ (a * Q) ≠ 0 := fun h0 =>
    hunit (map_eq_X_pow_of_compM_pow_eq_zero f hmon hd h0)
  -- the base congruence mod `c`, at exponent `c^a`
  have hbaseD : D ^ (c ^ a * (Q + 1)) = D ^ (c ^ a) := by
    have hrw : c ^ a * (Q + 1) = c ^ a + c ^ a * Q := by ring
    rw [hrw]
    exact hper2 (c ^ a) (c ^ a) hn₀
  set φ : ℤ →+* ZMod c := Int.castRingHom (ZMod c) with hφ
  have hmapZ : ∀ N : ℕ, (compM ℤ f ^ N).map φ = D ^ N := by
    intro N
    rw [map_matrix_pow, compM_map, hD]
  have hdvd_of_map : ∀ (M : Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ),
      M.map φ = 0 → ∀ i j, (c : ℤ) ∣ M i j := by
    intro M hM i j
    have h1 := congrFun (congrFun hM i) j
    simp only [Matrix.map_apply, Matrix.zero_apply, hφ] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).1 (by exact_mod_cast h1)
  have hbase : ∀ i j, (c : ℤ) ∣
      (compM ℤ f ^ (c ^ a * (Q + 1)) - compM ℤ f ^ (c ^ a)) i j := by
    refine hdvd_of_map _ ?_
    rw [map_matrix_sub, hmapZ, hmapZ, hbaseD, sub_self]
  have hcomm : Commute (compM ℤ f ^ (c ^ a * (Q + 1))) (compM ℤ f ^ (c ^ a)) :=
    (Commute.refl (compM ℤ f)).pow_pow _ _
  intro ν hν
  have hcν : a ≤ c ^ ν := le_trans hn₀ (Nat.pow_le_pow_right hc.one_lt.le hν)
  set m := ν - a with hm
  have hνm : a + m = ν := by omega
  -- the lifted congruence, rewritten at exponent `c^ν`
  have hT1 : (compM ℤ f ^ (c ^ a * (Q + 1))) ^ (c ^ m)
      = (compM ℤ f ^ (c ^ ν)) ^ (Q + 1) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    rw [← hνm, pow_add]
    ring
  have hT2 : (compM ℤ f ^ (c ^ a)) ^ (c ^ m) = compM ℤ f ^ (c ^ ν) := by
    rw [← pow_mul, ← hνm, pow_add]
  have hcongT : ∀ i j, (c : ℤ) ^ (m + 1) ∣
      ((compM ℤ f ^ (c ^ ν)) ^ (Q + 1) - compM ℤ f ^ (c ^ ν)) i j := by
    intro i j
    have h1 := pow_c_pow_congr hcomm hbase m i j
    rwa [hT1, hT2] at h1
  refine ⟨hcongT, ?_⟩
  -- the determinant congruence, read in `ZMod (c^(m+1))`
  set R := ZMod (c ^ (m + 1)) with hR
  set ψ : ℤ →+* R := Int.castRingHom R with hψ
  set S : Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
    (compM ℤ f ^ (c ^ ν)).map ψ with hS
  have hSsucc : S ^ (Q + 1) = S := by
    have hmap : ((compM ℤ f ^ (c ^ ν)) ^ (Q + 1)).map ψ = S ^ (Q + 1) := by
      rw [hS, map_matrix_pow]
    rw [← hmap]
    ext i j
    have h1 := hcongT i j
    have h2 : ψ (((compM ℤ f ^ (c ^ ν)) ^ (Q + 1) - compM ℤ f ^ (c ^ ν)) i j) = 0 := by
      obtain ⟨z, hz⟩ := h1
      rw [hz, hψ]
      simp only [map_mul, eq_intCast, Int.cast_pow, Int.cast_natCast]
      have hzero : ((c : R)) ^ (m + 1) = 0 := by
        have h3 := ZMod.natCast_self (c ^ (m + 1))
        push_cast at h3
        simpa [hR] using h3
      rw [hzero, zero_mul]
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, hS] at h2 ⊢
    linear_combination h2
  have hidem : S ^ Q * S ^ Q = S ^ Q := pow_idem_of_pow_succ hQ hSsucc
  have hSQne : S ^ Q ≠ 0 := by
    intro h0
    have hdvdc : c ∣ c ^ (m + 1) := dvd_pow_self c (by omega)
    set χ : R →+* ZMod c := ZMod.castHom hdvdc (ZMod c) with hχ
    have hcomp : ((χ : R → ZMod c) ∘ (ψ : ℤ → R)) = (φ : ℤ → ZMod c) := by
      funext z
      simp [hψ, hφ, hχ]
    have hmapD : ((S ^ Q).map χ) = D ^ (c ^ ν * Q) := by
      rw [hS, ← map_matrix_pow, Matrix.map_map, hcomp, ← pow_mul, hmapZ]
    rw [h0, hDL ν hcν] at hmapD
    exact hDLne (by simpa using hmapD.symm)
  have hdet0 : (1 - S ^ Q).det = 0 :=
    det_one_sub_eq_zero_of_idem (zmod_idem_eq_zero_or_one hc (m + 1)) hidem hSQne
  have hmapdet : ψ ((1 - (compM ℤ f ^ (c ^ ν)) ^ Q).det) = (1 - S ^ Q).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, map_sub, hS]
    rw [← map_matrix_pow]
    simp only [Matrix.map_apply]
    by_cases hij : i = j <;> simp [hij]
  rw [hdet0] at hmapdet
  have hfin := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((1 - (compM ℤ f ^ (c ^ ν)) ^ Q).det) (c ^ (m + 1))).1 (by simpa [hψ] using hmapdet)
  exact_mod_cast hfin


/-! ### Step 2: the transfer, over the algebraic numbers

The system is solved over `AlgQ`, the algebraic numbers inside `ℂ`, not over `ℂ`: step 3 conjugates
the solution by an automorphism, and that is only available on algebraic numbers.  Both phase 56
lemmas generalize verbatim from `ℂ` to any algebraically closed field of characteristic zero. -/

theorem exists_zero_of_family {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {σ ι : Type*} [Finite σ] [Fintype ι] {c : ℕ} (hc : 2 ≤ c)
    (F : ι → MvPolynomial σ ℤ)
    (hlev : ∀ k : ℕ, ∃ p : σ → ℤ, ∀ i, (c : ℤ) ^ k ∣ MvPolynomial.eval p (F i)) :
    ∃ q : σ → K, ∀ i, MvPolynomial.eval₂ (Int.castRingHom K) q (F i) = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ with hφ
  set G : ι → MvPolynomial σ ℚ := fun i => (F i).map φ with hG
  have hbridge : ∀ (q : MvPolynomial σ ℤ) (x : σ → K),
      MvPolynomial.aeval x (q.map φ) = MvPolynomial.eval₂ (Int.castRingHom K) x q := by
    intro q x
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext fun n => by simp [hφ]
  have hzl : MvPolynomial.zeroLocus K (Ideal.span (Set.range G)) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨i, hi⟩ := hcon x
    have hxi := hx (G i) (Ideal.subset_span ⟨i, rfl⟩)
    rw [hG] at hxi
    exact hi (by rw [← hbridge]; exact hxi)
  have htop : Ideal.span (Set.range G) = ⊤ := by
    have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) (Ideal.span (Set.range G))
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

theorem exists_root_enum_field {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (f : ℤ[X]) (hmon : f.Monic) (hirr : Irreducible f) :
    ∃ e : Fin f.natDegree → K, Function.Injective e ∧
      (∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0) ∧
      ∀ z : K, (f.map (Int.castRingHom K)).eval z = 0 → ∃ i, e i = z := by
  classical
  set fC := f.map (Int.castRingHom K) with hfCdef
  have hfC0 : fC ≠ 0 := (hmon.map (Int.castRingHom K)).ne_zero
  have hnd : fC.natDegree = f.natDegree := hmon.natDegree_map _
  have hcard : fC.roots.card = f.natDegree := by
    rw [← hnd]; exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits fC)
  -- separability, via irreducibility over `ℚ`
  have hsepQ : (f.map (Int.castRingHom ℚ)).Separable := by
    have hirrQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
      (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).1 hirr
    exact hirrQ.separable
  have hsepC : fC.Separable := by
    have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
      RingHom.ext fun n => by simp
    have hfe : fC = (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ K) := by
      rw [Polynomial.map_map, hcomp]
    rw [hfe]
    exact hsepQ.map
  have hnodup : fC.roots.Nodup := Polynomial.nodup_roots hsepC
  obtain ⟨S, hS⟩ : ∃ S : Finset K, S = fC.roots.toFinset := ⟨_, rfl⟩
  have hScard : S.card = f.natDegree := by
    rw [hS, Multiset.toFinset_card_of_nodup hnodup, hcard]
  have hSroot : ∀ z ∈ S, fC.eval z = 0 := by
    intro z hz
    rw [hS, Multiset.mem_toFinset] at hz
    exact Polynomial.isRoot_of_mem_roots hz
  have hSmem : ∀ z : K, fC.eval z = 0 → z ∈ S := by
    intro z hz
    rw [hS, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hfC0).2 hz
  set E := S.equivFin with hE
  refine ⟨fun i => (E.symm (Fin.cast hScard.symm i)  : K), ?_, ?_, ?_⟩
  · intro i j hij
    have := E.symm.injective (Subtype.ext hij)
    exact Fin.cast_injective _ this
  · intro i
    exact hSroot _ (E.symm (Fin.cast hScard.symm i)).2
  · intro z hz
    refine ⟨Fin.cast hScard (E ⟨z, hSmem z hz⟩), ?_⟩
    simp


/-! ### Step 2b: the two mixed payoffs of the Vandermonde conjugation

Phase 56 read off `P(e k)^Q = 1` from `T^Q = 1`.  In the mixed case `T` is not torsion, and the two
facts to read off the conjugation are `P(e k)^(Q+1) = P(e k)` (so `P(e k) ∈ {0} ∪ μ_Q`) and
`∏_k (1 - P(e k)^Q) = det (1 - T^Q) = 0` (so *some* `P(e k)` is a `Q`-th root of unity). -/

/-- Right cancellation by an invertible matrix. -/
theorem right_cancel_of_isUnit_det {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    {A B V : Matrix n n K} (hV : IsUnit V.det) (h : A * V = B * V) : A = B := by
  have hinv : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hV
  calc A = A * (V * V⁻¹) := by rw [hinv, Matrix.mul_one]
    _ = (A * V) * V⁻¹ := by rw [Matrix.mul_assoc]
    _ = (B * V) * V⁻¹ := by rw [h]
    _ = B * (V * V⁻¹) := by rw [Matrix.mul_assoc]
    _ = B := by rw [hinv, Matrix.mul_one]

/-- **Mixed payoff 1.**  `T^(Q+1) = T` forces `P(e k)^(Q+1) = P(e k)` at every root. -/
theorem polyVal_pow_succ_eq {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (hinj : Function.Injective e) (x : Fin f.natDegree → K) {Q : ℕ}
    (hQ : polyMat K f x ^ (Q + 1) = polyMat K f x) (i : Fin f.natDegree) :
    polyVal x (e i) ^ (Q + 1) = polyVal x (e i) := by
  classical
  set V := Matrix.vandermonde e with hV
  set Δ := Matrix.diagonal (fun i => polyVal x (e i)) with hΔ
  have hconj : V * polyMat K f x = Δ * V := vandermonde_mul_polyMat f hmon e he x
  have hpow := conj_pow V (polyMat K f x) Δ hconj (Q + 1)
  rw [hQ, hconj] at hpow
  have hdiag : Δ ^ (Q + 1) = Δ :=
    right_cancel_of_isUnit_det (vandermonde_isUnit_det e hinj) hpow.symm
  rw [hΔ, Matrix.diagonal_pow] at hdiag
  have := congrArg (fun M : Matrix (Fin f.natDegree) (Fin f.natDegree) K => M i i) hdiag
  simpa using this

/-- **Mixed payoff 2.**  `det (1 - T^Q) = 0` forces `P(e k)^Q = 1` for some root, i.e. *some*
spectral value of `T` is nonzero. -/
theorem exists_polyVal_pow_eq_one {K : Type*} [Field K] (f : ℤ[X]) (hmon : f.Monic)
    (e : Fin f.natDegree → K) (he : ∀ i, (f.map (Int.castRingHom K)).eval (e i) = 0)
    (hinj : Function.Injective e) (x : Fin f.natDegree → K) {Q : ℕ}
    (hdet : (1 - polyMat K f x ^ Q).det = 0) : ∃ i, polyVal x (e i) ^ Q = 1 := by
  classical
  set V := Matrix.vandermonde e with hV
  set Δ := Matrix.diagonal (fun i => polyVal x (e i)) with hΔ
  have hconj : V * polyMat K f x = Δ * V := vandermonde_mul_polyMat f hmon e he x
  have hpow := conj_pow V (polyMat K f x) Δ hconj Q
  have hsub : V * (1 - polyMat K f x ^ Q) = (1 - Δ ^ Q) * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hpow]
  have hdets := congrArg Matrix.det hsub
  rw [Matrix.det_mul, Matrix.det_mul, hdet, mul_zero] at hdets
  have hVu := vandermonde_isUnit_det e hinj
  have hz : (1 - Δ ^ Q).det = 0 := by
    rcases mul_eq_zero.1 hdets.symm with h | h
    · exact h
    · exact absurd h (isUnit_iff_ne_zero.1 hVu)
  have hdd : (1 - Δ ^ Q) = Matrix.diagonal (fun i => 1 - polyVal x (e i) ^ Q) := by
    rw [hΔ, Matrix.diagonal_pow]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hdd, Matrix.det_diagonal] at hz
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.1 hz
  exact ⟨i, by linear_combination -hi⟩


/-! ### Step 2c: the integer system and its solution over the algebraic numbers -/

/-- The field of algebraic numbers inside `ℂ`.  The integer system is solved here, not in `ℂ`,
because step 3 conjugates the solution by an automorphism over `ℚ`. -/
noncomputable abbrev AlgQ := ↥(algebraicClosure ℚ ℂ)

noncomputable instance : IsAlgClosure ℚ AlgQ := algebraicClosure.isAlgClosure ℚ ℂ

noncomputable instance : IsAlgClosed AlgQ := IsAlgClosure.isAlgClosed ℚ

theorem map_matrix_one {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (φ : R →+* S) : (1 : Matrix n n R).map φ = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, Matrix.map_apply, hij]

theorem map_one_sub_polyMat_pow {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : ℤ[X]) (x : Fin f.natDegree → R) (Q : ℕ) :
    (1 - polyMat R f x ^ Q).map φ = 1 - polyMat S f (fun t => φ (x t)) ^ Q := by
  rw [map_matrix_sub, map_matrix_one, map_matrix_pow, polyMat_map]

theorem map_polyMat_det {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : ℤ[X]) (x : Fin f.natDegree → R) (Q : ℕ) :
    φ ((1 - polyMat R f x ^ Q).det) = (1 - polyMat S f (fun t => φ (x t)) ^ Q).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_one_sub_polyMat_pow]

theorem map_polyMat_pow_succ_sub {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : ℤ[X]) (x : Fin f.natDegree → R) (Q : ℕ) (i j : Fin f.natDegree) :
    φ ((polyMat R f x ^ (Q + 1) - polyMat R f x) i j)
      = (polyMat S f (fun t => φ (x t)) ^ (Q + 1) - polyMat S f (fun t => φ (x t))) i j := by
  have hh : (polyMat R f x ^ (Q + 1) - polyMat R f x).map φ
      = polyMat S f (fun t => φ (x t)) ^ (Q + 1) - polyMat S f (fun t => φ (x t)) := by
    rw [map_matrix_sub, map_matrix_pow, polyMat_map]
  simpa [Matrix.map_apply] using congrFun (congrFun hh i) j

/-- **Steps 5–6, mixed.**  The `d² + 3` equation system — `T^(Q+1) = T`, `det (1 - T^Q) = 0`,
`w^m = 1` and the window equation — solvable modulo `c^k` at every level, has a solution in the
algebraic numbers. -/
theorem exists_spectral_solution_mixed (f : ℤ[X]) (hd : 1 ≤ f.natDegree) {c : ℕ} (hc : c.Prime)
    {Q n₀ s m : ℕ}
    (hmix : ∀ ν : ℕ, n₀ ≤ ν →
      (∀ i j, (c : ℤ) ^ (ν - n₀ + 1) ∣
          ((compM ℤ f ^ (c ^ ν)) ^ (Q + 1) - compM ℤ f ^ (c ^ ν)) i j) ∧
      (c : ℤ) ^ (ν - n₀ + 1) ∣ (1 - (compM ℤ f ^ (c ^ ν)) ^ Q).det)
    {ε : ℤ}
    (hcong : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ w : ℤ, (c : ℤ) ^ k ∣ w ^ m - 1 ∧
        (c : ℤ) ^ k ∣ traceSeq f (c ^ n + s) - (w - ε)) :
    ∃ (x : Fin f.natDegree → AlgQ) (w : AlgQ),
      polyMat AlgQ f x ^ (Q + 1) = polyMat AlgQ f x ∧
      (1 - polyMat AlgQ f x ^ Q).det = 0 ∧ w ^ m = 1 ∧
      (polyMat AlgQ f x * compM AlgQ f ^ s).trace = w - (ε : AlgQ) := by
  classical
  set d := f.natDegree with hdd
  set σ := Option (Fin d) with hσ
  set Xv : Fin d → MvPolynomial σ ℤ := fun j => MvPolynomial.X (some j) with hXv
  set W : MvPolynomial σ ℤ := MvPolynomial.X none with hW
  set Fsys : Option ((Fin d × Fin d) ⊕ Bool) → MvPolynomial σ ℤ := fun o =>
    o.elim (1 - polyMat (MvPolynomial σ ℤ) f Xv ^ Q).det
      (Sum.elim
        (fun ij => (polyMat (MvPolynomial σ ℤ) f Xv ^ (Q + 1)
          - polyMat (MvPolynomial σ ℤ) f Xv) ij.1 ij.2)
        (fun b => if b then W ^ m - ((1 : ℤ) : MvPolynomial σ ℤ)
          else (∑ j, Xv j * ((traceSeq f ((j : ℕ) + s) : ℤ) : MvPolynomial σ ℤ)) - W
            + ((ε : ℤ) : MvPolynomial σ ℤ))) with hFsys
  -- evaluation at an integer point
  have hevalZ : ∀ p : σ → ℤ,
      MvPolynomial.eval p (Fsys none)
          = (1 - polyMat ℤ f (fun t => p (some t)) ^ Q).det ∧
      (∀ i j : Fin d, MvPolynomial.eval p (Fsys (some (Sum.inl (i, j))))
        = (polyMat ℤ f (fun t => p (some t)) ^ (Q + 1)
            - polyMat ℤ f (fun t => p (some t))) i j) ∧
      MvPolynomial.eval p (Fsys (some (Sum.inr true))) = (p none) ^ m - 1 ∧
      MvPolynomial.eval p (Fsys (some (Sum.inr false)))
        = (∑ j, p (some j) * traceSeq f ((j : ℕ) + s)) - p none + ε := by
    intro p
    refine ⟨?_, fun i j => ?_, ?_, ?_⟩
    · have := map_polyMat_det (MvPolynomial.eval p) f Xv Q
      simpa [hFsys, hXv] using this
    · have := map_polyMat_pow_succ_sub (MvPolynomial.eval p) f Xv Q i j
      simpa [hFsys, hXv] using this
    · simp [hFsys, hW]
    · simp [hFsys, hXv, hW]
  -- evaluation at a point of `AlgQ`
  have hevalA : ∀ q : σ → AlgQ,
      MvPolynomial.eval₂ (Int.castRingHom AlgQ) q (Fsys none)
          = (1 - polyMat AlgQ f (fun t => q (some t)) ^ Q).det ∧
      (∀ i j : Fin d, MvPolynomial.eval₂ (Int.castRingHom AlgQ) q (Fsys (some (Sum.inl (i, j))))
        = (polyMat AlgQ f (fun t => q (some t)) ^ (Q + 1)
            - polyMat AlgQ f (fun t => q (some t))) i j) ∧
      MvPolynomial.eval₂ (Int.castRingHom AlgQ) q (Fsys (some (Sum.inr true)))
          = (q none) ^ m - 1 ∧
      MvPolynomial.eval₂ (Int.castRingHom AlgQ) q (Fsys (some (Sum.inr false)))
        = (∑ j, q (some j) * ((traceSeq f ((j : ℕ) + s) : ℤ) : AlgQ)) - q none + (ε : AlgQ) := by
    intro q
    refine ⟨?_, fun i j => ?_, ?_, ?_⟩
    · have := map_polyMat_det (MvPolynomial.eval₂Hom (Int.castRingHom AlgQ) q) f Xv Q
      simpa [hFsys, hXv, ← MvPolynomial.coe_eval₂Hom] using this
    · have := map_polyMat_pow_succ_sub
        (MvPolynomial.eval₂Hom (Int.castRingHom AlgQ) q) f Xv Q i j
      simpa [hFsys, hXv, ← MvPolynomial.coe_eval₂Hom] using this
    · simp [hFsys, hW, ← MvPolynomial.coe_eval₂Hom]
    · simp [hFsys, hXv, hW, ← MvPolynomial.coe_eval₂Hom]
  -- the levels
  have hlev : ∀ k : ℕ, ∃ p : σ → ℤ, ∀ i, (c : ℤ) ^ k ∣ MvPolynomial.eval p (Fsys i) := by
    intro k
    obtain ⟨n, hnk, w, hw, hV⟩ := hcong (k + n₀)
    obtain ⟨x, hx⟩ := exists_coords f hd (c ^ n)
    obtain ⟨hm1, hm2⟩ := hmix n (by omega)
    have hlevk : k ≤ n - n₀ + 1 := by omega
    refine ⟨fun o => Option.elim o w x, ?_⟩
    obtain ⟨h0, h1, h2, h3⟩ := hevalZ (fun o => Option.elim o w x)
    intro i
    rcases i with _ | i
    · rw [h0]
      simp only [Option.elim]
      rw [← hx]
      exact dvd_trans (pow_dvd_pow (c : ℤ) hlevk) hm2
    · rcases i with ⟨i, j⟩ | b
      · rw [h1 i j]
        simp only [Option.elim]
        rw [← hx]
        exact dvd_trans (pow_dvd_pow (c : ℤ) hlevk) (hm1 i j)
      · rcases b with _ | _
        · rw [h3]
          have htr : (∑ j, x j * traceSeq f ((j : ℕ) + s)) = traceSeq f (c ^ n + s) := by
            have h4 := trace_polyMat_mul f x s
            rw [← hx, ← pow_add] at h4
            exact h4.symm
          simp only [Option.elim]
          rw [htr]
          have hrw : traceSeq f (c ^ n + s) - w + ε
              = traceSeq f (c ^ n + s) - (w - ε) := by ring
          rw [hrw]
          exact dvd_trans (pow_dvd_pow (c : ℤ) (by omega)) hV
        · rw [h2]
          simp only [Option.elim]
          exact dvd_trans (pow_dvd_pow (c : ℤ) (by omega)) hw
  obtain ⟨q, hq⟩ := exists_zero_of_family (K := AlgQ) (σ := σ) hc.two_le Fsys hlev
  obtain ⟨h0, h1, h2, h3⟩ := hevalA q
  refine ⟨fun t => q (some t), q none, ?_, ?_, ?_, ?_⟩
  · have hz : polyMat AlgQ f (fun t => q (some t)) ^ (Q + 1)
        - polyMat AlgQ f (fun t => q (some t)) = 0 := by
      ext i j
      rw [← h1 i j, hq (some (Sum.inl (i, j)))]
      simp
    exact sub_eq_zero.1 hz
  · rw [← h0]; exact hq none
  · have := hq (some (Sum.inr true))
    rw [h2] at this
    exact sub_eq_zero.1 this
  · have := hq (some (Sum.inr false))
    rw [h3] at this
    rw [trace_polyMat_mul]
    linear_combination this


/-! ### Step 3: transport along a ring hom, and the automorphism

The system is a set of *integer* polynomial equations, so any ring hom carries a solution to a
solution.  That is what makes step 3 work: an automorphism `σ` of the algebraic numbers moving
`α_(k*)` — a root at which the spectral value is nonzero — onto `α` produces a new solution whose
spectral value *at `α`* is nonzero, which is exactly what the size argument needs. -/

theorem trace_map_eq {n R S : Type*} [Fintype n] [CommRing R] [CommRing S] (τ : R →+* S)
    (M : Matrix n n R) : (M.map τ).trace = τ M.trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem map_matrix_mul {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (τ : R →+* S) (A B : Matrix n n R) : (A * B).map τ = A.map τ * B.map τ := by
  simpa [RingHom.mapMatrix_apply] using map_mul (RingHom.mapMatrix τ) A B

theorem polyVal_map {R S : Type*} [CommRing R] [CommRing S] (τ : R →+* S) {d : ℕ}
    (x : Fin d → R) (z : R) : τ (polyVal x z) = polyVal (fun t => τ (x t)) (τ z) := by
  simp [polyVal, map_sum, map_mul, map_pow]

/-- **Transport.**  A ring hom carries a solution of the integer system to a solution. -/
theorem transport_solution {R S : Type*} [CommRing R] [CommRing S] (τ : R →+* S)
    (f : ℤ[X]) {Q m s : ℕ} {ε : ℤ} (x : Fin f.natDegree → R) (w : R)
    (hT : polyMat R f x ^ (Q + 1) = polyMat R f x) (hw : w ^ m = 1)
    (htr : (polyMat R f x * compM R f ^ s).trace = w - (ε : R)) :
    polyMat S f (fun t => τ (x t)) ^ (Q + 1) = polyMat S f (fun t => τ (x t)) ∧
      (τ w) ^ m = 1 ∧
      (polyMat S f (fun t => τ (x t)) * compM S f ^ s).trace = τ w - (ε : S) := by
  refine ⟨?_, by rw [← map_pow, hw, map_one], ?_⟩
  · have h : (polyMat R f x ^ (Q + 1)).map τ = (polyMat R f x).map τ := by rw [hT]
    rwa [map_matrix_pow, polyMat_map] at h
  · have hmm : (polyMat R f x * compM R f ^ s).map τ
        = polyMat S f (fun t => τ (x t)) * compM S f ^ s := by
      rw [map_matrix_mul, polyMat_map, map_matrix_pow, compM_map]
    have h := trace_map_eq τ (polyMat R f x * compM R f ^ s)
    rw [hmm, htr] at h
    rw [h, map_sub, map_intCast]

/-- **Step 3 (the automorphism).**  If `a` and `b` are roots of the monic irreducible `f` in the
algebraic numbers, some automorphism over `ℚ` carries `a` to `b`. -/
theorem exists_algEquiv_of_roots (f : ℤ[X]) (hmon : f.Monic) (hirr : Irreducible f)
    (hd : 1 ≤ f.natDegree) {a b : AlgQ}
    (ha : (f.map (Int.castRingHom AlgQ)).eval a = 0)
    (hb : (f.map (Int.castRingHom AlgQ)).eval b = 0) :
    ∃ τ : AlgQ ≃ₐ[ℚ] AlgQ, τ a = b := by
  classical
  set g := f.map (Int.castRingHom ℚ) with hg
  have hgm : g.Monic := hmon.map _
  have hgirr : Irreducible g :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).1 hirr
  have hbridge : ∀ z : AlgQ, Polynomial.aeval z g
      = (f.map (Int.castRingHom AlgQ)).eval z := by
    intro z
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hg, Polynomial.map_map]
    congr 2
  have hmin : minpoly ℚ b = g :=
    (minpoly.eq_of_irreducible_of_monic (x := b) hgirr (by rw [hbridge]; exact hb) hgm).symm
  have halg : IsAlgebraic ℚ b := ⟨g, hgm.ne_zero, by rw [hbridge]; exact hb⟩
  refine minpoly.exists_algEquiv_of_root halg ?_
  rw [hmin, hbridge]
  exact ha

/-! ### Step 4: the archimedean contradiction, mixed version -/

theorem norm_le_one_of_pow_succ_eq {z : ℂ} {Q : ℕ} (hQ : 1 ≤ Q) (h : z ^ (Q + 1) = z) :
    ‖z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0]; simp
  · have hzQ : z ^ Q = 1 := by
      have hfac : z * (z ^ Q - 1) = 0 := by
        have hr : z * (z ^ Q - 1) = z ^ (Q + 1) - z := by ring
        rw [hr, h, sub_self]
      rcases mul_eq_zero.1 hfac with h1 | h1
      · exact absurd h1 h0
      · linear_combination h1
    exact le_of_eq (norm_eq_one_of_pow_eq_one hQ hzQ)

/-- **Step 7 (mixed size argument).**  `T^(Q+1) = T` with a *nonzero* spectral value at `α`,
`tr(T C^s) = w - ε`, `w` a root of unity and `|ε| ≤ 1`, forces `α^s ≤ 2 + (d - 1) = d + 1`. -/
theorem not_exists_spectral_mixed (f : ℤ[X]) (hmon : f.Monic) (hirr : Irreducible f)
    (hdeg : 2 ≤ f.natDegree) {α : ℝ} (hα : 1 < α)
    (hroot : (f.map (Int.castRingHom ℂ)).eval (α : ℂ) = 0)
    (hpisot : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1)
    {Q : ℕ} (hQ : 1 ≤ Q) {s : ℕ} (hs : (f.natDegree : ℝ) + 1 < α ^ s)
    {m : ℕ} (hm : 1 ≤ m) {ε : ℤ} (hε : |ε| ≤ 1)
    (x : Fin f.natDegree → ℂ) (w : ℂ)
    (hT : polyMat ℂ f x ^ (Q + 1) = polyMat ℂ f x) (hnz : polyVal x (α : ℂ) ≠ 0)
    (hw : w ^ m = 1)
    (htr : (polyMat ℂ f x * compM ℂ f ^ s).trace = w - (ε : ℂ)) : False := by
  classical
  have hd : 1 ≤ f.natDegree := by omega
  obtain ⟨e, hinj, he, hsurj⟩ := exists_root_enum_field (K := ℂ) f hmon hirr
  obtain ⟨i₀, hi₀⟩ := hsurj (α : ℂ) hroot
  have hfC0 : (f.map (Int.castRingHom ℂ)) ≠ 0 := (hmon.map (Int.castRingHom ℂ)).ne_zero
  have hsmall : ∀ k, k ≠ i₀ → ‖e k‖ < 1 := by
    intro k hk
    refine hpisot (e k) ((Polynomial.mem_roots hfC0).2 (he k)) ?_
    rw [← hi₀]
    exact fun hh => hk (hinj hh)
  have hsp : ∑ k, polyVal x (e k) * e k ^ s = w - (ε : ℂ) := by
    rw [← trace_polyMat_mul_compM_pow f hmon e he hinj x s]; exact htr
  have hpv : ∀ k, polyVal x (e k) ^ (Q + 1) = polyVal x (e k) :=
    polyVal_pow_succ_eq f hmon e he hinj x hT
  have hle : ∀ k, ‖polyVal x (e k)‖ ≤ 1 := fun k =>
    norm_le_one_of_pow_succ_eq hQ (hpv k)
  -- at `α` the spectral value is nonzero, hence of modulus one
  have hone : ‖polyVal x (e i₀)‖ = 1 := by
    have hnz0 : polyVal x (e i₀) ≠ 0 := by rw [hi₀]; exact hnz
    have hzQ : polyVal x (e i₀) ^ Q = 1 := by
      have hfac : polyVal x (e i₀) * (polyVal x (e i₀) ^ Q - 1) = 0 := by
        have hr : polyVal x (e i₀) * (polyVal x (e i₀) ^ Q - 1)
            = polyVal x (e i₀) ^ (Q + 1) - polyVal x (e i₀) := by ring
        rw [hr, hpv i₀, sub_self]
      rcases mul_eq_zero.1 hfac with h1 | h1
      · exact absurd h1 hnz0
      · linear_combination h1
    exact norm_eq_one_of_pow_eq_one hQ hzQ
  have hsplit : polyVal x (e i₀) * e i₀ ^ s
      = (w - (ε : ℂ)) - ∑ k ∈ Finset.univ.erase i₀, polyVal x (e k) * e k ^ s := by
    rw [← hsp, ← Finset.add_sum_erase _ (fun k => polyVal x (e k) * e k ^ s)
      (Finset.mem_univ i₀)]
    ring
  have hlhs : ‖polyVal x (e i₀) * e i₀ ^ s‖ = α ^ s := by
    rw [norm_mul, hone, one_mul, hi₀, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have htail : ‖∑ k ∈ Finset.univ.erase i₀, polyVal x (e k) * e k ^ s‖
      ≤ (f.natDegree : ℝ) - 1 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hb : ∀ k ∈ Finset.univ.erase i₀, ‖polyVal x (e k) * e k ^ s‖ ≤ 1 := by
      intro k hk
      rw [norm_mul, norm_pow]
      have h1 : ‖e k‖ ^ s ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (le_of_lt (hsmall k (Finset.ne_of_mem_erase hk)))
      have h2 := hle k
      nlinarith [norm_nonneg (polyVal x (e k)), pow_nonneg (norm_nonneg (e k)) s]
    have hsum := Finset.sum_le_sum hb
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin] at hsum
    refine le_trans hsum ?_
    rw [nsmul_eq_mul, mul_one]
    have hcast : ((f.natDegree - 1 : ℕ) : ℝ) = (f.natDegree : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ f.natDegree := hd
      push_cast [h1]; ring
    rw [hcast]
  have hwε : ‖w - (ε : ℂ)‖ ≤ 2 := by
    have h1 : ‖w‖ = 1 := norm_eq_one_of_pow_eq_one hm hw
    have h2 : ‖(ε : ℂ)‖ ≤ 1 := by
      rw [show ((ε : ℤ) : ℂ) = ((ε : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      obtain ⟨hε1, hε2⟩ := abs_le.1 hε
      refine ⟨by exact_mod_cast hε1, by exact_mod_cast hε2⟩
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


/-- Ring homs commute with evaluating an integer polynomial. -/
theorem eval_map_int_hom {A B : Type*} [CommRing A] [CommRing B] (τ : A →+* B) (f : ℤ[X])
    (z : A) : τ ((f.map (Int.castRingHom A)).eval z)
      = (f.map (Int.castRingHom B)).eval (τ z) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun n => by simp

/-- **Steps 3–4 assembled.**  From a solution over the algebraic numbers with *some* nonzero
spectral value, an automorphism produces a complex solution whose spectral value at the
distinguished root `α` is nonzero. -/
theorem exists_complex_solution_nonzero_at_root (f : ℤ[X]) (hmon : f.Monic)
    (hirr : Irreducible f) (hd : 1 ≤ f.natDegree) {α : ℝ}
    (hrootC : (f.map (Int.castRingHom ℂ)).eval (α : ℂ) = 0)
    {Q m s : ℕ} (hQ : 1 ≤ Q) {ε : ℤ}
    (x : Fin f.natDegree → AlgQ) (w : AlgQ)
    (hT : polyMat AlgQ f x ^ (Q + 1) = polyMat AlgQ f x)
    (hdet : (1 - polyMat AlgQ f x ^ Q).det = 0) (hw : w ^ m = 1)
    (htr : (polyMat AlgQ f x * compM AlgQ f ^ s).trace = w - (ε : AlgQ)) :
    ∃ (y : Fin f.natDegree → ℂ) (v : ℂ),
      polyMat ℂ f y ^ (Q + 1) = polyMat ℂ f y ∧ polyVal y (α : ℂ) ≠ 0 ∧ v ^ m = 1 ∧
      (polyMat ℂ f y * compM ℂ f ^ s).trace = v - (ε : ℂ) := by
  classical
  set ι : AlgQ →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom with hι
  have hιinj : Function.Injective ι := fun a b hab => by
    exact Subtype.ext hab
  -- the roots of `f` in the algebraic numbers, and one with nonzero spectral value
  obtain ⟨e, hinj, he, _⟩ := exists_root_enum_field (K := AlgQ) f hmon hirr
  obtain ⟨k, hk⟩ := exists_polyVal_pow_eq_one f hmon e he hinj x hdet
  have hknz : polyVal x (e k) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : Q ≠ 0)] at hk
    exact zero_ne_one hk
  -- `α` is an algebraic number, and a root of `f` there
  have halgα : IsAlgebraic ℚ (α : ℂ) := by
    refine ⟨f.map (Int.castRingHom ℚ), (hmon.map _).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map,
      show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from
        RingHom.ext fun n => by simp]
    exact hrootC
  set α' : AlgQ := ⟨(α : ℂ), (mem_algebraicClosure_iff).2 halgα⟩ with hα'
  have hια' : ι α' = (α : ℂ) := rfl
  have hα'root : (f.map (Int.castRingHom AlgQ)).eval α' = 0 := by
    refine hιinj ?_
    rw [eval_map_int_hom ι f α', hια', hrootC, map_zero]
  -- the automorphism
  obtain ⟨τ, hτ⟩ := exists_algEquiv_of_roots f hmon hirr hd (he k) hα'root
  set τr : AlgQ →+* AlgQ := τ.toAlgHom.toRingHom with hτr
  obtain ⟨hT1, hw1, htr1⟩ := transport_solution τr f x w hT hw htr
  obtain ⟨hT2, hw2, htr2⟩ :=
    transport_solution ι f (fun t => τr (x t)) (τr w) hT1 hw1 htr1
  refine ⟨fun t => ι (τr (x t)), ι (τr w), hT2, ?_, hw2, htr2⟩
  -- the spectral value at `α` is the image of a nonzero one
  have hval : polyVal (fun t => ι (τr (x t))) (α : ℂ) = ι (τr (polyVal x (e k))) := by
    have h1 : τr (polyVal x (e k)) = polyVal (fun t => τr (x t)) (τr (e k)) :=
      polyVal_map τr x (e k)
    have h2 : τr (e k) = α' := hτ
    rw [h1, h2, polyVal_map ι (fun t => τr (x t)) α', hια']
  rw [hval]
  intro h0
  have h1 : τr (polyVal x (e k)) = 0 := hιinj (by rw [h0, map_zero])
  exact hknz (τ.injective (by simpa [hτr] using h1))

/-- **Theorem D (full):** some root of `f` is a `c`-unit, i.e. `f ≢ X^d (mod c)`. -/
theorem floor_pow_prime_pow_add_not_prime_full (f : ℤ[X]) (hmon : f.Monic)
    (hirr : Irreducible f) (hdeg : 2 ≤ f.natDegree) {α : ℝ} (hroot : aeval α f = 0)
    (hα : 1 < α)
    (hpisot : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1)
    {c : ℕ} (hc : c.Prime) (hunit : f.map (Int.castRingHom (ZMod c)) ≠ X ^ f.natDegree)
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
  -- `f(0) ≠ 0`: otherwise `X ∣ f`, impossible for an irreducible of degree `≥ 2`
  have hcoeff0 : f.coeff 0 ≠ 0 := by
    intro h
    obtain ⟨g, hgeq⟩ : (Polynomial.X : ℤ[X]) ∣ f := Polynomial.X_dvd_iff.2 h
    have hg0 : g ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hgeq
      exact hmon.ne_zero hgeq
    rcases hirr.isUnit_or_isUnit hgeq with hu | hu
    · exact Polynomial.not_isUnit_X hu
    · have hgd : g.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hf1 : f.natDegree = 1 := by
        rw [hgeq, Polynomial.natDegree_mul Polynomial.X_ne_zero hg0, hgd,
          Polynomial.natDegree_X]
      omega
  have hdet0 : (compM ℤ f).det ≠ 0 := compM_det_ne_zero_int f hd hcoeff0
  -- the mixed limit matrix (step 1)
  obtain ⟨Q, n₀, hQ, hmix⟩ := exists_mixed_limit f hmon hd hc hunit
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
  have hm1 : 1 ≤ (t.1 : ℕ) := by
    obtain ⟨n, _, h1, _⟩ := hfreq 0
    exact h1
  obtain ⟨x, w, hT, hdet, hw, htr⟩ :=
    exists_spectral_solution_mixed f hd hc hmix hcong
  obtain ⟨y, v, hT', hnz, hv, htr'⟩ :=
    exists_complex_solution_nonzero_at_root f hmon hirr hd hrootC hQ x w hT hdet hw htr
  exact not_exists_spectral_mixed f hmon hirr hdeg hα hrootC hpisot hQ hs hm1
    (by rw [hoffdef]; rcases t.2 with _ | _ <;> simp) y v hT' hnz hv htr'



end LeanFormalizations.Mills.TheoremDMixed

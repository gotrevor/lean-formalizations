/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ExteriorDold
import LeanFormalizations.NumberTheory.Mills.TeichmullerCongruence

/-!
# Phase 51: the Frobenius orbit sum is scalar (Theorem A route, steps 3–5)

Let `A ∈ M_d(ℤ)` with `χ_A` irreducible mod the prime `c`, and `B = A^(c^n)`.  Then

  `Σ_(k<d) A^(c^(n+k)) ≡ tr(A^(c^n)) · I   (mod c^(n+1))`.

This is the order-`d` generalization of the sign flip (`d = 2`: `A^(c^(n+1)) ≡ tr(B)·I − B`).  In
particular every off-diagonal entry of the orbit sum vanishes mod `c^(n+1)`, which is what Theorem A
(`u(c^n) + h` composite i.o. for order-`d` recurrences at inert `c`) consumes next phase.

Checked numerically on 604 cases (`d ∈ {2,…,5}`, `c ∈ {2,3,5,7}`, `n ≤ 3`, plus Tribonacci at 3):
0 failures.  Controls: at precision `c^(n+2)` it fails in 581 of 604 cases; with a reducible `χ_A`
(mod 3) it fails in 46 of 47 cases.  So precision `n + 1` and the irreducibility hypothesis are sharp.

## Route (see `ROADMAP-PRIME-TOWERS.md` §4a, steps 3–5)
0. **Period** (`pow_prime_pow_add_card_congr`).  Mod `c`, `𝔽_c[A] ≅ 𝔽_c[X]/(χ̄_A)` is the field
   `𝔽_(c^d)`, so `A^(c^d) ≡ A (mod c)` (Frobenius, `FiniteField.pow_card`, via `AdjoinRoot` /
   `Polynomial.aeval`, or Cayley–Hamilton mod `c` plus `X^(c^d) ≡ X mod χ̄`).  Lift with phase 47's
   `TeichmullerCongruence.pow_congr_lift` (`X ≡ Y mod c^m`, commuting ⇒ `X^c ≡ Y^c mod c^(m+1)`),
   `n` times.
1. Work in `R = ZMod (c^(n+1))` and let `B̄` be the image of `A^(c^n)`.  `1, B̄, …, B̄^(d−1)` are
   `R`-linearly independent because they are independent mod `c` (the minimal polynomial of `Ā` is
   `χ̄_A`, since it is irreducible), so `R[B̄]` is free of rank `d`.
2. `σ : q(B̄) ↦ q(B̄^c)` is well defined: phase 50's `aeval_charpoly_prime_pow_congr` gives
   `χ_B(B^c) ≡ 0 (mod c^(n+1))`.  It is a ring endomorphism.
3. **Fixed ring = scalars.**  Induct on precision: if `σ(y) = y` and `y ≡ s (mod c)`, then
   `y − s = c·y′` with `σ(y′) ≡ y′ (mod c^n)`.  At precision 1, `σ` is Frobenius on `𝔽_(c^d)`,
   whose fixed field is `𝔽_c`.
4. `S = Σ_(k<d) B̄^(c^k)` is `σ`-fixed: `σ(S) = S − B̄ + B̄^(c^d)`, and `B̄^(c^d) = B̄` by step 0.  So
   `S = s·I`.  Taking traces with Dold (`tr B̄^(c^k) = tr B̄`, phase 49) gives `d·s = d·tr B̄`.  To
   get `s = tr B̄` even when `c ∣ d`, identify `S` with the trace of the free `R`-algebra `R[B̄]`
   (the trace of multiplication by `B̄` in the basis `B̄^i` is `tr B̄`, as it is the companion
   matrix of `χ_B`), or run step 3's induction on `S − tr(B̄)·I` directly.
   **Any other route is welcome**, e.g. an induction on `n` that uses only `ExteriorDold` and
   step 0.  Add as many public helpers as needed.

Frozen: the three statements below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.OrbitSum

open Matrix Polynomial

section Period

open Matrix Polynomial

variable {d : ℕ} {c : ℕ}

/-- The reduction mod `c` of the characteristic polynomial is monic. -/
theorem charpolyBar_monic (A : Matrix (Fin d) (Fin d) ℤ) (c : ℕ) :
    (A.charpoly.map (Int.castRingHom (ZMod c))).Monic :=
  A.charpoly_monic.map _

theorem charpolyBar_natDegree (A : Matrix (Fin d) (Fin d) ℤ) (c : ℕ) [Fact c.Prime] :
    (A.charpoly.map (Int.castRingHom (ZMod c))).natDegree = d := by
  rw [(A.charpoly_monic).natDegree_map, A.charpoly_natDegree_eq_dim]
  simp

/-- `AdjoinRoot χ̄_A` is a `ZMod c`-module of rank `d`, hence has `c ^ d` elements. -/
theorem adjoinRoot_card (A : Matrix (Fin d) (Fin d) ℤ) (c : ℕ) [Fact c.Prime]
    [Fintype (AdjoinRoot (A.charpoly.map (Int.castRingHom (ZMod c))))] :
    Fintype.card (AdjoinRoot (A.charpoly.map (Int.castRingHom (ZMod c)))) = c ^ d := by
  have hfr : Module.finrank (ZMod c)
      (AdjoinRoot (A.charpoly.map (Int.castRingHom (ZMod c)))) = d := by
    rw [(AdjoinRoot.powerBasis' (charpolyBar_monic A c)).finrank, AdjoinRoot.powerBasis'_dim,
      charpolyBar_natDegree]
  rw [Module.card_eq_pow_finrank (K := ZMod c), hfr, ZMod.card]

/-- **Frobenius period mod `c`:** if `χ̄_A` is irreducible then `Ā ^ (c ^ d) = Ā` over `ZMod c`,
because `Ā` generates a copy of the field `AdjoinRoot χ̄_A` of order `c ^ d`. -/
theorem mapMatrix_pow_card_pow_dim (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) :
    ((Int.castRingHom (ZMod c)).mapMatrix A) ^ (c ^ d) =
      (Int.castRingHom (ZMod c)).mapMatrix A := by
  haveI : Fact c.Prime := ⟨hc⟩
  haveI : Fact (Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) := ⟨hirr⟩
  set f := A.charpoly.map (Int.castRingHom (ZMod c)) with hf
  set Abar := (Int.castRingHom (ZMod c)).mapMatrix A with hAbar
  have hchar : Abar.charpoly = f := by
    rw [hAbar, hf, RingHom.mapMatrix_apply, Matrix.charpoly_map]
  have hCH : Polynomial.aeval Abar f = 0 := by
    rw [← hchar]; exact Matrix.aeval_self_charpoly Abar
  haveI : Module.Finite (ZMod c) (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' (charpolyBar_monic A c)).basis
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod c)
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot f) = c ^ d := adjoinRoot_card A c
  have hroot : (AdjoinRoot.root f) ^ (c ^ d) = AdjoinRoot.root f := by
    rw [← hcard]; exact FiniteField.pow_card _
  have hdvd : f ∣ (Polynomial.X ^ (c ^ d) - Polynomial.X : (ZMod c)[X]) := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero]
    exact hroot
  obtain ⟨q, hq⟩ := hdvd
  have := congrArg (Polynomial.aeval Abar) hq
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_mul, hCH, zero_mul] at this
  exact sub_eq_zero.1 this

/-- **Period, statement 1's engine:** `A ^ (c ^ d) ≡ A (mod c)` entrywise. -/
theorem pow_card_pow_dim_congr (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (i j : Fin d) :
    (c : ℤ) ∣ (A ^ (c ^ d) - A) i j := by
  refine TeichmullerCongruence.dvd_of_mapMatrix_eq ?_ i j
  rw [map_pow]
  exact mapMatrix_pow_card_pow_dim A hc hirr

end Period


section Integral

open Matrix Polynomial

variable {d : ℕ} {c : ℕ}

/-- Chained Dold: the charpoly coefficients along the Frobenius tower are constant mod `c ^ (n+1)`
from step `n` on. -/
theorem charpoly_coeff_tower_congr (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (n k j : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ (A ^ (c ^ (n + k))).charpoly.coeff j - (A ^ (c ^ n)).charpoly.coeff j := by
  induction k with
  | zero => simp
  | succ m ih =>
    have h := ExteriorDold.charpoly_coeff_prime_pow_congr A hc (n + m) j
    have h' : (c : ℤ) ^ (n + 1) ∣
        (A ^ (c ^ (n + m + 1))).charpoly.coeff j - (A ^ (c ^ (n + m))).charpoly.coeff j :=
      dvd_trans (pow_dvd_pow _ (by omega)) h
    have := dvd_add h' ih
    simpa [show n + (m + 1) = n + m + 1 by omega] using this

/-- Mod `c` the whole Frobenius tower has the same characteristic polynomial. -/
theorem charpolyBar_tower (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime) (k : ℕ) :
    (A ^ (c ^ k)).charpoly.map (Int.castRingHom (ZMod c)) =
      A.charpoly.map (Int.castRingHom (ZMod c)) := by
  ext j
  simp only [Polynomial.coeff_map, eq_intCast]
  have h := charpoly_coeff_tower_congr A hc 0 k j
  simp only [pow_zero, pow_one, Nat.zero_add] at h
  have : (((A ^ (c ^ k)).charpoly.coeff j - A.charpoly.coeff j : ℤ) : ZMod c) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by simpa using h)
  rw [Int.cast_sub, sub_eq_zero] at this
  exact this

/-- With `χ̄_B` irreducible, no nonzero polynomial of degree `< d` over `ZMod c` annihilates `B̄`:
`χ̄_B` is the minimal polynomial of `B̄`. -/
theorem eq_zero_of_aeval_mapMatrix_eq_zero (B : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (B.charpoly.map (Int.castRingHom (ZMod c))))
    {r : (ZMod c)[X]} (hdeg : r.natDegree < d)
    (hr : Polynomial.aeval ((Int.castRingHom (ZMod c)).mapMatrix B) r = 0) : r = 0 := by
  haveI : Fact c.Prime := ⟨hc⟩
  by_contra hne
  set Bbar := (Int.castRingHom (ZMod c)).mapMatrix B with hBbar
  set f := B.charpoly.map (Int.castRingHom (ZMod c)) with hf
  have hfB : Polynomial.aeval Bbar f = 0 := by
    have : Bbar.charpoly = f := by rw [hBbar, hf, RingHom.mapMatrix_apply, Matrix.charpoly_map]
    rw [← this]; exact Matrix.aeval_self_charpoly Bbar
  have hnd : f.natDegree = d := charpolyBar_natDegree B c
  have hnotdvd : ¬ f ∣ r := fun hdvd => by
    have := Polynomial.natDegree_le_of_dvd hdvd hne
    omega
  have hcop : IsCoprime f r := (dvd_or_isCoprime f r hirr).resolve_left hnotdvd
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (Polynomial.aeval Bbar) huv
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  simp only [map_add, map_mul, hfB, hr, mul_zero, add_zero, map_one, zero_add] at key
  exact zero_ne_one key

/-- **Integral injectivity:** if `χ̄_B` is irreducible mod `c` and a polynomial `r ∈ ℤ[X]` of degree
`< d` has `r(B) ≡ 0 (mod c ^ m)` entrywise, then all coefficients of `r` are divisible by `c ^ m`. -/
theorem coeff_dvd_of_aeval_dvd (B : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (B.charpoly.map (Int.castRingHom (ZMod c)))) :
    ∀ (m : ℕ) (r : Polynomial ℤ), r.natDegree < d →
      (∀ i j, (c : ℤ) ^ m ∣ (Polynomial.aeval B r) i j) → ∀ i, (c : ℤ) ^ m ∣ r.coeff i := by
  haveI : Fact c.Prime := ⟨hc⟩
  intro m
  induction m with
  | zero => intro r _ _ i; simp
  | succ m ih =>
    intro r hdeg hdvd
    -- step 1: every coefficient of `r` is divisible by `c`
    have h1 : ∀ i, (c : ℤ) ∣ r.coeff i := by
      have hmap : Polynomial.aeval ((Int.castRingHom (ZMod c)).mapMatrix B)
          (r.map (Int.castRingHom (ZMod c))) = 0 := by
        ext i j
        have h0 : ((((Polynomial.aeval B r) i j : ℤ)) : ZMod c) = 0 := by
          refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ?_
          exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) (hdvd i j)
        have hcomm : (Int.castRingHom (ZMod c)).mapMatrix (Polynomial.aeval B r)
            = Polynomial.aeval ((Int.castRingHom (ZMod c)).mapMatrix B)
              (r.map (Int.castRingHom (ZMod c))) := by
          rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map,
            Polynomial.hom_eval₂]
          congr 1
          exact RingHom.ext_int _ _
        rw [← hcomm]
        simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using h0
      have hz : r.map (Int.castRingHom (ZMod c)) = 0 := by
        refine eq_zero_of_aeval_mapMatrix_eq_zero B hc hirr ?_ hmap
        exact lt_of_le_of_lt (Polynomial.natDegree_map_le) hdeg
      intro i
      have := congrArg (fun p => Polynomial.coeff p i) hz
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    obtain ⟨r₁, hr₁⟩ := (Polynomial.C_dvd_iff_dvd_coeff (c : ℤ) r).2 h1
    have hcne : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne_zero
    have hdeg₁ : r₁.natDegree < d := by
      have : r.natDegree = r₁.natDegree := by rw [hr₁, Polynomial.natDegree_C_mul hcne]
      omega
    have hdvd₁ : ∀ i j, (c : ℤ) ^ m ∣ (Polynomial.aeval B r₁) i j := by
      intro i j
      have hev : Polynomial.aeval B r = (c : ℤ) • Polynomial.aeval B r₁ := by
        rw [hr₁, map_mul, Polynomial.aeval_C, Algebra.smul_def]
      have := hdvd i j
      rw [hev] at this
      simp only [Matrix.smul_apply, smul_eq_mul, pow_succ'] at this
      exact (mul_dvd_mul_iff_left hcne).1 this
    intro i
    have := ih r₁ hdeg₁ hdvd₁ i
    rw [hr₁]
    simp only [Polynomial.coeff_C_mul, pow_succ']
    exact mul_dvd_mul_left _ this

end Integral

/-- **Period:** with `χ_A` irreducible mod `c`, `A^(c^(n+d)) ≡ A^(c^n) (mod c^(n+1))`. -/
theorem pow_prime_pow_add_card_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ}
    (hc : c.Prime) (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ)
    (i j : Fin d) :
    (c : ℤ) ^ (n + 1) ∣ (A ^ (c ^ (n + d))) i j - (A ^ (c ^ n)) i j := by
  have key : ∀ n : ℕ, ∀ i j : Fin d,
      (c : ℤ) ^ (n + 1) ∣ (A ^ (c ^ (n + d)) - A ^ (c ^ n)) i j := by
    intro n
    induction n with
    | zero => intro i j; simpa using pow_card_pow_dim_congr A hc hirr i j
    | succ m ih =>
      intro i j
      have hcomm : Commute (A ^ (c ^ (m + d))) (A ^ (c ^ m)) :=
        (Commute.refl A).pow_pow _ _
      have h := TeichmullerCongruence.pow_congr_lift hcomm (c := c) (e := m + 1)
        (by omega) ih i j
      have e1 : (A ^ (c ^ (m + d))) ^ c = A ^ (c ^ (m + 1 + d)) := by
        rw [← pow_mul, ← pow_succ]
        ring_nf
      have e2 : (A ^ (c ^ m)) ^ c = A ^ (c ^ (m + 1)) := by
        rw [← pow_mul, ← pow_succ]
      rw [e1, e2] at h
      exact h
  simpa [Matrix.sub_apply] using key n i j

/-- **Orbit sum is scalar:** `Σ_(k<d) A^(c^(n+k)) ≡ tr(A^(c^n))·I (mod c^(n+1))`. -/
theorem orbit_sum_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ) (i j : Fin d) :
    (c : ℤ) ^ (n + 1) ∣
      (∑ k ∈ Finset.range d, A ^ (c ^ (n + k))) i j - (A ^ (c ^ n)).trace * (1 : Matrix (Fin d) (Fin d) ℤ) i j := by
  sorry

/-- **Off-diagonal entries of the orbit sum vanish** (the input to Theorem A). -/
theorem orbit_sum_entry_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ) {i j : Fin d}
    (hij : i ≠ j) :
    (c : ℤ) ^ (n + 1) ∣ ∑ k ∈ Finset.range d, (A ^ (c ^ (n + k))) i j := by
  sorry

end LeanFormalizations.Mills.OrbitSum

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

/-- Irreducibility of `χ̄_A` forces the dimension to be positive. -/
theorem pos_of_irreducible {A : Matrix (Fin d) (Fin d) ℤ} {c : ℕ} [Fact c.Prime]
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) : 0 < d := by
  by_contra h
  have hd : d = 0 := by omega
  have hdeg : (A.charpoly.map (Int.castRingHom (ZMod c))).natDegree = 0 := by
    rw [charpolyBar_natDegree]; omega
  have h1 : (A.charpoly.map (Int.castRingHom (ZMod c))) = 1 := by
    have := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [this]
    have hlc := charpolyBar_monic A c
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hlc
    rw [hlc, map_one]
  exact hirr.not_isUnit (h1 ▸ isUnit_one)

/-- **The Frobenius orbit consists of roots:** `χ_B(B^(c^k)) ≡ 0 (mod c^(n+1))` for `B = A^(c^n)`
and every `k`. -/
theorem aeval_charpoly_tower (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime) (n k : ℕ)
    (i j : Fin d) :
    (c : ℤ) ^ (n + 1) ∣
      (Polynomial.aeval (A ^ (c ^ (n + k))) (A ^ (c ^ n)).charpoly) i j := by
  match k with
  | 0 => simp [Matrix.aeval_self_charpoly]
  | (m + 1) =>
    have h1 : (c : ℤ) ^ (n + 1) ∣
        (Polynomial.aeval (A ^ (c ^ (n + m + 1))) (A ^ (c ^ (n + m))).charpoly) i j :=
      dvd_trans (pow_dvd_pow _ (by omega))
        (ExteriorDold.aeval_charpoly_prime_pow_congr A hc (n + m) i j)
    have h2 : (c : ℤ) ^ (n + 1) ∣
        (Polynomial.aeval (A ^ (c ^ (n + m + 1)))
          ((A ^ (c ^ n)).charpoly - (A ^ (c ^ (n + m))).charpoly)) i j := by
      refine ExteriorDold.dvd_aeval_entry _ _ _ (fun t => ?_) i j
      rw [Polynomial.coeff_sub]
      simpa using (charpoly_coeff_tower_congr A hc n m t).neg_right
    have h3 := dvd_add h1 h2
    rw [map_sub] at h3
    simp only [Matrix.sub_apply] at h3
    have heq : n + (m + 1) = n + m + 1 := by omega
    rw [heq]
    simpa using h3

/-- The Frobenius substitution `X ↦ X^(c^k)` sends `χ̄_B` into the ideal it generates, over
`ZMod (c^(n+1))`: this is what makes `x^(c^k)` a root of `χ̄_B` in `AdjoinRoot χ̄_B`. -/
theorem charpoly_comp_dvd (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n k : ℕ) :
    ((A ^ (c ^ n)).charpoly.map (Int.castRingHom (ZMod (c ^ (n + 1))))) ∣
      (((A ^ (c ^ n)).charpoly.comp (Polynomial.X ^ (c ^ k))).map
        (Int.castRingHom (ZMod (c ^ (n + 1))))) := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hd : 0 < d := pos_of_irreducible hirr
  set B := A ^ (c ^ n) with hB
  have hirrB : Irreducible (B.charpoly.map (Int.castRingHom (ZMod c))) := by
    rw [hB, charpolyBar_tower A hc]; exact hirr
  set g := B.charpoly with hg
  have hgm : g.Monic := B.charpoly_monic
  set G := g.comp (Polynomial.X ^ (c ^ k)) with hG
  have hdiv : G %ₘ g + g * (G /ₘ g) = G := Polynomial.modByMonic_add_div G g
  have hdegg : g.natDegree = d := by rw [hg, B.charpoly_natDegree_eq_dim]; simp
  have hdeg : (G %ₘ g).natDegree < d := by
    rcases eq_or_ne (G %ₘ g) 0 with h | h
    · rw [h]; simpa using hd
    · have := Polynomial.natDegree_lt_natDegree h (Polynomial.degree_modByMonic_lt G hgm)
      omega
  have hev : ∀ i j, (c : ℤ) ^ (n + 1) ∣ (Polynomial.aeval B (G %ₘ g)) i j := by
    intro i j
    have hap := congrArg (Polynomial.aeval B) hdiv
    rw [map_add, map_mul] at hap
    have hCH : Polynomial.aeval B g = 0 := by rw [hg]; exact Matrix.aeval_self_charpoly B
    rw [hCH, zero_mul, add_zero] at hap
    have hGB : Polynomial.aeval B G = Polynomial.aeval (A ^ (c ^ (n + k))) g := by
      rw [hG, Polynomial.aeval_comp]
      congr 1
      rw [hB, map_pow, Polynomial.aeval_X, ← pow_mul, ← pow_add]
    rw [hap, hGB]
    exact aeval_charpoly_tower A hc n k i j
  have hco := coeff_dvd_of_aeval_dvd B hc hirrB (n + 1) (G %ₘ g) hdeg hev
  have hzero : (G %ₘ g).map (Int.castRingHom (ZMod (c ^ (n + 1)))) = 0 := by
    ext t
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ?_
    have := hco t
    push_cast
    exact_mod_cast this
  have := congrArg (Polynomial.map (Int.castRingHom (ZMod (c ^ (n + 1))))) hdiv
  rw [Polynomial.map_add, Polynomial.map_mul, hzero, zero_add] at this
  exact ⟨_, this.symm⟩

end Integral


section Factorization

open Polynomial

variable {T : Type*} [CommRing T]

/-- Over any commutative ring, a family of roots whose pairwise differences are units splits off
as a product of linear factors. -/
theorem prod_X_sub_C_dvd_of_roots {ι : Type*} [DecidableEq ι] (p : T[X]) (s : Finset ι) (r : ι → T)
    (hroot : ∀ k ∈ s, p.IsRoot (r k))
    (hu : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → IsUnit (r k - r l)) :
    (∏ k ∈ s, (X - C (r k))) ∣ p := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h, hh⟩ := ih (fun k hk => hroot k (Finset.mem_insert_of_mem hk))
      (fun k hk l hl hkl => hu k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl)
    have hpa : p.eval (r a) = 0 := hroot a (Finset.mem_insert_self _ _)
    rw [hh, eval_mul] at hpa
    have hunit : IsUnit ((∏ k ∈ s, (X - C (r k))).eval (r a)) := by
      rw [eval_prod]
      refine Finset.prod_induction _ IsUnit (fun x y => IsUnit.mul) isUnit_one fun k hk => ?_
      have hne : a ≠ k := fun hak => ha (hak ▸ hk)
      simpa using hu a (Finset.mem_insert_self _ _) k (Finset.mem_insert_of_mem hk) hne
    have hz : h.eval (r a) = 0 := (hunit.mul_right_eq_zero).1 hpa
    obtain ⟨h', hh'⟩ := (dvd_iff_isRoot (a := r a) (p := h)).2 hz
    refine ⟨h', ?_⟩
    rw [Finset.prod_insert ha, hh, hh']
    ring

/-- A monic polynomial of degree `m` with `m` roots of pairwise unit difference is exactly the
product of the corresponding linear factors. -/
theorem eq_prod_X_sub_C_of_roots {ι : Type*} [DecidableEq ι] (p : T[X]) (hp : p.Monic)
    (s : Finset ι) (r : ι → T) (hcard : s.card = p.natDegree)
    (hroot : ∀ k ∈ s, p.IsRoot (r k))
    (hu : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → IsUnit (r k - r l)) :
    p = ∏ k ∈ s, (X - C (r k)) := by
  nontriviality T
  obtain ⟨h, hh⟩ := prod_X_sub_C_dvd_of_roots p s r hroot hu
  have hmonic : (∏ k ∈ s, (X - C (r k))).Monic := monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hdeg : (∏ k ∈ s, (X - C (r k))).natDegree = s.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
    simp
  have hh' : h.Monic := Polynomial.Monic.of_mul_monic_left hmonic (hh ▸ hp)
  have : p.natDegree = s.card + h.natDegree := by
    rw [hh, Polynomial.Monic.natDegree_mul hmonic hh', hdeg]
  have hz : h.natDegree = 0 := by omega
  have : h = 1 := (Polynomial.Monic.natDegree_eq_zero hh').1 hz
  rw [hh, this, mul_one]

end Factorization


section FrobeniusOrbit

open Polynomial

/-- `AdjoinRoot f` for a monic `f` over `ZMod c` has `c ^ deg f` elements. -/
theorem adjoinRoot_card_of_monic {c : ℕ} [Fact c.Prime] {f : (ZMod c)[X]} (hm : f.Monic)
    [Fintype (AdjoinRoot f)] : Fintype.card (AdjoinRoot f) = c ^ f.natDegree := by
  have hfr : Module.finrank (ZMod c) (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim]
  rw [Module.card_eq_pow_finrank (K := ZMod c), hfr, ZMod.card]

/-- **The Frobenius orbit of the generator is free:** in the field `AdjoinRoot f` of order
`c ^ deg f`, the elements `root f ^ (c ^ i)` for `i < deg f` are pairwise distinct. -/
theorem root_pow_frobenius_injOn {c : ℕ} [Fact c.Prime] {f : (ZMod c)[X]} (hm : f.Monic)
    (hirr : Irreducible f) {i j : ℕ} (hi : i < f.natDegree) (hj : j < f.natDegree) (hij : i ≠ j) :
    (AdjoinRoot.root f) ^ (c ^ i) ≠ (AdjoinRoot.root f) ^ (c ^ j) := by
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  set K := AdjoinRoot f with hK
  set y : K := AdjoinRoot.root f with hy
  haveI : Module.Finite (ZMod c) K := Module.Finite.of_basis (AdjoinRoot.powerBasis' hm).basis
  haveI : Finite K := Module.finite_of_finite (ZMod c)
  haveI : Fintype K := Fintype.ofFinite _
  have hcard : Fintype.card K = c ^ f.natDegree := adjoinRoot_card_of_monic hm
  haveI : CharP K c := charP_of_injective_algebraMap (algebraMap (ZMod c) K).injective c
  haveI : ExpChar K c := ExpChar.prime Fact.out
  -- the crux: `y ^ (c ^ m) = y` with `1 ≤ m < deg f` is impossible
  have crux : ∀ m : ℕ, 0 < m → m < f.natDegree → y ^ (c ^ m) ≠ y := by
    intro m hm0 hmd hfix
    have hψ : ∀ z : K, z ^ (c ^ m) = z := by
      intro z
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := f) z
      have hcomp : (iterateFrobenius K c m).comp (algebraMap (ZMod c) K)
          = algebraMap (ZMod c) K := by
        ext a
        rw [RingHom.comp_apply, iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]
      have h1 : iterateFrobenius K c m (Polynomial.aeval y p)
          = Polynomial.eval₂ ((iterateFrobenius K c m).comp (algebraMap (ZMod c) K))
            (iterateFrobenius K c m y) p := by
        rw [Polynomial.aeval_def]
        exact Polynomial.hom_eval₂ p _ _ y
      have h2 : iterateFrobenius K c m y = y := by rw [iterateFrobenius_def]; exact hfix
      rw [hcomp, h2, ← Polynomial.aeval_def] at h1
      rw [← AdjoinRoot.aeval_eq p, ← iterateFrobenius_def]
      exact h1
    -- every element is a root of `X ^ (c ^ m) - X`
    set P : K[X] := X ^ (c ^ m) - X with hP
    have hcm : 1 < c ^ m := by
      have : 1 < c := Fact.out (p := c.Prime) |>.one_lt
      exact Nat.one_lt_pow (by omega) this
    have hPdeg : P.natDegree = c ^ m := by
      have hXd : (X : K[X]).natDegree < ((X : K[X]) ^ (c ^ m)).natDegree := by
        rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; omega
      rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hXd, Polynomial.natDegree_X_pow]
    have hPne : P ≠ 0 := fun h => by
      have := congrArg (fun q => Polynomial.coeff q (c ^ m)) h
      simp [hP, Polynomial.coeff_X, show (1 : ℕ) ≠ c ^ m by omega] at this
    have hsub : (Finset.univ : Finset K) ⊆ P.roots.toFinset := by
      intro z _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
      simp [hP, Polynomial.IsRoot, hψ z]
    have hle : (Fintype.card K) ≤ c ^ m := by
      calc (Fintype.card K) = (Finset.univ : Finset K).card := by simp
        _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
        _ ≤ P.natDegree := P.card_roots'
        _ = c ^ m := hPdeg
    rw [hcard] at hle
    have : c ^ m < c ^ f.natDegree :=
      Nat.pow_lt_pow_right (Fact.out (p := c.Prime)).one_lt hmd
    omega
  intro heq
  rcases lt_or_gt_of_ne hij with h | h
  · have hinj : Function.Injective (fun z : K => z ^ (c ^ i)) := by
      intro a b hab
      have hb : iterateFrobenius K c i a = iterateFrobenius K c i b := by
        simp only [iterateFrobenius_def]; exact hab
      exact (iterateFrobenius K c i).injective hb
    refine crux (j - i) (by omega) (by omega) (hinj ?_)
    show (y ^ c ^ (j - i)) ^ c ^ i = y ^ c ^ i
    rw [← pow_mul, ← pow_add]
    rw [show j - i + i = j by omega]
    exact heq.symm
  · have hinj : Function.Injective (fun z : K => z ^ (c ^ j)) := by
      intro a b hab
      have hb : iterateFrobenius K c j a = iterateFrobenius K c j b := by
        simp only [iterateFrobenius_def]; exact hab
      exact (iterateFrobenius K c j).injective hb
    refine crux (i - j) (by omega) (by omega) (hinj ?_)
    show (y ^ c ^ (i - j)) ^ c ^ j = y ^ c ^ j
    rw [← pow_mul, ← pow_add]
    rw [show i - j + j = i by omega]
    exact heq

end FrobeniusOrbit


section Assembly

open Matrix Polynomial

variable {d : ℕ}

/-- `nextCoeff` commutes with coefficient maps on monic polynomials. -/
theorem nextCoeff_map_of_monic {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {p : R[X]} (hp : p.Monic) : (p.map φ).nextCoeff = φ p.nextCoeff := by
  unfold Polynomial.nextCoeff
  rw [hp.natDegree_map]
  split_ifs with h
  · simp
  · simp [Polynomial.coeff_map]

/-- Reduction `ZMod N → ZMod c` has kernel `(c)`. -/
theorem dvd_of_castHom_eq_zero {c N : ℕ} [NeZero N] (h : c ∣ N) {a : ZMod N}
    (ha : ZMod.castHom h (ZMod c) a = 0) : (c : ZMod N) ∣ a := by
  have hval : ((a.val : ℕ) : ZMod N) = a := ZMod.natCast_rightInverse a
  have h0 : ((a.val : ℕ) : ZMod c) = 0 := by
    rw [← hval] at ha
    rwa [map_natCast] at ha
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h0
  refine ⟨(t : ZMod N), ?_⟩
  rw [← hval, ht]
  push_cast
  ring

/-- **The orbit-sum identity, at the level of polynomials over `ZMod (c ^ (n+1))`.** -/
theorem orbit_sum_poly (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ) :
    ((A ^ (c ^ n)).charpoly.map (Int.castRingHom (ZMod (c ^ (n + 1))))) ∣
      ((∑ k ∈ Finset.range d, (Polynomial.X : (ZMod (c ^ (n + 1)))[X]) ^ (c ^ k))
        - Polynomial.C (((A ^ (c ^ n)).trace : ℤ) : ZMod (c ^ (n + 1)))) := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hd : 0 < d := pos_of_irreducible hirr
  haveI : NeZero (c ^ (n + 1)) := ⟨pow_ne_zero _ hc.ne_zero⟩
  haveI : Nontrivial (ZMod (c ^ (n + 1))) := by
    have : 1 < c ^ (n + 1) := Nat.one_lt_pow (by omega) hc.one_lt
    exact ZMod.nontrivial_iff.2 (by omega)
  set B := A ^ (c ^ n) with hB
  set φ : ℤ →+* ZMod (c ^ (n + 1)) := Int.castRingHom _ with hφ
  set g : Polynomial ℤ := B.charpoly with hg
  set gb : (ZMod (c ^ (n + 1)))[X] := g.map φ with hgb
  have hgm : g.Monic := B.charpoly_monic
  have hgbm : gb.Monic := hgm.map _
  have hgbdeg : gb.natDegree = d := by
    rw [hgb, hgm.natDegree_map, hg, B.charpoly_natDegree_eq_dim]; simp
  have hcd : c ∣ c ^ (n + 1) := dvd_pow_self c (Nat.succ_ne_zero n)
  set ρ : ZMod (c ^ (n + 1)) →+* ZMod c := ZMod.castHom hcd (ZMod c) with hρ
  set gh : (ZMod c)[X] := gb.map ρ with hgh
  have hghA : gh = A.charpoly.map (Int.castRingHom (ZMod c)) := by
    rw [hgh, hgb, Polynomial.map_map]
    have : ρ.comp φ = Int.castRingHom (ZMod c) := RingHom.ext_int _ _
    rw [this, hg, hB, charpolyBar_tower A hc]
  have hirrgh : Irreducible gh := by rw [hghA]; exact hirr
  have hghm : gh.Monic := hgbm.map _
  have hghdeg : gh.natDegree = d := by rw [hghA, charpolyBar_natDegree]
  haveI : Fact (Irreducible gh) := ⟨hirrgh⟩
  set T := AdjoinRoot gb with hT
  set K := AdjoinRoot gh with hK
  set x : T := AdjoinRoot.root gb with hx
  set y : K := AdjoinRoot.root gh with hy
  -- the reduction map `T → K`
  have hlift : gb.eval₂ ((AdjoinRoot.of gh).comp ρ) y = 0 := by
    rw [← Polynomial.eval₂_map]; exact AdjoinRoot.eval₂_root gh
  set π : T →+* K := AdjoinRoot.lift ((AdjoinRoot.of gh).comp ρ) y hlift with hπ
  have hπmk : ∀ p : (ZMod (c ^ (n + 1)))[X], π (AdjoinRoot.mk gb p) = AdjoinRoot.mk gh (p.map ρ) := by
    intro p
    rw [hπ, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
      ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  have hρsurj : Function.Surjective ρ := by
    intro a
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
    exact ⟨(k : ZMod (c ^ (n + 1))), by rw [hρ, map_natCast]⟩
  have hπsurj : Function.Surjective π := by
    intro z
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨p, hp⟩ := Polynomial.map_surjective ρ hρsurj q
    exact ⟨AdjoinRoot.mk gb p, by rw [hπmk, hp]⟩
  haveI : Nontrivial T := π.domain_nontrivial
  have hcnil : ((c : T)) ^ (n + 1) = 0 := by
    have h0 : ((c : ZMod (c ^ (n + 1)))) ^ (n + 1) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have hcast : ((c : T)) = algebraMap (ZMod (c ^ (n + 1))) T (c : ZMod (c ^ (n + 1))) := by
      rw [map_natCast]
    rw [hcast, ← map_pow, h0, map_zero]
  have hker : ∀ z : T, π z = 0 → ∃ w, z = (c : T) * w := by
    intro z hz
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [hπmk, AdjoinRoot.mk_eq_zero] at hz
    obtain ⟨qh, hqh⟩ := hz
    obtain ⟨q, hq⟩ := Polynomial.map_surjective ρ hρsurj qh
    have hzero : (p - gb * q).map ρ = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hq, ← hgh, hqh]
      ring
    have hcoeff : ∀ i, (c : ZMod (c ^ (n + 1))) ∣ (p - gb * q).coeff i := by
      intro i
      refine dvd_of_castHom_eq_zero hcd ?_
      have hcc := congrArg (fun r => Polynomial.coeff r i) hzero
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcc
      exact hcc
    obtain ⟨s, hs⟩ := (Polynomial.C_dvd_iff_dvd_coeff (c : ZMod (c ^ (n + 1))) _).2 hcoeff
    refine ⟨AdjoinRoot.mk gb s, ?_⟩
    have : p = gb * q + Polynomial.C (c : ZMod (c ^ (n + 1))) * s := by
      rw [← hs]; ring
    rw [this, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, zero_add,
      AdjoinRoot.mk_C, map_natCast]
  have hunit : ∀ u : T, π u ≠ 0 → IsUnit u := by
    intro u hu
    obtain ⟨k, hk⟩ := (isUnit_iff_exists_inv.1 (Ne.isUnit hu))
    obtain ⟨v, hv⟩ := hπsurj k
    have h1 : π (u * v - 1) = 0 := by rw [map_sub, map_mul, hv, hk, map_one, sub_self]
    obtain ⟨w, hw⟩ := hker _ h1
    have h2 : u * v = 1 + (c : T) * w := by rw [← hw]; ring
    have h3 : IsNilpotent ((c : T) * w) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow, hcnil, zero_mul]
    have h4 : IsUnit (u * v) := by rw [h2]; exact h3.isUnit_one_add
    exact isUnit_of_mul_isUnit_left h4
  -- the `d` roots
  set P : T[X] := gb.map (AdjoinRoot.of gb) with hP
  have hPm : P.Monic := hgbm.map _
  have hPdeg : P.natDegree = d := by rw [hP, hgbm.natDegree_map, hgbdeg]
  have hroot : ∀ k : ℕ, P.IsRoot (x ^ (c ^ k)) := by
    intro k
    have hdvd := charpoly_comp_dvd A hc hirr n k
    rw [← hg, ← hgb] at hdvd
    have hmapcomp : (g.comp (Polynomial.X ^ (c ^ k))).map φ
        = gb.comp (Polynomial.X ^ (c ^ k)) := by
      rw [hgb, Polynomial.map_comp]
      simp
    rw [hmapcomp] at hdvd
    obtain ⟨h, hh⟩ := hdvd
    have hz : AdjoinRoot.mk gb (gb.comp (Polynomial.X ^ (c ^ k))) = 0 := by
      rw [hh, map_mul, AdjoinRoot.mk_self, zero_mul]
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_comp] at hz
    simp only [map_pow, Polynomial.aeval_X, AdjoinRoot.aeval_eq, AdjoinRoot.mk_X] at hz
    rw [Polynomial.IsRoot, hP, Polynomial.eval_map, ← AdjoinRoot.algebraMap_eq,
      ← Polynomial.aeval_def]
    exact hz
  have hdiff : ∀ k ∈ Finset.range d, ∀ l ∈ Finset.range d, k ≠ l →
      IsUnit (x ^ (c ^ k) - x ^ (c ^ l)) := by
    intro k hk l hl hkl
    refine hunit _ ?_
    have hπx : π x = y := AdjoinRoot.lift_root _
    rw [map_sub, map_pow, map_pow, hπx]
    rw [sub_ne_zero]
    refine root_pow_frobenius_injOn hghm hirrgh ?_ ?_ hkl
    · rw [hghdeg]; simpa using hk
    · rw [hghdeg]; simpa using hl
  have hfact : P = ∏ k ∈ Finset.range d, (Polynomial.X - Polynomial.C (x ^ (c ^ k))) :=
    eq_prod_X_sub_C_of_roots P hPm (Finset.range d) (fun k => x ^ (c ^ k))
      (by rw [hPdeg]; simp) (fun k _ => hroot k) hdiff
  -- compare the `nextCoeff`s
  have hnext : P.nextCoeff = - ∑ k ∈ Finset.range d, x ^ (c ^ k) := by
    rw [hfact, Polynomial.prod_X_sub_C_nextCoeff]
  have hgbnext : gb.nextCoeff = φ g.nextCoeff := by
    rw [hgb, nextCoeff_map_of_monic _ hgm]
  have hgnext : g.nextCoeff = - B.trace := by
    rw [hg, Matrix.trace_eq_neg_charpoly_nextCoeff (M := B), neg_neg]
  have hnext2 : P.nextCoeff = AdjoinRoot.of gb (φ (- (B.trace))) := by
    rw [hP, nextCoeff_map_of_monic _ hgbm, hgbnext, hgnext]
  have hsum : ∑ k ∈ Finset.range d, x ^ (c ^ k)
      = AdjoinRoot.mk gb (Polynomial.C (((B.trace : ℤ)) : ZMod (c ^ (n + 1)))) := by
    have h5 := hnext.symm.trans hnext2
    rw [map_neg, map_neg, neg_inj] at h5
    rw [h5, AdjoinRoot.mk_C]
    rfl
  rw [← AdjoinRoot.mk_eq_zero, map_sub, ← hsum, map_sum]
  simp only [map_pow, AdjoinRoot.mk_X, ← hx]
  exact sub_self _

end Assembly

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
  haveI : Fact c.Prime := ⟨hc⟩
  haveI : NeZero (c ^ (n + 1)) := ⟨pow_ne_zero _ hc.ne_zero⟩
  obtain ⟨h, hh⟩ := orbit_sum_poly A hc hirr n
  set ψ : Matrix (Fin d) (Fin d) ℤ →+* Matrix (Fin d) (Fin d) (ZMod (c ^ (n + 1))) :=
    (Int.castRingHom (ZMod (c ^ (n + 1)))).mapMatrix with hψ
  set Bb := ψ (A ^ (c ^ n)) with hBb
  have hCH : Polynomial.aeval Bb
      ((A ^ (c ^ n)).charpoly.map (Int.castRingHom (ZMod (c ^ (n + 1))))) = 0 := by
    have hcp : Bb.charpoly = (A ^ (c ^ n)).charpoly.map (Int.castRingHom (ZMod (c ^ (n + 1)))) := by
      rw [hBb, hψ, RingHom.mapMatrix_apply, Matrix.charpoly_map]
    rw [← hcp]; exact Matrix.aeval_self_charpoly Bb
  have key := congrArg (Polynomial.aeval Bb) hh
  rw [map_mul, hCH, zero_mul, map_sub, map_sum] at key
  simp only [map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at key
  have hpow : ∀ k : ℕ, Bb ^ (c ^ k) = ψ (A ^ (c ^ (n + k))) := by
    intro k
    rw [hBb, ← map_pow, ← pow_mul, ← pow_add]
  have hsum : ψ (∑ k ∈ Finset.range d, A ^ (c ^ (n + k)))
      = ∑ k ∈ Finset.range d, Bb ^ (c ^ k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (hpow k).symm
  rw [← hsum, Algebra.algebraMap_eq_smul_one] at key
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij
  have hone : (1 : Matrix (Fin d) (Fin d) (ZMod (c ^ (n + 1)))) i j
      = (((1 : Matrix (Fin d) (Fin d) ℤ) i j : ℤ) : ZMod (c ^ (n + 1))) := by
    by_cases hb : i = j <;> simp [Matrix.one_apply, hb]
  rw [hone] at hij
  have hcast : (((∑ k ∈ Finset.range d, A ^ (c ^ (n + k))) i j
      - (A ^ (c ^ n)).trace * (1 : Matrix (Fin d) (Fin d) ℤ) i j : ℤ) : ZMod (c ^ (n + 1))) = 0 := by
    push_cast
    rw [← hij]
    rw [hψ, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (c ^ (n + 1))).1 hcast
  exact_mod_cast this

/-- **Off-diagonal entries of the orbit sum vanish** (the input to Theorem A). -/
theorem orbit_sum_entry_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c)))) (n : ℕ) {i j : Fin d}
    (hij : i ≠ j) :
    (c : ℤ) ^ (n + 1) ∣ ∑ k ∈ Finset.range d, (A ^ (c ^ (n + k))) i j := by
  have h := orbit_sum_congr A hc hirr n i j
  rw [Matrix.one_apply_ne hij, mul_zero, sub_zero, Matrix.sum_apply] at h
  exact h

end LeanFormalizations.Mills.OrbitSum

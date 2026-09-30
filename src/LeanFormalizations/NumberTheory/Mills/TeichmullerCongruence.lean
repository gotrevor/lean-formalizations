/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedWindow

/-!
# Phase 47: `A^(c^n)` is eventually periodic `c`-adically (Teichmüller limit, in integers)

Foundation for the limit-point sub-node (R2) of `ShiftedTraceRigidity` (`ROADMAP-PRIME-TOWERS.md` §4-live):
the sequence `A^(c^n)` has finitely many `c`-adic limit points, as a congruence statement about
integer matrices (no `ℤ_c` needed).

## Route
1. Let `A` be invertible mod `c` and `ord = c^a · o` its order in `GL_d(ZMod c)` with `c ∤ o`.  Take `f ≥ 1` with
   `c^f ≡ 1 (mod o)` (e.g. `f = φ(o)`, or `1` if `o = 1`).
2. Base (`n = a`): `A^(c^(a+f)) ≡ A^(c^a) (mod c)`, because `ord ∣ c^a (c^f − 1)`.  More generally the same holds for all `n ≥ a`.
3. Lifting: if `X ≡ Y (mod c^e)` entrywise, `e ≥ 1`, and `X`, `Y` commute (both are powers of `A`), then
   `X^c ≡ Y^c (mod c^(e+1))`.  Write `X = Y + c^e Z` with `Z` a polynomial in `A`; in the binomial
   expansion every term but `Y^c` is divisible by `c^(e+1)` (`c ∣ binom(c, i)` for `0 < i < c`, and
   `c^(ce) ⊇ c^(e+1)`).
4. Induction on `n ≥ a` with `A^(c^(n+1+f)) = (A^(c^(n+f)))^c` gives exponent `n − a + 1`.

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
-/
namespace LeanFormalizations.Mills.TeichmullerCongruence

open Finset

/-- Entrywise congruence mod `c` is the same as equality of the reductions to `ZMod c`. -/
theorem mapMatrix_eq_of_dvd {d c : ℕ} {X Y : Matrix (Fin d) (Fin d) ℤ}
    (h : ∀ i j, (c : ℤ) ∣ (X - Y) i j) :
    (Int.castRingHom (ZMod c)).mapMatrix X = (Int.castRingHom (ZMod c)).mapMatrix Y := by
  ext i j
  have h0 : ((((X - Y) i j : ℤ)) : ZMod c) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h i j)
  simp only [Matrix.sub_apply, Int.cast_sub, sub_eq_zero] at h0
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using h0

/-- Converse of `mapMatrix_eq_of_dvd`. -/
theorem dvd_of_mapMatrix_eq {d c : ℕ} {X Y : Matrix (Fin d) (Fin d) ℤ}
    (h : (Int.castRingHom (ZMod c)).mapMatrix X = (Int.castRingHom (ZMod c)).mapMatrix Y)
    (i j : Fin d) : (c : ℤ) ∣ (X - Y) i j := by
  have h0 : (((X i j : ℤ)) : ZMod c) = ((Y i j : ℤ) : ZMod c) := by
    have := congrFun (congrFun h i) j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
  have : ((((X - Y) i j : ℤ)) : ZMod c) = 0 := by
    simp only [Matrix.sub_apply, Int.cast_sub, h0, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this

/-- The geometric-sum cofactor of `X ^ c - Y ^ c` is itself divisible by `c` once `X ≡ Y (mod c)`:
mod `c` every one of its `c` terms collapses to `Y ^ (c - 1)`. -/
theorem dvd_geomSum {d c : ℕ} {X Y : Matrix (Fin d) (Fin d) ℤ}
    (h : ∀ i j, (c : ℤ) ∣ (X - Y) i j) (i j : Fin d) :
    (c : ℤ) ∣ (∑ k ∈ range c, X ^ k * Y ^ (c - 1 - k)) i j := by
  set ψ : Matrix (Fin d) (Fin d) ℤ →+* Matrix (Fin d) (Fin d) (ZMod c) :=
    (Int.castRingHom (ZMod c)).mapMatrix with hψ
  have hXY : ψ X = ψ Y := mapMatrix_eq_of_dvd h
  have hsum : ψ (∑ k ∈ range c, X ^ k * Y ^ (c - 1 - k)) = 0 := by
    rw [map_sum]
    have hterm : ∀ k ∈ range c, ψ (X ^ k * Y ^ (c - 1 - k)) = ψ Y ^ (c - 1) := by
      intro k hk
      have hk' : k < c := mem_range.1 hk
      rw [map_mul, map_pow, map_pow, hXY, ← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_range]
    ext i' j'
    simp [nsmul_eq_mul, ZMod.natCast_self]
  have h0 : (((∑ k ∈ range c, X ^ k * Y ^ (c - 1 - k)) i j : ℤ) : ZMod c) = 0 := by
    have h1 : ψ (∑ k ∈ range c, X ^ k * Y ^ (c - 1 - k)) i j = 0 := by
      rw [hsum]; rfl
    exact h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0

/-- **Teichmüller lifting step.**  Commuting integer matrices congruent mod `c ^ e` (`e ≥ 1`)
have `c`-th powers congruent mod `c ^ (e + 1)`. -/
theorem pow_congr_lift {d c : ℕ} {X Y : Matrix (Fin d) (Fin d) ℤ} (hcomm : Commute X Y)
    {e : ℕ} (he : 1 ≤ e) (h : ∀ i j, (c : ℤ) ^ e ∣ (X - Y) i j) (i j : Fin d) :
    (c : ℤ) ^ (e + 1) ∣ (X ^ c - Y ^ c) i j := by
  have hmod : ∀ i j, (c : ℤ) ∣ (X - Y) i j := fun i j =>
    dvd_trans (dvd_pow_self (c : ℤ) (by omega)) (h i j)
  have hfac : X ^ c - Y ^ c = (∑ k ∈ range c, X ^ k * Y ^ (c - 1 - k)) * (X - Y) :=
    (hcomm.geom_sum₂_mul c).symm
  rw [hfac, Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ => ?_
  have := mul_dvd_mul (dvd_geomSum hmod i k) (h k j)
  calc (c : ℤ) ^ (e + 1) = (c : ℤ) * (c : ℤ) ^ e := by ring
    _ ∣ _ := this

theorem pow_prime_pow_period_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hunit : ¬ (c : ℤ) ∣ A.det) :
    ∃ f a : ℕ, 1 ≤ f ∧ ∀ n ≥ a, ∀ i j,
      (c : ℤ) ^ (n - a + 1) ∣ (A ^ (c ^ (n + f)) - A ^ (c ^ n)) i j := by
  haveI : Fact c.Prime := ⟨hc⟩
  set φ : ℤ →+* ZMod c := Int.castRingHom (ZMod c) with hφ
  set D : Matrix (Fin d) (Fin d) (ZMod c) := φ.mapMatrix A with hD
  have hdetD : IsUnit D.det := by
    have hmd : D.det = φ A.det := by rw [hD]; exact (RingHom.map_det φ A).symm
    rw [hmd]
    refine Ne.isUnit ?_
    simpa [hφ, ZMod.intCast_zmod_eq_zero_iff_dvd] using hunit
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det D).2 hdetD
  obtain ⟨N, hN⟩ : ∃ N, N = Nat.card (GL (Fin d) (ZMod c)) := ⟨_, rfl⟩
  have hNpos : 0 < N := by rw [hN]; exact Nat.card_pos
  have hNne : N ≠ 0 := hNpos.ne'
  have huN : u ^ N = 1 := by rw [hN]; exact pow_card_eq_one'
  obtain ⟨a, ha⟩ : ∃ a, a = N.factorization c := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = N / c ^ (N.factorization c) := ⟨_, rfl⟩
  have hsplit : c ^ a * M = N := by
    rw [ha, hM]; exact Nat.ordProj_mul_ordCompl_eq_self N c
  have hMdvd : ¬ (c ∣ M) := by rw [hM]; exact Nat.not_dvd_ordCompl hc hNne
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, mul_zero] at hsplit; exact absurd hsplit.symm hNne
    · exact h
  obtain ⟨f, hf⟩ : ∃ f, f = Nat.totient M := ⟨_, rfl⟩
  have hfpos : 1 ≤ f := by rw [hf]; exact Nat.totient_pos.2 hMpos
  have hcop : Nat.Coprime c M := (Nat.Prime.coprime_iff_not_dvd hc).2 hMdvd
  obtain ⟨s, hs⟩ : ∃ s, c ^ f = 1 + M * s := by
    have hmod : c ^ f ≡ 1 [MOD M] := by rw [hf]; exact Nat.ModEq.pow_totient hcop
    have h1 : 1 ≤ c ^ f := Nat.one_le_pow _ _ hc.pos
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h1).1 hmod.symm
    exact ⟨t, by omega⟩
  -- the mod-`c` periodicity, for every `n ≥ a`
  have hkey : ∀ n, a ≤ n → D ^ (c ^ (n + f)) = D ^ (c ^ n) := by
    intro n hn
    have hgM : (u ^ (c ^ n)) ^ M = 1 := by
      rw [← pow_mul]
      have hdvd : N ∣ c ^ n * M := by
        rw [← hsplit]
        exact Nat.mul_dvd_mul_right (pow_dvd_pow c hn) M
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, pow_mul, huN, one_pow]
    have hgfix : (u ^ (c ^ n)) ^ (c ^ f) = u ^ (c ^ n) := by
      rw [hs, pow_add, pow_one, pow_mul, hgM, one_pow, mul_one]
    have hval : (u : Matrix (Fin d) (Fin d) (ZMod c)) ^ (c ^ (n + f)) =
        (u : Matrix (Fin d) (Fin d) (ZMod c)) ^ (c ^ n) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
      congr 1
      rw [pow_add, pow_mul, hgfix]
    rwa [hu] at hval
  refine ⟨f, a, hfpos, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro i j
      have h1 : ∀ i j, (c : ℤ) ∣ (A ^ (c ^ (a + f)) - A ^ (c ^ a)) i j := by
        refine fun i j => dvd_of_mapMatrix_eq ?_ i j
        rw [map_pow, map_pow]
        exact hkey a le_rfl
      simpa using h1 i j
  | succ n hn ih =>
      intro i j
      have hcomm : Commute (A ^ (c ^ (n + f))) (A ^ (c ^ n)) :=
        (Commute.refl A).pow_pow _ _
      have he : 1 ≤ n - a + 1 := by omega
      have hlift := pow_congr_lift hcomm he ih i j
      have e1 : (A ^ (c ^ (n + f))) ^ c = A ^ (c ^ (n + 1 + f)) := by
        rw [← pow_mul, ← pow_succ]
        congr 2
        omega
      have e2 : (A ^ (c ^ n)) ^ c = A ^ (c ^ (n + 1)) := by
        rw [← pow_mul, ← pow_succ]
      rw [e1, e2] at hlift
      have e3 : n - a + 1 + 1 = n + 1 - a + 1 := by omega
      rwa [e3] at hlift

end LeanFormalizations.Mills.TeichmullerCongruence

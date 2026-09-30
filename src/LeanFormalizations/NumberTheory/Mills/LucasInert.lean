/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasPrimePow

/-!
# Phase 36: `U_(c^n)(P,Q) + h` is composite i.o. at every odd prime `c` inert in `ℚ(√D)`

Phase 34 did Fibonacci; phase 33 did `c = 2` for all `P, Q` odd (the condition that `2` is inert
in `ℚ(√D)`, `D = P² − 4Q`).  This phase generalizes both at odd `c`.  See
`SWEEP-PRIME-MODULUS.md`.  The sign flip was checked numerically for 756 cases
(`|P|, |Q| ≤ 5`, `c ≤ 13`, `n ≤ 2`).

## Route
`lucasU P Q N = (A^N) 1 0` with `A = !![P, -Q; 1, 0]` (phase 33), `det A = Q`, and
`A^N = !![U_(N+1), −Q U_N; U_N, −Q U_(N−1)]`.
1. `lucasU_frobenius_inert`: `c ∣ U_(c+1)` and `c ∣ U_c + 1`, i.e. `A^(c+1) ≡ Q·I (mod c)`.
   `X² − PX + Q` is irreducible over `ZMod c` because `D` is a non-square, so Frobenius
   swaps its roots: `x^c = x'` and `x^(c+1) = x x' = Q`.  Generalize phase 34's
   `fib_frobenius_inert` proof (which was the case `P = 1`, `Q = −1`).
2. `lucasU_prime_pow_succ_add`: `c^(n+1) ∣ U(c^(n+1)) + U(c^n)`.  Lift step 1 to
   `A^(c^n (c+1)) ≡ Q^(c^n) I (mod c^(n+1))` (binomial), then read entry `(1,0)` of
   `A^(c^(n+1)) · A^(c^n) ≡ Q^(c^n) I`, using `U_(−N) = −Q^(−N) U_N` or directly the product
   formula `U_(a+b) = U_a U_(b+1) − Q U_(a−1) U_b`.  Follow phase 34's `fib_prime_pow_succ_add`.
3. Main theorem as in phase 34, using `pow_dvd_sub_or_add_of_lt_padicValNat` and
   `exists_entry_pow_congr` (with `p ∤ Q` for large `|p_n|`).  `h = 0`: `U(c^n) ∣ U(c^(n+1))`
   plus growth.  `h = ±1`: `U(c^n) ≡ (−1)^n (mod c)` is a unit.  Values may be negative and
   non-monotone, so work with `natAbs` and a large multiple of the period `j` (as in phase 33).

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.LucasInert

open LeanFormalizations.Mills.ThreeAdic LeanFormalizations.Mills.LucasTwoPow Filter Polynomial

/-! ### The companion matrix, made public -/

/-- The companion matrix `A = !![P, -Q; 1, 0]` (a public copy of phase 33's private `lucasMat`). -/
def lucasA (P Q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![P, -Q; 1, 0]

theorem lucasA_pow_apply_one_zero (P Q : ℤ) (N : ℕ) :
    (lucasA P Q ^ N) 1 0 = lucasU P Q N := rfl

theorem lucasA_det (P Q : ℤ) : (lucasA P Q).det = Q := by
  simp [lucasA, Matrix.det_fin_two_of]

theorem lucasA_pow_succ_left (P Q : ℤ) (N : ℕ) (j : Fin 2) :
    (lucasA P Q ^ (N + 1)) 1 j = (lucasA P Q ^ N) 0 j := by
  rw [pow_succ']
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [lucasA]

/-- `(A^N) 0 0 = U(N+1)`. -/
theorem lucasA_pow_apply_zero_zero (P Q : ℤ) (N : ℕ) :
    (lucasA P Q ^ N) 0 0 = lucasU P Q (N + 1) := by
  rw [← lucasA_pow_apply_one_zero, lucasA_pow_succ_left]

/-- `(A^(N+1)) i 1 = -Q * (A^N) i 0`. -/
theorem lucasA_pow_succ_apply_one (P Q : ℤ) (N : ℕ) (i : Fin 2) :
    (lucasA P Q ^ (N + 1)) i 1 = -Q * (lucasA P Q ^ N) i 0 := by
  rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  simp [lucasA]
  ring

/-! ### Step 1: Frobenius at an inert prime -/

/-- The Lucas recursion, read off any root of `X² − P X + Q`. -/
theorem pow_eq_lucasU {R : Type*} [CommRing R] (P Q : ℤ) {x : R}
    (hx : x ^ 2 = (P : R) * x - (Q : R)) (N : ℕ) :
    x ^ (N + 1) = ((lucasU P Q (N + 1) : ℤ) : R) * x - (Q : R) * ((lucasU P Q N : ℤ) : R) := by
  induction N with
  | zero =>
      have h0 : lucasU P Q 0 = 0 := by simp [lucasU, Matrix.one_apply]
      have h1 : lucasU P Q 1 = 1 := by simp [lucasU]
      rw [h0, h1]; push_cast; ring
  | succ N ih =>
      have hrec := lucasU_add_two P Q N
      calc x ^ (N + 2) = x ^ (N + 1) * x := by ring
        _ = (((lucasU P Q (N + 1) : ℤ) : R) * x - (Q : R) * ((lucasU P Q N : ℤ) : R)) * x := by
              rw [ih]
        _ = ((lucasU P Q (N + 1) : ℤ) : R) * x ^ 2
              - (Q : R) * ((lucasU P Q N : ℤ) : R) * x := by ring
        _ = ((lucasU P Q (N + 2) : ℤ) : R) * x - (Q : R) * ((lucasU P Q (N + 1) : ℤ) : R) := by
              rw [hx, hrec]; push_cast; ring

/-- `hD` forces `c ≠ 2`: every element of `ZMod 2` is a square. -/
theorem ne_two_of_not_isSquare {P Q : ℤ} {c : ℕ}
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) : c ≠ 2 := by
  rintro rfl
  exact hD (by revert hD; generalize ((P ^ 2 - 4 * Q : ℤ) : ZMod 2) = y; intro _; revert y; decide)

/-- `hD` forces `c ∤ Q`: otherwise `D ≡ P²`. -/
theorem not_dvd_of_not_isSquare {P Q : ℤ} {c : ℕ}
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) : ¬ (c : ℤ) ∣ Q := by
  intro hdvd
  have hQ0 : ((Q : ℤ) : ZMod c) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
  refine hD ⟨((P : ℤ) : ZMod c), ?_⟩
  push_cast
  rw [hQ0]
  ring

/-- `hD` forces `Q ≠ 0`. -/
theorem ne_zero_of_not_isSquare {P Q : ℤ} {c : ℕ}
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) : Q ≠ 0 := by
  rintro rfl
  exact hD ⟨((P : ℤ) : ZMod c), by push_cast; ring⟩

/-- `X² − PX + Q` has no root mod an inert prime. -/
theorem no_root_inert {P Q : ℤ} {c : ℕ} (hc : c.Prime)
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) (y : ZMod c) :
    y ^ 2 - ((P : ℤ) : ZMod c) * y + ((Q : ℤ) : ZMod c) ≠ 0 := by
  intro hy
  refine hD ⟨2 * y - ((P : ℤ) : ZMod c), ?_⟩
  push_cast
  linear_combination (-4 : ZMod c) * hy

/-- Frobenius at an inert prime: `A^(c+1) ≡ Q·I (mod c)`, entrywise. -/
theorem lucasU_frobenius_inert {P Q : ℤ} {c : ℕ} (hc : c.Prime)
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) :
    (c : ℤ) ∣ lucasU P Q (c + 1) ∧ (c : ℤ) ∣ lucasU P Q c + 1 := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hQnd : ¬ (c : ℤ) ∣ Q := not_dvd_of_not_isSquare hD
  have hnr := no_root_inert hc hD
  set f : (ZMod c)[X] := X ^ 2 - C ((P : ℤ) : ZMod c) * X + C ((Q : ℤ) : ZMod c) with hf
  have hdeg : f.natDegree = 2 := by rw [hf]; compute_degree!
  have hirr : Irreducible f := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro y hy
    refine hnr y ?_
    have h : f.eval y = 0 := hy
    rw [hf] at h
    simpa using h
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  have hfne : f ≠ 0 := hirr.ne_zero
  set K := AdjoinRoot f with hK
  letI pb : PowerBasis (ZMod c) K := AdjoinRoot.powerBasis hfne
  haveI : Module.Finite (ZMod c) K := Module.Finite.of_basis pb.basis
  letI : Fintype K := Module.fintypeOfFintype pb.basis
  set x : K := AdjoinRoot.root f with hxdef
  have hPK : ((P : ℤ) : K) = algebraMap (ZMod c) K ((P : ℤ) : ZMod c) := (map_intCast _ P).symm
  have hQK : ((Q : ℤ) : K) = algebraMap (ZMod c) K ((Q : ℤ) : ZMod c) := (map_intCast _ Q).symm
  have hx2 : x ^ 2 = ((P : ℤ) : K) * x - ((Q : ℤ) : K) := by
    have h0 : (AdjoinRoot.mk f)
        (X ^ 2 - C ((P : ℤ) : ZMod c) * X + C ((Q : ℤ) : ZMod c) : (ZMod c)[X]) = 0 := by
      rw [← hf]; exact AdjoinRoot.mk_self
    simp only [map_add, map_sub, map_pow, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      ← hxdef, ← AdjoinRoot.algebraMap_eq] at h0
    rw [hPK, hQK]
    linear_combination h0
  -- linear independence of `1, x` over the prime field
  have hli : ∀ a b : ZMod c, (algebraMap (ZMod c) K a) * x + algebraMap (ZMod c) K b = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have hdvd : f ∣ (C a * X + C b : (ZMod c)[X]) := by
      rw [← AdjoinRoot.mk_eq_zero]
      simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← hxdef]
      exact hab
    by_cases ha : a = 0
    · subst ha
      simp only [map_zero, zero_mul, zero_add] at hab
      exact ⟨rfl, (map_eq_zero_iff _ (algebraMap (ZMod c) K).injective).1 hab⟩
    · exfalso
      have hne : (C a * X + C b : (ZMod c)[X]) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun r => Polynomial.coeff r 1) h0
        simp at h1
        exact ha h1
      have h2 := Polynomial.natDegree_le_of_dvd hdvd hne
      have hd1 : (C a * X + C b : (ZMod c)[X]).natDegree ≤ 1 := by compute_degree
      omega
  have hnox : ∀ a : ZMod c, algebraMap (ZMod c) K a ≠ x := by
    intro a ha
    have := hli 1 (-a) (by rw [map_one, one_mul, map_neg, ha]; ring)
    exact one_ne_zero this.1
  haveI : CharP K c := charP_of_injective_algebraMap (algebraMap (ZMod c) K).injective c
  haveI : ExpChar K c := ExpChar.prime hc
  have hpc : ((P : ℤ) : K) ^ c = ((P : ℤ) : K) := by rw [hPK, ← map_pow, ZMod.pow_card]
  have hqc : ((Q : ℤ) : K) ^ c = ((Q : ℤ) : K) := by rw [hQK, ← map_pow, ZMod.pow_card]
  have hy : (x ^ c) ^ 2 - ((P : ℤ) : K) * (x ^ c) + ((Q : ℤ) : K) = 0 := by
    have h1 : (x ^ 2 - ((P : ℤ) : K) * x + ((Q : ℤ) : K) : K) = 0 := by linear_combination hx2
    have h2 : ((x ^ 2 - ((P : ℤ) : K) * x + ((Q : ℤ) : K) : K)) ^ c = 0 := by
      rw [h1, zero_pow hc.pos.ne']
    rw [add_pow_char, sub_pow_char, mul_pow, hpc, hqc] at h2
    have h3 : (x ^ 2 : K) ^ c = (x ^ c) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h3] at h2
    exact h2
  have hfact : (x ^ c - x) * (x ^ c - (((P : ℤ) : K) - x)) = 0 := by linear_combination hy - hx2
  have hconj : x ^ c = ((P : ℤ) : K) - x := by
    rcases mul_eq_zero.1 hfact with h | h
    · exfalso
      obtain ⟨a, ha⟩ := FibonacciPrimePow.exists_algebraMap_eq_of_pow_eq (p := c) x
        (by linear_combination h)
      exact hnox a ha
    · linear_combination h
  have hkey : x ^ (c + 1) = ((Q : ℤ) : K) := by
    have h : x ^ (c + 1) = x * x ^ c := by ring
    rw [h, hconj]
    linear_combination -hx2
  have hlu : x ^ (c + 1) = ((lucasU P Q (c + 1) : ℤ) : K) * x - ((Q : ℤ) : K) *
      ((lucasU P Q c : ℤ) : K) := by
    exact pow_eq_lucasU P Q (x := x) hx2 c
  have hzero : (algebraMap (ZMod c) K (((lucasU P Q (c + 1) : ℤ) : ZMod c))) * x
      + algebraMap (ZMod c) K (((-Q * lucasU P Q c - Q : ℤ) : ZMod c)) = 0 := by
    rw [map_intCast, map_intCast]
    push_cast
    linear_combination hkey - hlu
  obtain ⟨h1, h2⟩ := hli _ _ hzero
  have hd1 : (c : ℤ) ∣ lucasU P Q (c + 1) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ?_
    exact h1
  refine ⟨hd1, ?_⟩
  have hd2 : (c : ℤ) ∣ -Q * lucasU P Q c - Q := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
  have hd3 : (c : ℤ) ∣ Q * (lucasU P Q c + 1) := by
    have : Q * (lucasU P Q c + 1) = -(-Q * lucasU P Q c - Q) := by ring
    rw [this]
    exact dvd_neg.2 hd2
  have hcp : Prime (c : ℤ) := Nat.prime_iff_prime_int.mp hc
  rcases (hcp.dvd_mul).1 hd3 with h | h
  · exact absurd h hQnd
  · exact h

/-! ### Step 2: lifting the exponent -/

theorem intCast_eq_zsmul_one {R : Type*} [Ring R] (q : ℤ) : (q : R) = q • (1 : R) := by
  rw [zsmul_eq_mul, mul_one]

/-- Binomial expansion to second order around a central scalar, valid in any ring. -/
theorem intCast_add_pow_expand {R : Type*} [Ring R] (q : ℤ) (ε : R) (k : ℕ) :
    ∃ D : R, ((q : R) + ε) ^ (k + 1)
      = ((q ^ (k + 1) : ℤ) : R) + ((((k + 1 : ℕ) : ℤ) * q ^ k) • ε) + ε ^ 2 * D := by
  have key : ∃ D : Polynomial ℤ, (Polynomial.C q + Polynomial.X : Polynomial ℤ) ^ (k + 1)
      = Polynomial.C (q ^ (k + 1))
        + Polynomial.C (((k + 1 : ℕ) : ℤ) * q ^ k) * Polynomial.X + Polynomial.X ^ 2 * D := by
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
        obtain ⟨D, hD⟩ := ih
        refine ⟨Polynomial.C (((k + 1 : ℕ) : ℤ) * q ^ k) + Polynomial.C q * D
          + Polynomial.X * D, ?_⟩
        rw [pow_succ, hD]
        simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_eq_natCast]
        push_cast
        ring
  obtain ⟨D, hD⟩ := key
  refine ⟨Polynomial.aeval ε D, ?_⟩
  have h := congrArg (Polynomial.aeval ε) hD
  simp only [map_add, map_pow, map_mul, map_natCast, map_intCast,
    Polynomial.aeval_X, algebraMap_int_eq, eq_intCast] at h
  rw [h, zsmul_eq_mul]
  push_cast
  noncomm_ring

/-- The form of the expansion used along the tower: if `c ∣ a` then, modulo `c * a`, the `c`-th
power of `q + a·B` is the scalar `q^c`. -/
theorem scalar_add_pow_expand {R : Type*} [Ring R] (q a a' : ℤ) (B : R) {m : ℕ} (hm : 1 ≤ m)
    (ha : a = (m : ℤ) * a') :
    ∃ C : R, ((q : R) + a • B) ^ m = ((q ^ m : ℤ) : R) + ((m : ℤ) * a) • C := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨D, hD⟩ := intCast_add_pow_expand q (a • B) k
  refine ⟨q ^ k • B + a' • (B ^ 2 * D), ?_⟩
  rw [hD]
  have h2 : ((((k + 1 : ℕ) : ℤ) * q ^ k) • (a • B))
      = (((k + 1 : ℕ) : ℤ) * a) • (q ^ k • B) := by
    rw [smul_smul, smul_smul]; congr 1; ring
  have h3 : (a • B) ^ 2 * D = (((k + 1 : ℕ) : ℤ) * a) • (a' • (B ^ 2 * D)) := by
    rw [_root_.smul_pow, smul_mul_assoc, smul_smul]
    congr 1
    rw [sq, ha]; ring
  rw [h2, h3, smul_add, add_assoc]

/-- **The inductive form of the sign flip**: `A^(c^n (c+1)) ≡ Q^(c^n)·I (mod c^(n+1))`. -/
theorem lucasA_pow_frobenius {P Q : ℤ} {c : ℕ} (hc : c.Prime)
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) (n : ℕ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
      lucasA P Q ^ (c ^ n * (c + 1))
        = ((Q ^ (c ^ n) : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) + (c : ℤ) ^ (n + 1) • B := by
  induction n with
  | zero =>
      obtain ⟨hd1, hd2⟩ := lucasU_frobenius_inert hc hD
      obtain ⟨a, ha⟩ := hd1
      obtain ⟨b, hb⟩ := hd2
      refine ⟨!![P * a - Q * b, -Q * a; a, -Q * b], ?_⟩
      have hrec : lucasU P Q (c + 2) = P * lucasU P Q (c + 1) - Q * lucasU P Q c :=
        lucasU_add_two P Q c
      have hidx : c ^ 0 * (c + 1) = c + 1 := by ring
      have e00 : (lucasA P Q ^ (c + 1)) 0 0 = lucasU P Q (c + 2) :=
        lucasA_pow_apply_zero_zero P Q (c + 1)
      have e01 : (lucasA P Q ^ (c + 1)) 0 1 = -Q * lucasU P Q (c + 1) := by
        rw [lucasA_pow_succ_apply_one, lucasA_pow_apply_zero_zero]
      have e10 : (lucasA P Q ^ (c + 1)) 1 0 = lucasU P Q (c + 1) :=
        lucasA_pow_apply_one_zero P Q (c + 1)
      have e11 : (lucasA P Q ^ (c + 1)) 1 1 = -Q * lucasU P Q c := by
        rw [lucasA_pow_succ_apply_one, lucasA_pow_apply_one_zero]
      have hb' : lucasU P Q c = (c : ℤ) * b - 1 := by linarith
      rw [hidx, Matrix.eta_fin_two (lucasA P Q ^ (c + 1)), e00, e01, e10, e11, hrec, ha, hb',
        intCast_eq_zsmul_one, Matrix.one_fin_two, pow_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
  | succ n ih =>
      obtain ⟨B, hB⟩ := ih
      have ha : (c : ℤ) ^ (n + 1) = (c : ℤ) * (c : ℤ) ^ n := by ring
      obtain ⟨C, hC⟩ := scalar_add_pow_expand (Q ^ c ^ n) ((c : ℤ) ^ (n + 1)) ((c : ℤ) ^ n) B
        (m := c) hc.pos ha
      refine ⟨C, ?_⟩
      have hsplit : c ^ (n + 1) * (c + 1) = (c ^ n * (c + 1)) * c := by ring
      have hstep : lucasA P Q ^ (c ^ (n + 1) * (c + 1))
          = (((Q ^ c ^ n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) + (c : ℤ) ^ (n + 1) • B) ^ c := by
        rw [hsplit, pow_mul, hB]
      rw [hstep, hC]
      congr 1
      · rw [← pow_mul, ← pow_succ]
      · congr 1
        ring

/-- **The sign flip at an inert prime.** -/
theorem lucasU_prime_pow_succ_add {P Q : ℤ} {c : ℕ} (hc : c.Prime) (hQ : ¬ (c : ℤ) ∣ Q)
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ lucasU P Q (c ^ (n + 1)) + lucasU P Q (c ^ n) := by
  obtain ⟨B, hB⟩ := lucasA_pow_frobenius hc hD n
  set A : Matrix (Fin 2) (Fin 2) ℤ := lucasA P Q with hA
  set N : ℕ := c ^ n with hN
  set adj : Matrix (Fin 2) (Fin 2) ℤ := (A ^ N).adjugate with hadjdef
  have hdet : (A ^ N).det = Q ^ N := by rw [Matrix.det_pow, hA, lucasA_det]
  have hmuladj : A ^ N * adj = (Q ^ N) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hadjdef, Matrix.mul_adjugate, hdet]
  have hidx : c ^ (n + 1) + N = c ^ n * (c + 1) := by rw [hN]; ring
  have hE : (Q ^ N) • (A ^ c ^ (n + 1))
      = (Q ^ N) • adj + (c : ℤ) ^ (n + 1) • (B * adj) := by
    have h1 : A ^ c ^ (n + 1) * (A ^ N * adj) = A ^ (c ^ n * (c + 1)) * adj := by
      rw [← Matrix.mul_assoc, ← pow_add, hidx]
    rw [hmuladj, Matrix.mul_smul, Matrix.mul_one, hB, Matrix.add_mul,
      intCast_eq_zsmul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul] at h1
    exact h1
  have hadj10 : adj 1 0 = -((A ^ N) 1 0) := by
    rw [hadjdef, Matrix.adjugate_fin_two]
    simp
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hE
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, hadj10] at h10
  have hU1 : (A ^ c ^ (n + 1)) 1 0 = lucasU P Q (c ^ (n + 1)) := lucasA_pow_apply_one_zero P Q _
  have hU0 : (A ^ N) 1 0 = lucasU P Q (c ^ n) := lucasA_pow_apply_one_zero P Q _
  rw [hU1, hU0] at h10
  have hkey : (c : ℤ) ^ (n + 1) ∣ Q ^ N * (lucasU P Q (c ^ (n + 1)) + lucasU P Q (c ^ n)) := by
    refine ⟨(B * adj) 1 0, ?_⟩
    linarith [h10]
  have hcop1 : IsCoprime ((c : ℤ)) Q := by
    exact (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hc)).2 hQ
  have hcop : IsCoprime ((c : ℤ) ^ (n + 1)) (Q ^ N) := (hcop1.pow)
  exact hcop.dvd_of_dvd_mul_left hkey

/-! ### Step 3a: divisibility along the tower, and elementary obstructions -/

/-- `U(m) ∣ (A^m) 0 1` (which is `−Q U(m)` for `m ≥ 1`, and `0` for `m = 0`). -/
theorem lucasU_dvd_lucasA_pow_apply_zero_one (P Q : ℤ) (m : ℕ) :
    lucasU P Q m ∣ (lucasA P Q ^ m) 0 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Matrix.one_apply]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [lucasA_pow_succ_apply_one, lucasA_pow_apply_zero_zero]
  exact Dvd.dvd.mul_left dvd_rfl _

/-- Both off-diagonal entries of `A^(m k)` are divisible by `U(m)`. -/
theorem lucasU_dvd_offdiag (P Q : ℤ) (m k : ℕ) :
    lucasU P Q m ∣ (lucasA P Q ^ (m * k)) 1 0 ∧
      lucasU P Q m ∣ (lucasA P Q ^ (m * k)) 0 1 := by
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
      obtain ⟨ih1, ih0⟩ := ih
      have hsplit : m * (k + 1) = m * k + m := by ring
      have hmul : ∀ i j : Fin 2, (lucasA P Q ^ (m * (k + 1))) i j
          = (lucasA P Q ^ (m * k)) i 0 * (lucasA P Q ^ m) 0 j
            + (lucasA P Q ^ (m * k)) i 1 * (lucasA P Q ^ m) 1 j := by
        intro i j
        rw [hsplit, pow_add, Matrix.mul_apply, Fin.sum_univ_two]
      have h10 : lucasU P Q m ∣ (lucasA P Q ^ m) 1 0 := by
        rw [lucasA_pow_apply_one_zero]
      have h01 : lucasU P Q m ∣ (lucasA P Q ^ m) 0 1 :=
        lucasU_dvd_lucasA_pow_apply_zero_one P Q m
      refine ⟨?_, ?_⟩
      · rw [hmul 1 0]
        exact dvd_add (Dvd.dvd.mul_right ih1 _) (Dvd.dvd.mul_left h10 _)
      · rw [hmul 0 1]
        exact dvd_add (Dvd.dvd.mul_left h01 _) (Dvd.dvd.mul_right ih0 _)

/-- `U(m) ∣ U(mk)`. -/
theorem lucasU_dvd_mul (P Q : ℤ) (m k : ℕ) : lucasU P Q m ∣ lucasU P Q (m * k) := by
  have := (lucasU_dvd_offdiag P Q m k).1
  rwa [lucasA_pow_apply_one_zero] at this

/-- Divisibility along the `c`-power tower. -/
theorem lucasU_tower_dvd (P Q : ℤ) {c m n : ℕ} (hmn : m ≤ n) :
    lucasU P Q (c ^ m) ∣ lucasU P Q (c ^ n) := by
  have h : c ^ n = c ^ m * c ^ (n - m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h]
  exact lucasU_dvd_mul P Q _ _

theorem abs_sub_abs_le_abs_add' {a b : ℤ} : |a| - |b| ≤ |a + b| := by
  have h := abs_sub_abs_le_abs_sub a (-b)
  rw [abs_neg, sub_neg_eq_add] at h
  linarith

/-- A prime `c` dividing `x` with `c < |x|` obstructs primality of `x`. -/
theorem not_prime_of_dvd_of_lt_abs {c : ℕ} (hc : c.Prime) {x : ℤ} (hd : (c : ℤ) ∣ x)
    (hx : (c : ℤ) < |x|) : ¬ Prime x := by
  intro hpx
  have hn : x.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hpx
  have hd' : c ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd
    simpa using this
  have habs : |x| = (x.natAbs : ℤ) := Int.abs_eq_natAbs x
  rcases hn.eq_one_or_self_of_dvd c hd' with hh | hh
  · have := hc.two_le; omega
  · omega

/-- `U(c^n) ≡ (−1)^n (mod c)`: the sign flip read modulo `c` alone. -/
theorem lucasU_prime_pow_mod {P Q : ℤ} {c : ℕ} (hc : c.Prime) (hQ : ¬ (c : ℤ) ∣ Q)
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) (n : ℕ) :
    (c : ℤ) ∣ lucasU P Q (c ^ n) - (-1) ^ n := by
  induction n with
  | zero =>
      have h1 : lucasU P Q (c ^ 0) = 1 := by simp [lucasU, lucasA]
      rw [h1]; norm_num
  | succ n ih =>
      have hstep := lucasU_prime_pow_succ_add hc hQ hD n
      have hc1 : (c : ℤ) ∣ lucasU P Q (c ^ (n + 1)) + lucasU P Q (c ^ n) :=
        dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) hstep
      have hre : lucasU P Q (c ^ (n + 1)) - (-1) ^ (n + 1)
          = (lucasU P Q (c ^ (n + 1)) + lucasU P Q (c ^ n))
            - (lucasU P Q (c ^ n) - (-1) ^ n) := by ring
      rw [hre]
      exact dvd_sub hc1 ih

/-- **`U_(c^n)(P,Q) + h` is composite infinitely often**, for every odd prime `c ∤ Q` that is
inert in `ℚ(√(P² − 4Q))`, whenever `|U(c^n)| → ∞`, and every `h`. -/
theorem lucasU_prime_pow_add_not_prime {P Q : ℤ} {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hQ : ¬ (c : ℤ) ∣ Q) (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c))
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (c ^ n) + h) := by
  set U : ℕ → ℤ := fun n => lucasU P Q (c ^ n) with hUdef
  set t : ℕ → ℤ := fun n => U n + h with htdef
  have hcle : 2 ≤ c := hc.two_le
  have hc3 : 3 ≤ c := by
    rcases Nat.lt_or_ge c 3 with hlt | hge
    · interval_cases c <;> simp_all
    · exact hge
  have hQ0 : Q ≠ 0 := ne_zero_of_not_isSquare hD
  have hgr : ∀ B : ℤ, ∃ N : ℕ, ∀ n ≥ N, B ≤ |U n| := by
    intro B
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hgrow B)
    exact ⟨N, hN⟩
  have hlow : ∀ n : ℕ, |U n| - |h| ≤ |t n| := fun n => abs_sub_abs_le_abs_add'
  rcases eq_or_ne h 0 with rfl | h0
  · -- `h = 0`: `U(c^m) ∣ U(c^n)` with `1 < |U(c^m)| < |U(c^n)|`
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨M, hM⟩ := hgr 2
    obtain ⟨N₂, hN₂⟩ := hgr (|U M| + 1)
    refine ⟨max (max N₂ (M + 1)) a, le_max_right _ _, ?_⟩
    set n : ℕ := max (max N₂ (M + 1)) a with hn
    have hMn : M ≤ n := by omega
    have h1 : 2 ≤ |U M| := hM M le_rfl
    have h2 : |U M| + 1 ≤ |U n| := hN₂ n (by omega)
    have hdvd : U M ∣ U n := lucasU_tower_dvd P Q hMn
    show ¬ Prime (U n + 0)
    rw [add_zero]
    intro hpr
    have hnp : (U n).natAbs.Prime := Int.prime_iff_natAbs_prime.1 hpr
    have hdn : (U M).natAbs ∣ (U n).natAbs := Int.natAbs_dvd_natAbs.2 hdvd
    have e1 : |U M| = ((U M).natAbs : ℤ) := Int.abs_eq_natAbs _
    have e2 : |U n| = ((U n).natAbs : ℤ) := Int.abs_eq_natAbs _
    rcases hnp.eq_one_or_self_of_dvd _ hdn with hh | hh <;> omega
  rcases eq_or_ne h 1 with rfl | h1
  · -- `h = 1`: for odd `n`, `c ∣ U(c^n) + 1`
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨N, hN⟩ := hgr ((c : ℤ) + 2)
    refine ⟨2 * (a + N) + 1, by omega, ?_⟩
    set n : ℕ := 2 * (a + N) + 1 with hn
    have hodd : Odd n := ⟨a + N, by omega⟩
    have h1 := hN n (by omega)
    have h2 := hlow n
    have habs1 : |(1 : ℤ)| = 1 := by norm_num
    rw [habs1] at h2
    show ¬ Prime (t n)
    refine not_prime_of_dvd_of_lt_abs hc ?_ (by omega)
    have hmod := lucasU_prime_pow_mod hc hQ hD n
    rw [hodd.neg_one_pow] at hmod
    show (c : ℤ) ∣ U n + 1
    simpa using hmod
  rcases eq_or_ne h (-1) with rfl | hm1
  · -- `h = -1`: for even `n`, `c ∣ U(c^n) − 1`
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨N, hN⟩ := hgr ((c : ℤ) + 2)
    refine ⟨2 * (a + N + 1), by omega, ?_⟩
    set n : ℕ := 2 * (a + N + 1) with hn
    have heven : Even n := ⟨a + N + 1, by omega⟩
    have h1 := hN n (by omega)
    have h2 := hlow n
    have habs1 : |(-1 : ℤ)| = 1 := by norm_num
    rw [habs1] at h2
    show ¬ Prime (t n)
    refine not_prime_of_dvd_of_lt_abs hc ?_ (by omega)
    have hmod := lucasU_prime_pow_mod hc hQ hD n
    rw [heven.neg_one_pow] at hmod
    show (c : ℤ) ∣ U n + -1
    have : U n + -1 = U n - 1 := by ring
    rw [this]
    exact hmod
  -- `|h| ≥ 2`: the filter argument
  have hH2 : 2 ≤ h.natAbs := by omega
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  set H : ℕ := h.natAbs with hH
  have hHabs : |h| = (H : ℤ) := Int.abs_eq_natAbs h
  obtain ⟨N₁, hN₁⟩ := hgr (|h| + |Q| + (c : ℤ) + 3)
  set N : ℕ := max n₀ N₁ with hNdef
  have hprime : ∀ n ≥ N, Prime (t n) := fun n hn => hn₀ n (by omega)
  have hbig : ∀ n ≥ N, |Q| + (c : ℤ) + 3 ≤ |t n| := by
    intro n hn
    have := hN₁ n (by omega)
    have := hlow n
    linarith
  have hpabs : ∀ n : ℕ, ((t n).natAbs : ℤ) = |t n| := fun n => (Int.abs_eq_natAbs _).symm
  have hpn : ∀ n ≥ N, (t n).natAbs.Prime := fun n hn =>
    Int.prime_iff_natAbs_prime.1 (hprime n hn)
  have hpnec : ∀ n ≥ N, (t n).natAbs ≠ c := by
    intro n hn hEq
    have h1 := hbig n hn
    have h2 := hpabs n
    rw [hEq] at h2
    have habsQ : (0 : ℤ) ≤ |Q| := abs_nonneg _
    omega
  have hpdvdQ : ∀ n ≥ N, ¬ ((t n).natAbs : ℤ) ∣ (lucasA P Q).det := by
    intro n hn hd
    rw [lucasA_det] at hd
    have h1 : ((t n).natAbs : ℤ) ≤ |Q| := Int.le_of_dvd (abs_pos.2 hQ0) ((dvd_abs _ _).2 hd)
    have h2 := hbig n hn
    rw [hpabs n] at h1
    have : (0 : ℤ) ≤ (c : ℤ) := by positivity
    omega
  -- the return step
  have hstep : ∀ n ≥ N, padicValNat c (glCard 2 (t n).natAbs) ≤ n →
      ∃ j, 1 ≤ j ∧ (t (n + j)).natAbs = (t n).natAbs := by
    intro n hn hv
    obtain ⟨j, hj1, hj⟩ := LeanFormalizations.Mills.SaitoFibonacci.exists_entry_pow_congr
      (lucasA P Q) (hpn n hn) hc (hpdvdQ n hn) hv
    have hent := hj 1 0
    rw [lucasA_pow_apply_one_zero, lucasA_pow_apply_one_zero] at hent
    have hdvd : ((t n).natAbs : ℤ) ∣ t (n + j) := by
      have hA : ((t n).natAbs : ℤ) ∣ t n := Int.natAbs_dvd.2 dvd_rfl
      have hre : t (n + j) = (U (n + j) - U n) + t n := by
        show U (n + j) + h = (U (n + j) - U n) + (U n + h)
        ring
      rw [hre]
      exact dvd_add hent hA
    have hq := hpn (n + j) (by omega)
    have hdq : (t n).natAbs ∣ (t (n + j)).natAbs :=
      Int.natAbs_dvd_natAbs.2 (Int.natAbs_dvd.1 hdvd)
    rcases hq.eq_one_or_self_of_dvd _ hdq with hh | hh
    · exact absurd hh (hpn n hn).ne_one
    · exact ⟨j, hj1, hh.symm⟩
  -- the `c`-part of `|GL₂(𝔽_p)|` exceeds `n`
  have hstep2 : ∀ n ≥ N, n < padicValNat c (glCard 2 (t n).natAbs) := by
    intro n hn
    by_contra hle
    push_neg at hle
    have chain : ∀ k : ℕ, ∃ n' : ℕ, n + k ≤ n' ∧ (t n').natAbs = (t n).natAbs ∧
        padicValNat c (glCard 2 (t n').natAbs) ≤ n' := by
      intro k
      induction k with
      | zero => exact ⟨n, by omega, rfl, hle⟩
      | succ k ih =>
          obtain ⟨n', hn'1, hn'2, hn'3⟩ := ih
          obtain ⟨j, hj1, hj⟩ := hstep n' (by omega) hn'3
          refine ⟨n' + j, by omega, ?_, ?_⟩
          · rw [hj]; exact hn'2
          · rw [hj]; omega
    obtain ⟨Nb, hNb⟩ := hgr (|t n| + |h| + 1)
    obtain ⟨n', hc1, hc2', _⟩ := chain (Nb + n)
    have h1 : |t n'| = |t n| := by rw [← hpabs n', ← hpabs n, hc2']
    have h2 := hNb n' (by omega)
    have h3 := hlow n'
    linarith
  -- `t n ≡ ±1` modulo `c ^ (n / 2)`
  have hstep3 : ∀ n ≥ N, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (c : ℤ) ^ (n / 2) ∣ t n - s := by
    intro n hn
    have hlt := hstep2 n hn
    obtain ⟨s0, hs0, hd⟩ : ∃ s0 : ℤ, (s0 = 1 ∨ s0 = -1) ∧
        (c : ℤ) ^ (n / 2) ∣ ((t n).natAbs : ℤ) - s0 := by
      rcases FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat hc hc2 (hpn n hn)
        (hpnec n hn) hlt with hd | hd
      · exact ⟨1, Or.inl rfl, hd⟩
      · exact ⟨-1, Or.inr rfl, by simpa using hd⟩
    rcases Int.natAbs_eq (t n) with he | he
    · exact ⟨s0, hs0, by rw [he]; exact hd⟩
    · refine ⟨-s0, ?_, ?_⟩
      · rcases hs0 with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by norm_num)
      · have hrw : t n - -s0 = -(((t n).natAbs : ℤ) - s0) := by omega
        rw [hrw]
        exact dvd_neg.2 hd
  -- contradict `|h| ≥ 2`
  set n : ℕ := 2 * (2 * H + 3) + N with hn
  set e : ℕ := n / 2 with he
  have hnN : N ≤ n := by omega
  have hebnd : 2 * H + 3 ≤ e := by omega
  have hbnd : (2 * H + 2 : ℤ) < (c : ℤ) ^ e := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ e ≤ c ^ e := Nat.pow_le_pow_left hcle e
    have h3 : 2 * H + 2 < c ^ e := by omega
    exact_mod_cast h3
  obtain ⟨s, hs, hsd⟩ := hstep3 n hnN
  obtain ⟨s', hs', hsd'⟩ := hstep3 (n + 1) (by omega)
  have hdvd' : (c : ℤ) ^ e ∣ t (n + 1) - s' := by
    refine dvd_trans (pow_dvd_pow _ ?_) hsd'
    omega
  have hflip : (c : ℤ) ^ e ∣ U (n + 1) + U n := by
    refine dvd_trans (pow_dvd_pow _ ?_) (lucasU_prime_pow_succ_add hc hQ hD n)
    omega
  have hsum : (c : ℤ) ^ e ∣ s + s' - 2 * h := by
    have hid : (s + s' - 2 * h) = (U (n + 1) + U n) - ((t n - s) + (t (n + 1) - s')) := by
      show _ = (U (n + 1) + U n) - ((U n + h - s) + (U (n + 1) + h - s'))
      ring
    rw [hid]
    exact dvd_sub hflip (dvd_add hsd hdvd')
  have hzero : s + s' - 2 * h = 0 := by
    by_contra hne
    have hle := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hsum)
    have hb : |s + s' - 2 * h| ≤ 2 * (H : ℤ) + 2 := by
      rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> rw [abs_le] <;> omega
    omega
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> omega

end LeanFormalizations.Mills.LucasInert

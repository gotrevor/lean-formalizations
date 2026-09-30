/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TeichmullerCongruence

/-!
# Phase 48: traces in the unipotent class mod 3 (sub-node R4 of `ShiftedTraceRigidity`)

`PROOF-THEOREM-E.md` Step 5: in the class `χ ≡ (X − z)³ (mod 3)` every trace of a nonzero power is
divisible by 3.  That is what kills `tr(ξ^s) = ±1`.  Matrix form, so negative shifts are covered through
the adjugate.

## Route
1. `three_dvd_trace_pow`: if `(M − w·1)^3 ≡ 0 (mod 3)` entrywise, then `N := M − w·1` is nilpotent over
   `ZMod 3`, so `tr (N^i) = 0` there for `i ≥ 1` (a nilpotent matrix over a field has nilpotent powers, and
   the trace of a nilpotent matrix is 0; look for `Matrix.isNilpotent_trace_of_isNilpotent` /
   `IsNilpotent.trace` or prove it via `charpoly`).  Expand `(w + N)^s` binomially (`w·1` commutes):
   `tr M^s ≡ 3 w^s ≡ 0 (mod 3)` (`d = 3`: `tr 1 = 3`).
2. `adjugate_unipotent`: if `(M − w·1)^3 ≡ 0 (mod 3)` and `3 ∤ w`, then
   `(adjugate M − w²·1)^3 ≡ 0 (mod 3)`.  Over `ZMod 3`: `M = w(1 + N′)` with `N′` nilpotent,
   `adjugate M = det M · M⁻¹`, `det M = w³ = w` in `ZMod 3` (unipotent determinant 1), and
   `M⁻¹ = w⁻¹ (1 − N′ + N′²)`.  So `adjugate M = w² (1 + nilpotent)`, and `w² = 1`.
3. `three_dvd_trace_adjugate_pow`: combine 1 and 2.

Frozen: the statements below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.UnipotentTrace

open Matrix

/-- Entrywise reduction of a `3×3` integer matrix mod `3`. -/
def red (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  (Int.castRingHom (ZMod 3)).mapMatrix A

theorem red_eq_zero_iff (A : Matrix (Fin 3) (Fin 3) ℤ) :
    red A = 0 ↔ ∀ i j, (3 : ℤ) ∣ A i j := by
  constructor
  · intro h i j
    rw [← Matrix.ext_iff] at h
    have := h i j
    simp only [red, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      eq_intCast, Int.cast_id] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 this
  · intro h
    ext i j
    simp only [red, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      eq_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (h i j)

theorem red_smul_one (w : ℤ) :
    red (w • (1 : Matrix (Fin 3) (Fin 3) ℤ))
      = (w : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
  ext i j
  simp only [red, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_one_eq_diagonal,
    Matrix.diagonal_apply, eq_intCast]
  split <;> simp

theorem red_sub (A B : Matrix (Fin 3) (Fin 3) ℤ) : red (A - B) = red A - red B := by
  ext i j; simp [red, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem red_pow (A : Matrix (Fin 3) (Fin 3) ℤ) (n : ℕ) : red (A ^ n) = (red A) ^ n :=
  map_pow (Int.castRingHom (ZMod 3)).mapMatrix A n

theorem red_trace (A : Matrix (Fin 3) (Fin 3) ℤ) : (red A).trace = (A.trace : ZMod 3) := by
  simp [red, RingHom.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.map_apply]

theorem red_adjugate (A : Matrix (Fin 3) (Fin 3) ℤ) : red A.adjugate = (red A).adjugate :=
  (Int.castRingHom (ZMod 3)).map_adjugate A

/-- The scalar matrix `w • 1` is central. -/
theorem commute_smul_one {R : Type*} [CommRing R] (w : R) (X : Matrix (Fin 3) (Fin 3) R) :
    Commute (w • (1 : Matrix (Fin 3) (Fin 3) R)) X := by
  show (w • (1 : Matrix (Fin 3) (Fin 3) R)) * X = X * (w • (1 : Matrix (Fin 3) (Fin 3) R))
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, Matrix.mul_one]

/-- Over `ZMod 3` the trace of every power of a nilpotent `3×3` matrix vanishes — the zeroth power
included, since `tr 1 = 3 = 0`. -/
theorem trace_pow_nilpotent (N : Matrix (Fin 3) (Fin 3) (ZMod 3)) (hN : N ^ 3 = 0) (m : ℕ) :
    (N ^ m).trace = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [pow_zero, Matrix.trace_one]
    decide
  · have hnil : IsNilpotent (N ^ m) := by
      refine ⟨3, ?_⟩
      rw [← pow_mul, mul_comm, pow_mul, hN, zero_pow (by omega)]
    exact isNilpotent_iff_eq_zero.1 (Matrix.isNilpotent_trace_of_isNilpotent hnil)

/-- Core computation over `ZMod 3`: powers of `v • 1 + N` with `N ^ 3 = 0` are traceless. -/
theorem trace_pow_eq_zero (v : ZMod 3) (N : Matrix (Fin 3) (Fin 3) (ZMod 3)) (hN : N ^ 3 = 0)
    (s : ℕ) : ((v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N) ^ s).trace = 0 := by
  have hcom : Commute (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) N := commute_smul_one _ _
  rw [hcom.add_pow, Matrix.trace_sum]
  refine Finset.sum_eq_zero ?_
  intro m _
  have hx : (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) ^ m
      = (v ^ m) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [smul_pow, one_pow]
  have hcast : ((s.choose m : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 3))
      = ((s.choose m : ℕ) : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [Matrix.smul_one_eq_diagonal]
    exact (Matrix.diagonal_natCast _).symm
  rw [hx, hcast, Matrix.smul_mul, one_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_smul, trace_pow_nilpotent N hN]
  simp

/-- Every nonzero residue of `ZMod 3` squares to `1`. -/
theorem sq_eq_one_of_ne_zero {v : ZMod 3} (hv : v ≠ 0) : v ^ 2 = 1 := by
  revert hv; revert v; decide

theorem cube_eq_self (x : ZMod 3) : x ^ 3 = x := by revert x; decide

/-- Over `ZMod 3`, a unipotent-times-scalar matrix has determinant `v ^ 3`. -/
theorem det_eq_of_unipotent (v : ZMod 3) (N : Matrix (Fin 3) (Fin 3) (ZMod 3)) (hN : N ^ 3 = 0) :
    (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N).det = v ^ 3 := by
  have hcom : Commute (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) N := commute_smul_one _ _
  have hcube : (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N) ^ 3
      = (v ^ 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [add_pow_char_of_commute (p := 3) hcom, hN, add_zero, smul_pow, one_pow]
  have hdet : ((v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N).det) ^ 3 = (v ^ 3) ^ 3 := by
    have := congrArg Matrix.det hcube
    rwa [Matrix.det_pow, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  calc (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N).det
      = ((v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N).det) ^ 3 := (cube_eq_self _).symm
    _ = (v ^ 3) ^ 3 := hdet
    _ = v ^ 3 := cube_eq_self _

/-- The explicit inverse of `v • 1 + N` over `ZMod 3` when `v ≠ 0` and `N ^ 3 = 0`. -/
theorem mul_inv_aux (v : ZMod 3) (N : Matrix (Fin 3) (Fin 3) (ZMod 3)) (hv : v ≠ 0)
    (hN : N ^ 3 = 0) :
    (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N) *
      (v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) - N + v • N ^ 2) = 1 := by
  have hv2 : v * v = 1 := by rw [← pow_two]; exact sq_eq_one_of_ne_zero hv
  have hN3 : N * N * N = 0 := by rw [← pow_two, ← pow_succ]; exact hN
  simp only [add_mul, mul_add, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul,
    Matrix.mul_one, smul_smul, pow_two, hv2, one_smul]
  rw [← Matrix.mul_assoc, hN3, smul_zero]
  abel

/-- Step 2 of the route, over `ZMod 3`. -/
theorem adjugate_sub_sq_cube_eq_zero (v : ZMod 3) (N : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hv : v ≠ 0) (hN : N ^ 3 = 0) :
    ((v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N).adjugate
      - (v ^ 2) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) ^ 3 = 0 := by
  set A := v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) + N with hAdef
  set B := v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) - N + v • N ^ 2 with hBdef
  have hAB : A * B = 1 := mul_inv_aux v N hv hN
  have hdet : A.det = v ^ 3 := det_eq_of_unipotent v N hN
  have hadj : A.adjugate = v • B := by
    calc A.adjugate = A.adjugate * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = (A.adjugate * A) * B := by rw [Matrix.mul_assoc]
      _ = (A.det • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) * B := by rw [Matrix.adjugate_mul]
      _ = v • B := by rw [hdet, cube_eq_self, Matrix.smul_mul, one_mul]
  have hv2 : v * v = 1 := by rw [← pow_two]; exact sq_eq_one_of_ne_zero hv
  have hkey : A.adjugate - (v ^ 2) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))
      = N * (N - v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) := by
    rw [hadj, hBdef, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← pow_two, pow_two v]
    simp only [smul_sub, smul_add, smul_smul, hv2, one_smul]
    abel
  rw [hkey]
  have hc : Commute N (N - v • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) :=
    (Commute.refl N).sub_right (commute_smul_one v N).symm
  rw [hc.mul_pow, hN, Matrix.zero_mul]

theorem three_dvd_trace_pow (M : Matrix (Fin 3) (Fin 3) ℤ) (w : ℤ)
    (h : ∀ i j, (3 : ℤ) ∣ ((M - w • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j) (s : ℕ) (hs : 1 ≤ s) :
    (3 : ℤ) ∣ (M ^ s).trace := by
  have hred : (red M - (w : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) ^ 3 = 0 := by
    rw [← red_smul_one, ← red_sub, ← red_pow]
    exact (red_eq_zero_iff _).2 h
  have hsplit : red M = (w : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))
      + (red M - (w : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) := by abel
  have := trace_pow_eq_zero (w : ZMod 3) _ hred s
  rw [← hsplit, ← red_pow, red_trace] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 this

theorem adjugate_unipotent (M : Matrix (Fin 3) (Fin 3) ℤ) (w : ℤ) (hw : ¬ (3 : ℤ) ∣ w)
    (h : ∀ i j, (3 : ℤ) ∣ ((M - w • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j) :
    ∀ i j, (3 : ℤ) ∣ ((M.adjugate - (w ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j := by
  have hw' : (w : ZMod 3) ≠ 0 := fun hc => hw ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hc)
  have hred : (red M - (w : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) ^ 3 = 0 := by
    rw [← red_smul_one, ← red_sub, ← red_pow]
    exact (red_eq_zero_iff _).2 h
  have hsplit : red M = (w : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))
      + (red M - (w : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))) := by abel
  have hcube := adjugate_sub_sq_cube_eq_zero (w : ZMod 3) _ hw' hred
  rw [← hsplit] at hcube
  refine (red_eq_zero_iff _).1 ?_
  rw [red_pow, red_sub, red_adjugate, red_smul_one]
  have hc2 : (((w ^ 2 : ℤ) : ZMod 3)) = ((w : ZMod 3)) ^ 2 := by push_cast; ring
  rw [hc2]
  exact hcube

theorem three_dvd_trace_adjugate_pow (M : Matrix (Fin 3) (Fin 3) ℤ) (w : ℤ) (hw : ¬ (3 : ℤ) ∣ w)
    (h : ∀ i j, (3 : ℤ) ∣ ((M - w • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ^ 3) i j) (s : ℕ) (hs : 1 ≤ s) :
    (3 : ℤ) ∣ (M.adjugate ^ s).trace :=
  three_dvd_trace_pow M.adjugate (w ^ 2) (adjugate_unipotent M w hw h) s hs

end LeanFormalizations.Mills.UnipotentTrace

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftRigidityDeg

/-!
# Phase 65 lap 2: the unipotent class is invisible to the 3-adic mechanism in degree `≥ 4`

The cubic proof `ShiftRigidity.not_primeTraces` reads everything off `3`-adic limits: the window
(`p_n ≡ ±1 mod 3^(n/3)`), the Teichmüller limit `u_k` of `α_k^(3^n)`, and the spectral identity
`Σ u_k α_k^s = ω`, `ω² = 1`.  Its cube class `f ≡ (X − z)³ (mod 3)` closes because the trace is
`≡ 3 z^m ≡ 0 (mod 3)`.  In degree `4` the same class has trace `≡ 4 z^m ≡ z^m`, and the argument
loses its grip: if `f ≡ (X − 1)⁴ (mod 3)` then `C^(3^n) → 1` `3`-adically, so
`tr C^(3^n + s) ≡ tr C^s (mod 3^(n−1))`, and when `tr C^s = ±1` every `3`-adic constraint the
cubic proof uses is satisfied (constant spectral vector `u ≡ 1`, `ω = tr β^s`).

This file proves that for an explicit quartic Pisot polynomial (`f₀ = X⁴ − 4X³ − X + 1`,
`β ≈ 4.04599`, other roots of modulus `≈ 0.691, 0.691, 0.517`, `s = −1`, `tr β^(−1) = 1`):
`unipotent_trace_congr`.  So `ShiftRigidityDeg.shiftTraceRigidity_ge_four` cannot be proved by the
cubic `3`-adic/spectral route alone; on this class it needs a non-`3`-adic input.

Sibling note.  For every instance found (`scripts`-free search over `|coeff| ≤ 9`, 47 pairs
`(f, s)` with `f ≡ (X ∓ 1)⁴ (mod 3)`, `tr β^s = ±1`, `s ∈ [−6, 6]`, all with `s < 0`), small primes
`q ≤ 60` divide `tr C^(3^n + s)` along a residue class of `n` (e.g. `q = 2, 11, 13` for `f₀`), so
each instance is individually not all-prime; no uniform mechanism is known.  The uniform statement
is of the "infinitely many composite Fermat numbers" type unless a covering prime always exists,
which is the named node `UnipotentCovering`.
-/

namespace LeanFormalizations.Mills.ShiftRigidityUnipotent

open Polynomial LeanFormalizations.Mills.TheoremDGeneral LeanFormalizations.Mills.ShiftRigidity
  LeanFormalizations.Mills.ShiftRigidityDeg

/-- `X⁴ − 4X³ − X + 1`, `≡ (X − 1)⁴ (mod 3)`. -/
noncomputable def f₀ : ℤ[X] := X ^ 4 - 4 * X ^ 3 - X + 1

/-- Its companion matrix in the `compM` convention. -/
def C₀ : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, -1; 1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 4]

/-- `C₀⁻¹`, with trace `1 = tr β^(−1)`. -/
def D₀ : Matrix (Fin 4) (Fin 4) ℤ := !![1, 1, 0, 0; 0, 0, 1, 0; 4, 0, 0, 1; -1, 0, 0, 0]

def A₀ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-355, -1435, -5806, -23491; 267, 1080, 4371, 17685; 66, 267, 1080, 4371;
    1435, 5806, 23491, 95044]

theorem C₀_mul_D₀ : C₀ * D₀ = 1 := by decide

theorem trace_D₀ : D₀.trace = 1 := by decide

/-- `C₀⁹ ≡ 1 (mod 3)`: the unipotent class. -/
theorem C₀_pow_nine : C₀ ^ 9 = 1 + 3 • A₀ := by decide

/-- Lifting the exponent: `M⁹ = 1 + 3A` gives `M^(9·3^k) ≡ 1 (mod 3^(k+1))`. -/
theorem pow_three_pow_lift {d : ℕ} {M A : Matrix (Fin d) (Fin d) ℤ} (h : M ^ 9 = 1 + 3 • A) :
    ∀ k : ℕ, ∃ B : Matrix (Fin d) (Fin d) ℤ, M ^ (9 * 3 ^ k) = 1 + (3 : ℤ) ^ (k + 1) • B := by
  intro k
  induction k with
  | zero => exact ⟨A, by simpa using h⟩
  | succ k ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B + (3 : ℤ) ^ (k + 1) • B ^ 2 + (3 : ℤ) ^ (2 * k + 1) • B ^ 3, ?_⟩
    rw [show 9 * 3 ^ (k + 1) = 9 * 3 ^ k * 3 by ring, pow_mul, hB]
    have key : ∀ x : Matrix (Fin d) (Fin d) ℤ, (1 + x) ^ 3 = 1 + 3 • x + 3 • x ^ 2 + x ^ 3 := by
      intro x; noncomm_ring
    rw [key]
    rw [_root_.smul_pow, _root_.smul_pow]
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ]
    simp only [smul_add, smul_smul]
    push_cast
    ring_nf
    abel

theorem f₀_natDegree : f₀.natDegree = 4 := by
  unfold f₀; compute_degree!

theorem compM_f₀ : Matrix.reindex (finCongr f₀_natDegree) (finCongr f₀_natDegree)
    (compM ℤ f₀) = C₀ := by
  ext i j
  have hc : ∀ n : ℕ, f₀.coeff n = if n = 0 then 1 else if n = 1 then -1 else if n = 3 then -4
      else if n = 4 then 1 else 0 := by
    intro n; unfold f₀
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul_X_pow,
      show (4 : ℤ[X]) * X ^ 3 = C 4 * X ^ 3 by simp]
    rcases n with _ | _ | _ | _ | _ | n <;> simp
  fin_cases i <;> fin_cases j <;> simp [compM, hc, f₀_natDegree, C₀]

theorem traceSeq_f₀ (N : ℕ) : traceSeq f₀ N = (C₀ ^ N).trace := by
  have htr : ∀ M : Matrix (Fin f₀.natDegree) (Fin f₀.natDegree) ℤ,
      (Matrix.reindex (finCongr f₀_natDegree) (finCongr f₀_natDegree) M).trace = M.trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp (finCongr f₀_natDegree).symm (fun i => M i i)
  rw [traceSeq, ← compM_f₀, ← Matrix.coe_reindexAlgEquiv ℤ ℤ, ← map_pow,
    Matrix.coe_reindexAlgEquiv, htr]

/-- **The obstruction (kernel-checked).**  For `f₀` and `s = −1`, the shifted trace is
`≡ tr β^(−1) = 1 (mod 3^(n−1))` for every `n ≥ 2`.  So the window `p² ≡ 1` and the Teichmüller
data (`u ≡ 1`, `ω = 1`) are consistent with every `tr C^(3^n − 1)` prime: the cubic `3`-adic
mechanism has nothing to contradict.  (Numerically `v₃(tr C^(3^n−1) − 1) = n` for `n ≤ 8`.) -/
theorem unipotent_trace_congr (n : ℕ) (hn : 2 ≤ n) :
    (3 : ℤ) ^ (n - 1) ∣ traceSeq f₀ (((3 : ℤ) ^ n + (-1)).toNat) - 1 := by
  obtain ⟨B, hB⟩ := pow_three_pow_lift C₀_pow_nine (n - 2)
  have h3 : 9 * 3 ^ (n - 2) = 3 ^ n := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hpos : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hE : (((3 : ℤ) ^ n + (-1)).toNat) = 3 ^ n - 1 := by
    have : ((3 : ℤ) ^ n + (-1)) = ((3 ^ n - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hpos]; ring
    rw [this, Int.toNat_natCast]
  rw [hE, traceSeq_f₀]
  have hsplit : C₀ ^ (3 ^ n - 1) = C₀ ^ (3 ^ n) * D₀ := by
    conv_rhs => rw [show 3 ^ n = 3 ^ n - 1 + 1 by omega, pow_succ, mul_assoc, C₀_mul_D₀, mul_one]
  rw [hsplit, ← h3, hB, add_mul, one_mul, Matrix.trace_add, trace_D₀, smul_mul_assoc,
    Matrix.trace_smul, add_sub_cancel_left, show n - 2 + 1 = n - 1 by omega, smul_eq_mul]
  exact dvd_mul_right _ _

/-- **Believed (~99%, numerics)**: `f₀` is Pisot (real root `≈ 4.045989`, other roots of modulus
`≈ 0.6911, 0.6911, 0.5175`). -/
theorem pisot_f₀ : ∃ α : ℝ, PisotDataAny f₀ α := by
  sorry

/-- **Open node (covering primes in the unipotent class).**  For a Pisot `f` of degree `≥ 4`
with `f ≡ (X − ε)^ℓ (mod 3)` and `s ≠ 0`, some prime `q` divides `tr C^(3^n + s)` for infinitely
many `n`.  This would close the class `unipotent_trace_congr` shows the `3`-adic route cannot see.
Evidence: all 47 small instances have such `q ≤ 60`.  Mechanism: none known; the analogue for
Fermat numbers is open, so a proof must use more than the shape of the exponent. -/
def UnipotentCovering : Prop :=
  ∀ (f : ℤ[X]) (α : ℝ), PisotDataAny f α → 4 ≤ f.natDegree → ∀ ε : ZMod 3,
    f.map (Int.castRingHom (ZMod 3)) = (X - Polynomial.C ε) ^ f.natDegree → ∀ s : ℤ, s ≠ 0 →
    ∃ q : ℕ, q.Prime ∧ ∀ N : ℕ, ∃ n ≥ N, (q : ℤ) ∣ traceSeq f ((3 : ℤ) ^ n + s).toNat

end LeanFormalizations.Mills.ShiftRigidityUnipotent

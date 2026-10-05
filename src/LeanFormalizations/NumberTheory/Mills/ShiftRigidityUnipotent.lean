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

open Filter Polynomial LeanFormalizations.Mills.TheoremDGeneral LeanFormalizations.Mills.ShiftRigidity
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

/-! ## A non-unipotent class the `3`-adic route cannot see either (phase 65 lap 3)

`f₁ = X⁴ − 8X³ − 5X² + 6X + 3 ≡ X²(X − 1)² (mod 3)` is a totally real quartic Pisot polynomial
(`β ≈ 8.50029`, other roots `≈ 0.8555, −0.8947, −0.4611`) whose reciprocal roots split into two pairs
with sum `−1` each (the reversed polynomial is `(Y² + Y + c)(Y² + Y + c')`, `c, c' = −4 ± √15`).  The
Teichmüller vector is `u = (1, 1, 0, 0)` (roots `≡ 1` and `≡ 0` above `3`), and `Σ u_k α_k^(−1) = −1`:
so `tr C^(3^n − 1) → −1` `3`-adically (`v₃(tr + 1) = n + 1` for `2 ≤ n ≤ 9`).  It is outside the classes
`(X − z)^ℓ`, so `exists_spectral_any` applies and its conclusion is satisfied: the generic leaf
`ShiftRigidityDeg.shiftTraceRigidity_ge_four_generic` also needs a non-`3`-adic input. -/

/-- `X⁴ − 8X³ − 5X² + 6X + 3`. -/
noncomputable def f₁ : ℤ[X] := X ^ 4 - 8 * X ^ 3 - 5 * X ^ 2 + 6 * X + 3

def C₁ : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, -3; 1, 0, 0, -6; 0, 1, 0, 5; 0, 0, 1, 8]

/-- The trace sequence of `C₁` by its recurrence (Cayley–Hamilton), as a computable window. -/
def tq : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (4, 8, 74, 614)
  | k + 1 => let t := tq k; (t.2.1, t.2.2.1, t.2.2.2,
      8 * t.2.2.2 + 5 * t.2.2.1 - 6 * t.2.1 - 3 * t.1)

theorem C₁_four : C₁ ^ 4 = (8 : ℤ) • C₁ ^ 3 + (5 : ℤ) • C₁ ^ 2 - (6 : ℤ) • C₁ - (3 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide

theorem tq_eq (k : ℕ) : tq k = ((C₁ ^ k).trace, (C₁ ^ (k + 1)).trace, (C₁ ^ (k + 2)).trace,
    (C₁ ^ (k + 3)).trace) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h4 : C₁ ^ (k + 4) = (8 : ℤ) • C₁ ^ (k + 3) + (5 : ℤ) • C₁ ^ (k + 2) - (6 : ℤ) • C₁ ^ (k + 1) -
        (3 : ℤ) • C₁ ^ k := by
      rw [pow_add, C₁_four]
      simp only [mul_add, mul_sub, mul_smul_comm, ← pow_add, mul_one, ← pow_succ]
    rw [tq, ih]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    show _ = (C₁ ^ (k + 4)).trace
    rw [h4]
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

/-- **Native-checked range.**  `tr C₁^(3^n − 1) ≡ −1 (mod 3^(n+1))` for `2 ≤ n ≤ 9`. -/
theorem C₁_trace_mod : ∀ n ∈ Finset.Icc 2 9, ((tq (3 ^ n - 1)).1 + 1) % 3 ^ (n + 1) = 0 := by
  native_decide

theorem f₁_natDegree : f₁.natDegree = 4 := by
  unfold f₁; compute_degree!

theorem compM_f₁ : Matrix.reindex (finCongr f₁_natDegree) (finCongr f₁_natDegree)
    (compM ℤ f₁) = C₁ := by
  ext i j
  have hc : ∀ n : ℕ, f₁.coeff n = if n = 0 then 3 else if n = 1 then 6 else if n = 2 then -5
      else if n = 3 then -8 else if n = 4 then 1 else 0 := by
    intro n; unfold f₁
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X_pow,
      show (8 : ℤ[X]) * X ^ 3 = C 8 * X ^ 3 by simp, show (5 : ℤ[X]) * X ^ 2 = C 5 * X ^ 2 by simp,
      show (6 : ℤ[X]) * X = C 6 * X ^ 1 by simp, show (3 : ℤ[X]) = C 3 by simp, coeff_C]
    rcases n with _ | _ | _ | _ | _ | n <;> simp
  fin_cases i <;> fin_cases j <;> simp [compM, hc, f₁_natDegree, C₁]

theorem traceSeq_f₁ (N : ℕ) : traceSeq f₁ N = (C₁ ^ N).trace := by
  have htr : ∀ M : Matrix (Fin f₁.natDegree) (Fin f₁.natDegree) ℤ,
      (Matrix.reindex (finCongr f₁_natDegree) (finCongr f₁_natDegree) M).trace = M.trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp (finCongr f₁_natDegree).symm (fun i => M i i)
  rw [traceSeq, ← compM_f₁, ← Matrix.coe_reindexAlgEquiv ℤ ℤ, ← map_pow,
    Matrix.coe_reindexAlgEquiv, htr]

theorem generic_trace_congr_le_nine {n : ℕ} (hn1 : 2 ≤ n) (hn9 : n ≤ 9) :
    (3 : ℤ) ^ (n + 1) ∣ traceSeq f₁ (((3 : ℤ) ^ n + (-1)).toNat) + 1 := by
  have hpos : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hE : (((3 : ℤ) ^ n + (-1)).toNat) = 3 ^ n - 1 := by
    have : ((3 : ℤ) ^ n + (-1)) = ((3 ^ n - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hpos]; ring
    rw [this, Int.toNat_natCast]
  rw [hE, traceSeq_f₁]
  have h := C₁_trace_mod n (Finset.mem_Icc.2 ⟨hn1, hn9⟩)
  rw [tq_eq] at h
  exact Int.dvd_of_emod_eq_zero h

/-- **Believed (~95%)**: the congruence for every `n` (Hensel's idempotent for `X²(X − 1)²` and the
pair relation; numerically `v₃ = n + 1` exactly for `n ≤ 9`). -/
theorem generic_trace_congr (n : ℕ) (hn : 2 ≤ n) :
    (3 : ℤ) ^ (n + 1) ∣ traceSeq f₁ (((3 : ℤ) ^ n + (-1)).toNat) + 1 := by
  sorry

/-- **Believed (~99%, numerics)**: `f₁` is Pisot, and outside every class `(X − z)⁴ (mod 3)`. -/
theorem pisot_f₁ : (∃ α : ℝ, PisotDataAny f₁ α) ∧
    ∀ z : ZMod 3, f₁.map (Int.castRingHom (ZMod 3)) ≠ (X - Polynomial.C z) ^ f₁.natDegree := by
  sorry

/-! ## A non-`3`-adic input: the `q`-power class (phase 65 lap 4)

`f₁ ≡ (X² + X + 1)² (mod 2)`: every root of `f₁` mod `2` is double, so every power sum is even
(`f₁_trace_even`), and `f₁` has no prime traces along ANY exponent sequence (`not_primeTraces_f₁`).
The cubic cube class `(X − z)³ (mod 3)` is the case `q = 3` of the same mechanism
(`PowerClassKill`): if `f ≡ g^q (mod q)` then `q` divides every trace.  So `f₁` is not a
counterexample to the 3-adic + power-class combination; it only refutes the 3-adic route alone. -/

/-- Any degree: a prime dividing every trace kills prime traces along `3^n + s`. -/
theorem not_primeTraces_of_dvd_any {f : ℤ[X]} {α : ℝ} (hD : PisotDataAny f α) {q : ℕ}
    (hq : q.Prime) (hdvd : ∀ N, 1 ≤ N → (q : ℤ) ∣ traceSeq f N) (s : ℤ) : ¬ PrimeTraces f s := by
  intro hP
  have hE := shiftExp_tendsto s
  have hgrow := (traceSeq_tendsto_any hD).comp hE
  obtain ⟨n, ⟨p, hp, hpe⟩, hb, hE1⟩ := (hP.and ((hgrow.eventually_ge_atTop ((q : ℤ) + 1)).and
    (hE.eventually (eventually_ge_atTop 1)))).exists
  have hb' : (q : ℤ) + 1 ≤ traceSeq f ((3 : ℤ) ^ n + s).toNat := hb
  have hpq : p = q := by
    have : (q : ℤ) ∣ (p : ℤ) := hpe ▸ hdvd _ hE1
    have : q ∣ p := by exact_mod_cast this
    exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 this).symm
  rw [hpe, hpq] at hb'
  omega

/-- `f₁ ≡ (X² + X + 1)² (mod 2)`: every trace is even (recurrence mod `2`). -/
theorem f₁_trace_even (k : ℕ) : (2 : ℤ) ∣ (C₁ ^ k).trace := by
  have h : ∀ k, (2 : ℤ) ∣ (tq k).1 ∧ (2 : ℤ) ∣ (tq k).2.1 ∧ (2 : ℤ) ∣ (tq k).2.2.1 ∧
      (2 : ℤ) ∣ (tq k).2.2.2 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      obtain ⟨_, h1, h2, h3⟩ := ih
      refine ⟨h1, h2, h3, ?_⟩
      show (2 : ℤ) ∣ 8 * (tq k).2.2.2 + 5 * (tq k).2.2.1 - 6 * (tq k).2.1 - 3 * (tq k).1
      omega
  have := (h k).1
  rwa [tq_eq] at this

/-- **`f₁` has no prime traces**, for every shift `s` (from `pisot_f₁`, numerics, and the
`2`-power class).  The generic control of lap 3 is killed by the prime `2`. -/
theorem not_primeTraces_f₁ (s : ℤ) : ¬ PrimeTraces f₁ s := by
  obtain ⟨α, hD⟩ := pisot_f₁.1
  exact not_primeTraces_of_dvd_any hD Nat.prime_two
    (fun N _ => by rw [traceSeq_f₁]; exact_mod_cast f₁_trace_even N) s

/-- **Believed (~99%), the `q`-power class kill, any prime `q`, any degree.**  If
`f ≡ g^q (mod q)` then `q ∣ tr C^N` for every `N`.  English proof: over `𝔽̄_q` every root of
`f mod q` has multiplicity divisible by `q`, so the power sum `Σ m_i r_i^N ≡ 0`; and the trace
of `C^N` reduces to that power sum.  `q = 3`, `deg g = 1` is `HalfShiftRigidity.three_dvd_of_cube`;
`q = 2` for `f₁` is `f₁_trace_even`. -/
def PowerClassKill : Prop :=
  ∀ (f : ℤ[X]) (q : ℕ), f.Monic → q.Prime → ∀ g : (ZMod q)[X],
    f.map (Int.castRingHom (ZMod q)) = g ^ q → ∀ N : ℕ, (q : ℤ) ∣ traceSeq f N

theorem powerClassKill_holds : PowerClassKill := by
  sorry

/-! ## The generic leaf survives the 3-adic route AND the power class (lap 4 sibling scan)

Scan: quartic `X⁴ + c₃X³ + c₂X² + c₁X + c₀`, `c₃ ∈ [−12, −3]`, `|cᵢ| ≤ 9`, Pisot, irreducible over
`ℤ` (no linear or quadratic factor), not `(X ∓ 1)⁴ (mod 3)`, not a square mod `2`, `s ∈ [−4, 4]`,
with `tr C^(3^n + s) ≡ ±1 (mod 3^(n−1))` for `3 ≤ n ≤ 11`: exactly two survive,
`X⁴ − 11X³ − 8X² + 6X + 3` and `f₂ = X⁴ − 5X³ − 8X² − 6X − 3`, both `s = −1`.
`f₂ ≡ X²(X − 1)² (mod 3)`, `≡ X⁴ + X³ + 1` (irreducible) `mod 2`, roots `≈ 6.4064, −0.8650,
−0.2707 ± 0.6842i`; `v₃(tr C₂^(3^n − 1) + 1) = n + 1` exactly for `2 ≤ n ≤ 11`.  In degree 4 the
power class needs `q ∣ 4`, so `q = 2` is the only one, and `tr C₂ = 5` is odd.  What does kill it
numerically is a hit prime: `7 ∣ tr C₂^(3^n − 1)` for `n ≡ 3 (mod 4)`, `n ≥ 7`; also
`q = 2, 13, 17, 23, 31, …`.  So the generic leaf reduces to a covering node (`HitPrime`). -/

/-- `X⁴ − 5X³ − 8X² − 6X − 3`. -/
noncomputable def f₂ : ℤ[X] := X ^ 4 - 5 * X ^ 3 - 8 * X ^ 2 - 6 * X - 3

def C₂ : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, 3; 1, 0, 0, 6; 0, 1, 0, 8; 0, 0, 1, 5]

/-- Traces of `C₂^k, …, C₂^(k+3)` by the recurrence. -/
def tq₂ : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (4, 5, 41, 263)
  | k + 1 => let t := tq₂ k; (t.2.1, t.2.2.1, t.2.2.2,
      5 * t.2.2.2 + 8 * t.2.2.1 + 6 * t.2.1 + 3 * t.1)

theorem C₂_trace : C₂.trace = 5 := by decide

/-- `tq₂` matches the matrix traces at the start (the full identity is as for `tq_eq`). -/
theorem tq₂_start : tq₂ 0 = (C₂ ^ 0 |>.trace, (C₂ ^ 1).trace, (C₂ ^ 2).trace, (C₂ ^ 3).trace) := by
  decide

/-- **Native-checked**: `tr C₂^(3^n − 1) ≡ −1 (mod 3^(n+1))`, `2 ≤ n ≤ 9`, by the recurrence. -/
theorem C₂_trace_mod : ∀ n ∈ Finset.Icc 2 9, ((tq₂ (3 ^ n - 1)).1 + 1) % 3 ^ (n + 1) = 0 := by
  native_decide

/-- **Native-checked hit prime**: `7 ∣ tr C₂^(3^7 − 1)` (numerically for every `n ≡ 3 (mod 4)`, `n ≥ 7`). -/
theorem C₂_hit_seven : (tq₂ (3 ^ 7 - 1)).1 % 7 = 0 := by
  native_decide

/-- **Open node (hit prime), any degree `≥ 4`.**  Some prime divides `tr C^(3^n + s)` for
infinitely many `n`.  With `traceSeq_tendsto_any` this gives `¬ PrimeTraces f s`.  Implies both
degree-4 leaves; `UnipotentCovering` is its unipotent restriction.  Evidence: every instance met
(`f₀`: `q = 2, 11, 13`; `f₁`: `q = 2` at every `n`; `f₂`: `q = 7`).  Mechanism: none known.  Sibling
caution: the analogue for `2^(2^n) + 1` FAILS (Fermat numbers are pairwise coprime), so a proof
must use that `f` has degree `≥ 2` or the shift `s ≠ 0`, not the exponent shape alone. -/
def HitPrime : Prop :=
  ∀ (f : ℤ[X]) (α : ℝ), PisotDataAny f α → 4 ≤ f.natDegree → ∀ s : ℤ, s ≠ 0 →
    ∃ q : ℕ, q.Prime ∧ ∀ N : ℕ, ∃ n ≥ N, (q : ℤ) ∣ traceSeq f ((3 : ℤ) ^ n + s).toNat

/-- A hit prime kills prime traces (any degree). -/
theorem not_primeTraces_of_hit {f : ℤ[X]} {α : ℝ} (hD : PisotDataAny f α) {s : ℤ} {q : ℕ}
    (hq : q.Prime) (hhit : ∀ N : ℕ, ∃ n ≥ N, (q : ℤ) ∣ traceSeq f ((3 : ℤ) ^ n + s).toNat) :
    ¬ PrimeTraces f s := by
  intro hP
  have hgrow := (traceSeq_tendsto_any hD).comp (shiftExp_tendsto s)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hP.and (hgrow.eventually_ge_atTop ((q : ℤ) + 1)))
  obtain ⟨n, hn, hd⟩ := hhit N
  obtain ⟨⟨p, hp, hpe⟩, hb⟩ := hN n hn
  have hb' : (q : ℤ) + 1 ≤ traceSeq f ((3 : ℤ) ^ n + s).toNat := hb
  have hpq : p = q := by
    have : (q : ℤ) ∣ (p : ℤ) := hpe ▸ hd
    have : q ∣ p := by exact_mod_cast this
    exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 this).symm
  rw [hpe, hpq] at hb'
  omega

/-- `HitPrime` closes every degree-`≥ 4` instance of `PrimeTraces`. -/
theorem not_primeTraces_of_hitPrime (h : HitPrime) {f : ℤ[X]} {α : ℝ} (hD : PisotDataAny f α)
    (hdeg : 4 ≤ f.natDegree) {s : ℤ} (hs : s ≠ 0) : ¬ PrimeTraces f s := by
  obtain ⟨q, hq, hhit⟩ := h f α hD hdeg s hs
  exact not_primeTraces_of_hit hD hq hhit

/-- **Identity return at a prime dividing the degree** (a partial hit-prime mechanism).  If
`q ∣ deg f`, `C^P ≡ 1 (mod q)` and `P ∣ N`, then `q ∣ tr C^N` (the trace of the identity is
`deg f ≡ 0`).  So `HitPrime` holds whenever `3^n ≡ −s (mod P)` for infinitely many `n`; on `f₀`
(`q = 2`, `P = 15`, `−s = 1 ∉ ⟨3⟩ mod 15`) it does not apply, so it is not the uniform mechanism. -/
theorem dvd_traceSeq_of_pow_eq_one {f : ℤ[X]} {q P N : ℕ} (hqd : q ∣ f.natDegree)
    (hP : ((compM ℤ f).map (Int.castRingHom (ZMod q))) ^ P = 1) (hPN : P ∣ N) :
    (q : ℤ) ∣ traceSeq f N := by
  obtain ⟨k, rfl⟩ := hPN
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 ?_
  have h1 : ((traceSeq f (P * k) : ℤ) : ZMod q) =
      (((compM ℤ f).map (Int.castRingHom (ZMod q))) ^ (P * k)).trace := by
    rw [traceSeq, ← Matrix.map_pow]
    simp [Matrix.trace, Matrix.diag]
  rw [h1, pow_mul, hP, one_pow, Matrix.trace_one, Fintype.card_fin]
  exact (ZMod.natCast_eq_zero_iff _ _).2 hqd

end LeanFormalizations.Mills.ShiftRigidityUnipotent

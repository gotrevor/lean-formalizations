/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciPrimePow

/-!
# Phase 35: `L(c^n) + h` is composite i.o. for every odd prime `c` and every `h`

Lucas numbers `L(N) = tr A^N` (`A = !![1,1;1,0]`) are a **trace** sequence, so Frobenius fixes
them and there is no sign flip (phase 34).  Instead we use an **exact** composition identity.
See `SWEEP-PRIME-MODULUS.md`.

## Route
Let `lucasV x q k` be the Lucas `V`-sequence with parameters `P = x`, `Q = q`
(`V₀ = 2`, `V₁ = x`, `V_(k+2) = x V_(k+1) − q V_k`).
1. `lucasV_mul_odd`: for odd `m`, `V_(c·m)(P,−1) = lucasV (V_m) (−1) c`.  Route: for a 2×2 matrix `B`,
   Cayley–Hamilton gives `B^2 = (tr B) B − (det B) I`, so `tr (B^k) = lucasV (tr B) (det B) k`
   by induction; apply to `B = A^m` for `A = !![P, 1; 1, 0]` (`tr = V_m`, `det = (−1)^m = −1`).
2. `lucasV_neg_one_growth`: for odd `c ≥ 3` and `x ≠ 0`, `|x| + 3 ≤ |lucasV x (−1) c|`.  For
   `x ≥ 1` the sequence is increasing from `k = 1` and `V_3 = x^3 + 3x`; for `x ≤ −1` use
   oddness, `lucasV (−x) (−1) c = −lucasV x (−1) c` for odd `c`.
3. `lucas_prime_pow_mod`: `L(c^n) ≡ 1 (mod c)` (from `lucasV x (−1) c ≡ x^c ≡ x (mod c)` and
   Fermat, or from `L(c) ≡ 1` plus step 1).
4. Main theorem.  Suppose `p_n = L(c^n) + h` is prime for all `n ≥ n₀`.
   - The filter: `SharedConjecture.exists_trace_pow_congr` with base `c` (the trace version;
     `det A = −1`), plus growth, gives `n < v_c(glCard 2 p_n)` for large `n`.  Then
     `FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat` gives `L(c^n) ≡ x_n (mod c^(n/2))`
     with `x_n ∈ {1 − h, −1 − h}`.
   - Step 1 (with `c^n` odd) and integrality of `lucasV` give `x_(n+1) ≡ lucasV x_n (−1) c`.
     Both sides lie in fixed finite sets, so for large `n` this is an equality, and
     `|x_(n+1) − x_n| ≤ 2`.
   - Step 2 forces `x_n = 0`, hence `c^(n/2) ∣ L(c^n)`, contradicting step 3.

Note that `c = 2` is genuinely excluded: `L(2^n)` (`h = 0`) is a Fermat-type open problem.

Frozen: every statement below; statements of `FibonacciPrimePow`, `SaitoFibonacci`,
`LucasTwoPow`, `ThreeAdic`, `SharedConjecture`, `Projective`, and `Literature/`.  Do not mark new
declarations `private`.
-/

namespace LeanFormalizations.Mills.LucasPrimePow

open LeanFormalizations.Mills.ThreeAdic Filter

/-- The Lucas `V`-sequence with parameters `P = x`, `Q = q`. -/
def lucasV (x q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => x
  | k + 2 => x * lucasV x q (k + 1) - q * lucasV x q k

/-- The Lucas numbers, `L(N) = F(N−1) + F(N+1)`, as integers (`L 0 = 2`). -/
def lucasL (N : ℕ) : ℤ := lucasV 1 (-1) N

/-! ### Equation lemmas for `lucasV` -/

theorem lucasV_zero (x q : ℤ) : lucasV x q 0 = 2 := rfl

theorem lucasV_one (x q : ℤ) : lucasV x q 1 = x := rfl

theorem lucasV_succ_succ (x q : ℤ) (k : ℕ) :
    lucasV x q (k + 2) = x * lucasV x q (k + 1) - q * lucasV x q k := rfl

theorem lucasL_eq_fib (N : ℕ) : lucasL (N + 1) = Nat.fib N + Nat.fib (N + 2) := by
  induction N using Nat.twoStepInduction with
  | zero => norm_num [lucasL, lucasV_one]
  | one => norm_num [lucasL, lucasV_succ_succ, lucasV_one, lucasV_zero]
  | more N ih1 ih2 =>
      have e : lucasL (N + 2 + 1) = lucasL (N + 1 + 1) + lucasL (N + 1) := by
        simp only [lucasL, show N + 2 + 1 = (N + 1) + 2 from rfl, lucasV_succ_succ]
        ring
      rw [e, ih1, ih2]
      have f1 : Nat.fib (N + 1 + 2) = Nat.fib (N + 1) + Nat.fib (N + 2) := Nat.fib_add_two
      have f2 : Nat.fib (N + 2 + 2) = Nat.fib (N + 2) + Nat.fib (N + 1 + 2) := by
        rw [show N + 1 + 2 = N + 2 + 1 from by omega]; exact Nat.fib_add_two
      have f0 : Nat.fib (N + 2) = Nat.fib N + Nat.fib (N + 1) := Nat.fib_add_two
      rw [f2, f1, f0]
      push_cast
      ring

/-! ### Cayley–Hamilton and the trace of a power -/

/-- Cayley–Hamilton in dimension two, written out. -/
theorem sq_eq_trace_smul_sub_det (B : Matrix (Fin 2) (Fin 2) ℤ) :
    B ^ 2 = B.trace • B - B.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply_eq, Matrix.one_apply_ne, Ne, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    norm_num <;> ring

/-- **The trace of a power of a 2×2 matrix is a Lucas `V`-value.** -/
theorem trace_pow_eq_lucasV (B : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ) :
    (B ^ k).trace = lucasV B.trace B.det k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasV_zero]
  | one => simp [lucasV_one]
  | more k ih1 ih2 =>
      have hsplit : B ^ (k + 2) = B ^ k * B ^ 2 := by rw [← pow_add]
      have hk1 : B ^ k * B = B ^ (k + 1) := (pow_succ B k).symm
      rw [hsplit, sq_eq_trace_smul_sub_det, mul_sub, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.mul_one, hk1, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
        lucasV_succ_succ, ih1, ih2]
      simp [smul_eq_mul]

/-! ### Elementary identities for `lucasV · (−1)` -/

theorem lucasV_neg (x : ℤ) (k : ℕ) :
    lucasV (-x) (-1) k = (-1) ^ k * lucasV x (-1) k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasV_zero]
  | one => simp [lucasV_one]
  | more k ih1 ih2 =>
      rw [lucasV_succ_succ, lucasV_succ_succ, ih1, ih2]
      ring

/-- `lucasV · q k` is a polynomial with integer coefficients in its first argument, so it
respects congruences. -/
theorem dvd_lucasV_sub {m a b q : ℤ} (h : m ∣ a - b) (k : ℕ) :
    m ∣ lucasV a q k - lucasV b q k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasV_zero]
  | one => simpa [lucasV_one] using h
  | more k ih1 ih2 =>
      rw [lucasV_succ_succ, lucasV_succ_succ]
      have e : a * lucasV a q (k + 1) - q * lucasV a q k
            - (b * lucasV b q (k + 1) - q * lucasV b q k)
          = a * (lucasV a q (k + 1) - lucasV b q (k + 1)) + (a - b) * lucasV b q (k + 1)
            - q * (lucasV a q k - lucasV b q k) := by ring
      rw [e]
      exact dvd_sub (dvd_add (ih2.mul_left a) (h.mul_right _)) (ih1.mul_left q)

/-- The companion matrix of `x² − Px − 1`. -/
def lucasM (P : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![P, 1; 1, 0]

theorem lucasM_trace (P : ℤ) : (lucasM P).trace = P := by
  simp [lucasM, Matrix.trace_fin_two]

theorem lucasM_det (P : ℤ) : (lucasM P).det = -1 := by
  simp [lucasM, Matrix.det_fin_two]

theorem trace_lucasM_pow (P : ℤ) (N : ℕ) : ((lucasM P) ^ N).trace = lucasV P (-1) N := by
  rw [trace_pow_eq_lucasV, lucasM_trace, lucasM_det]

/-- **Composition.**  For odd `m`, `V_(c·m)(P, −1) = V_c(V_m(P, −1), −1)`; e.g. `L(c·m) = V_c(L(m), −1)`. -/
theorem lucasV_mul_odd (P : ℤ) (c : ℕ) {m : ℕ} (hm : Odd m) :
    lucasV P (-1) (c * m) = lucasV (lucasV P (-1) m) (-1) c := by
  have h2 : (((lucasM P) ^ m) ^ c).trace
      = lucasV (((lucasM P) ^ m).trace) (((lucasM P) ^ m).det) c := trace_pow_eq_lucasV _ _
  rw [Matrix.det_pow, lucasM_det, hm.neg_one_pow, trace_lucasM_pow, ← pow_mul,
    mul_comm m c, trace_lucasM_pow] at h2
  exact h2

/-- Doubling: `V_(2m) = V_m² − 2(−1)^m`. -/
theorem lucasV_two_mul (P : ℤ) (m : ℕ) :
    lucasV P (-1) (2 * m) = (lucasV P (-1) m) ^ 2 - 2 * (-1) ^ m := by
  have h2 : (((lucasM P) ^ m) ^ 2).trace
      = lucasV (((lucasM P) ^ m).trace) (((lucasM P) ^ m).det) 2 := trace_pow_eq_lucasV _ _
  rw [Matrix.det_pow, lucasM_det, trace_lucasM_pow, ← pow_mul, mul_comm m 2,
    trace_lucasM_pow] at h2
  rw [h2, show (2 : ℕ) = 0 + 2 from rfl, lucasV_succ_succ, lucasV_one, lucasV_zero]
  ring

/-! ### Growth -/

theorem lucasV_two (x : ℤ) : lucasV x (-1) 2 = x * x + 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, lucasV_succ_succ, lucasV_one, lucasV_zero]; ring

theorem lucasV_three (x : ℤ) : lucasV x (-1) 3 = x ^ 3 + 3 * x := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, lucasV_succ_succ, show (1 : ℕ) + 1 = 2 from rfl,
    lucasV_two, lucasV_one]
  ring

theorem lucasV_pos_lt {x : ℤ} (hx : 1 ≤ x) (k : ℕ) :
    1 ≤ lucasV x (-1) (k + 1) ∧ lucasV x (-1) (k + 1) < lucasV x (-1) (k + 2) := by
  induction k with
  | zero =>
      have e1 : lucasV x (-1) (0 + 1) = x := by norm_num [lucasV_one]
      have e2 : lucasV x (-1) (0 + 2) = x * x + 2 := by norm_num [lucasV_two]
      rw [e1, e2]
      exact ⟨hx, by nlinarith⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [lucasV_succ_succ] at h2 ⊢
      have hT : (0 : ℤ) ≤ x * lucasV x (-1) (k + 1) - -1 * lucasV x (-1) k := by linarith
      have key : (0 : ℤ) ≤ (x - 1) * (x * lucasV x (-1) (k + 1) - -1 * lucasV x (-1) k) :=
        mul_nonneg (by linarith) hT
      exact ⟨by linarith, by nlinarith [key]⟩

theorem one_le_lucasV {x : ℤ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ lucasV x (-1) k := by
  obtain ⟨u, rfl⟩ : ∃ u, k = u + 1 := ⟨k - 1, by omega⟩
  exact (lucasV_pos_lt hx u).1

theorem lucasV_strictMono {x : ℤ} (hx : 1 ≤ x) {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    lucasV x (-1) j < lucasV x (-1) k := by
  induction k with
  | zero => omega
  | succ k ih =>
      obtain ⟨u, rfl⟩ : ∃ u, k = u + 1 := ⟨k - 1, by omega⟩
      have hstep := (lucasV_pos_lt hx u).2
      rcases Nat.lt_or_ge j (u + 1) with hlt | hge
      · exact lt_trans (ih hlt) hstep
      · have : j = u + 1 := by omega
        rw [this]; exact hstep

theorem nat_le_lucasV {x : ℤ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℤ) ≤ lucasV x (-1) k := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa [lucasV_one] using hx
      · have h1 := ih hk0
        have h2 : lucasV x (-1) k < lucasV x (-1) (k + 1) :=
          lucasV_strictMono hx hk0 (by omega)
        push_cast
        omega

/-- For odd `c ≥ 3` and `x ≠ 0`, `V_c(x, −1)` is far from `x`. -/
theorem lucasV_neg_one_growth {c : ℕ} (hc : Odd c) (hc3 : 3 ≤ c) {x : ℤ} (hx : x ≠ 0) :
    |x| + 3 ≤ |lucasV x (-1) c| := by
  have key : ∀ y : ℤ, 1 ≤ y → y + 3 ≤ lucasV y (-1) c := by
    intro y hy
    have h3 : lucasV y (-1) 3 ≤ lucasV y (-1) c := by
      rcases eq_or_lt_of_le hc3 with heq | hlt
      · rw [heq]
      · exact (lucasV_strictMono hy (by omega) hlt).le
    rw [lucasV_three] at h3
    nlinarith [mul_nonneg (sub_nonneg.2 hy) (by nlinarith : (0:ℤ) ≤ y ^ 2 + y + 3)]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hy : (1 : ℤ) ≤ -x := by omega
    have := key (-x) hy
    have hneg' : lucasV x (-1) c = -lucasV (-x) (-1) c := by
      have := lucasV_neg (-x) c
      rw [neg_neg] at this
      rw [this, hc.neg_one_pow]
      ring
    rw [hneg', abs_neg, abs_of_nonneg (by omega : (0:ℤ) ≤ lucasV (-x) (-1) c),
      abs_of_neg hneg]
    omega
  · have hy : (1 : ℤ) ≤ x := hpos
    have := key x hy
    rw [abs_of_nonneg (by omega : (0:ℤ) ≤ lucasV x (-1) c), abs_of_pos hpos]
    omega

/-! ### Frobenius: `V_c(x, −1) ≡ x (mod c)` -/

theorem trace_mul_natCast (M : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ) :
    (M * (k : Matrix (Fin 2) (Fin 2) ℤ)).trace = (k : ℤ) * M.trace := by
  have hk : (k : Matrix (Fin 2) (Fin 2) ℤ) = (k : ℕ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [nsmul_eq_mul, mul_one]
  rw [hk, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, nsmul_eq_mul]

/-- `2 x^c ≡ 2 V_c(x, −1) (mod c)`: the binomial theorem for the two commuting matrices
`B` and `x·I − B`, both of trace `x` and determinant `−1`. -/
theorem dvd_two_mul_lucasV_sub_pow {c : ℕ} (hc : c.Prime) (x : ℤ) :
    (c : ℤ) ∣ 2 * x ^ c - 2 * lucasV x (-1) c := by
  set B : Matrix (Fin 2) (Fin 2) ℤ := !![x, 1; 1, 0] with hB
  set B' : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; -1, x] with hB'
  set D : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal (fun _ : Fin 2 => x) with hD
  have hcomm : Commute B B' := by
    show B * B' = B' * B
    rw [hB, hB']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hsum : B + B' = D := by
    rw [hB, hB', hD]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.diagonal_apply]
  have htrB : B.trace = x := by rw [hB]; simp [Matrix.trace_fin_two]
  have hdetB : B.det = -1 := by rw [hB]; simp [Matrix.det_fin_two]
  have htrB' : B'.trace = x := by rw [hB']; simp [Matrix.trace_fin_two]
  have hdetB' : B'.det = -1 := by rw [hB']; simp [Matrix.det_fin_two]
  have hends : ∀ k : ℕ, (B ^ k).trace = lucasV x (-1) k ∧ (B' ^ k).trace = lucasV x (-1) k := by
    intro k
    refine ⟨?_, ?_⟩
    · rw [trace_pow_eq_lucasV, htrB, hdetB]
    · rw [trace_pow_eq_lucasV, htrB', hdetB']
  have hDtr : (D ^ c).trace = 2 * x ^ c := by
    rw [hD, Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_two]
    simp [Pi.pow_apply]
    ring
  have hexp := hcomm.add_pow c
  set g : ℕ → ℤ := fun m => (c.choose m : ℤ) * (B ^ m * B' ^ (c - m)).trace with hg
  have hsumtr : (2 : ℤ) * x ^ c = ∑ m ∈ Finset.range (c + 1), g m := by
    rw [← hDtr, ← hsum, hexp, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun m _ => trace_mul_natCast _ _
  have hcpos : 0 < c := hc.pos
  obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have hpeel : ∑ m ∈ Finset.range (c + 1), g m
      = (g 0 + ∑ i ∈ Finset.range d, g (i + 1)) + g c := by
    rw [Finset.sum_range_succ]
    congr 1
    rw [hd, Finset.sum_range_succ']
    ring
  have hg0 : g 0 = lucasV x (-1) c := by
    simp only [hg, pow_zero, Matrix.one_mul, Nat.choose_zero_right, Nat.cast_one,
      Nat.sub_zero, one_mul]
    exact (hends c).2
  have hgc : g c = lucasV x (-1) c := by
    simp only [hg, Nat.sub_self, pow_zero, Matrix.mul_one, Nat.choose_self, Nat.cast_one,
      one_mul]
    exact (hends c).1
  have hmid : (c : ℤ) ∣ ∑ i ∈ Finset.range d, g (i + 1) := by
    refine Finset.dvd_sum ?_
    intro i hi
    have hilt : i + 1 < c := by
      have := Finset.mem_range.1 hi
      omega
    have hdvd : (c : ℤ) ∣ (c.choose (i + 1) : ℤ) := by
      have := hc.dvd_choose_self (by omega) hilt
      exact_mod_cast this
    exact Dvd.dvd.mul_right hdvd _
  rw [hpeel, hg0, hgc] at hsumtr
  have hfin : 2 * x ^ c - 2 * lucasV x (-1) c = ∑ i ∈ Finset.range d, g (i + 1) := by
    linarith [hsumtr]
  rw [hfin]
  exact hmid

/-- **Frobenius.**  `V_c(x, −1) ≡ x (mod c)` for a prime `c ≠ 2`. -/
theorem lucasV_prime_mod {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (x : ℤ) :
    (c : ℤ) ∣ lucasV x (-1) c - x := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hfermat : (c : ℤ) ∣ x ^ c - x := by
    have : ((x ^ c - x : ℤ) : ZMod c) = 0 := by
      push_cast
      rw [ZMod.pow_card]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have h2 := dvd_two_mul_lucasV_sub_pow hc x
  have hcomb : (c : ℤ) ∣ 2 * (x - lucasV x (-1) c) := by
    have e : 2 * (x - lucasV x (-1) c)
        = (2 * x ^ c - 2 * lucasV x (-1) c) - 2 * (x ^ c - x) := by ring
    rw [e]
    exact dvd_sub h2 (hfermat.mul_left 2)
  have hcZ : Prime (c : ℤ) := Nat.prime_iff_prime_int.1 hc
  rcases (hcZ.dvd_mul.1 hcomb) with hd | hd
  · have := Int.le_of_dvd (by norm_num) hd
    have := hc.two_le
    have hc3 : 3 ≤ c := by
      rcases Nat.lt_or_ge c 3 with h | h
      · interval_cases c <;> simp_all
      · exact h
    have : (3 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc3
    omega
  · have : (c : ℤ) ∣ -(lucasV x (-1) c - x) := by simpa [neg_sub] using hd
    exact (dvd_neg.1 this)

/-- `V_(c^n)(P, −1) ≡ P (mod c)` for an odd prime `c`. -/
theorem lucasV_prime_pow_mod {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (P : ℤ) (n : ℕ) :
    (c : ℤ) ∣ lucasV P (-1) (c ^ n) - P := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  induction n with
  | zero => simp [lucasV_one]
  | succ n ih =>
      have hodd : Odd (c ^ n) := hcodd.pow
      have hstep : lucasV P (-1) (c ^ (n + 1)) = lucasV (lucasV P (-1) (c ^ n)) (-1) c := by
        rw [pow_succ, mul_comm]
        exact lucasV_mul_odd P c hodd
      have h1 := lucasV_prime_mod hc hc2 (lucasV P (-1) (c ^ n))
      rw [← hstep] at h1
      have e : lucasV P (-1) (c ^ (n + 1)) - P
          = (lucasV P (-1) (c ^ (n + 1)) - lucasV P (-1) (c ^ n))
            + (lucasV P (-1) (c ^ n) - P) := by ring
      rw [e]
      exact dvd_add h1 ih

/-- `L(c^n) ≡ 1 (mod c)` for a prime `c`. -/
theorem lucas_prime_pow_mod {c : ℕ} (hc : c.Prime) (n : ℕ) :
    (c : ℤ) ∣ lucasL (c ^ n) - 1 := by
  rcases eq_or_ne c 2 with rfl | hc2
  · -- `L(2^n)` is odd, by the doubling identity `V_(2m) = V_m² − 2(−1)^m`
    induction n with
    | zero => simp [lucasL, lucasV_one]
    | succ n ih =>
        have hstep : lucasL (2 ^ (n + 1))
            = (lucasL (2 ^ n)) ^ 2 - 2 * (-1) ^ (2 ^ n) := by
          rw [lucasL, lucasL, pow_succ, mul_comm]
          exact lucasV_two_mul 1 (2 ^ n)
        rw [hstep]
        have e : (lucasL (2 ^ n)) ^ 2 - 2 * (-1 : ℤ) ^ (2 ^ n) - 1
            = (lucasL (2 ^ n) - 1) * (lucasL (2 ^ n) + 1) - 2 * (-1) ^ (2 ^ n) := by ring
        rw [e]
        exact dvd_sub (ih.mul_right _) (Dvd.intro _ rfl)
  · simpa [lucasL] using lucasV_prime_pow_mod hc hc2 1 n

/-! ### The filter -/

/-- **The mechanism** (prime as modulus), read off the trace of `lucasM P`. -/
theorem exists_lucasV_prime_pow_congr {c p m : ℕ} (P : ℤ) (hp : p.Prime) (hc : c.Prime)
    (hv : padicValNat c (glCard 2 p) ≤ m) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ lucasV P (-1) (c ^ (m + j)) - lucasV P (-1) (c ^ m) := by
  have hdet : ¬ (p : ℤ) ∣ (lucasM P).det := by
    rw [lucasM_det]
    intro hdd
    have h1 : (p : ℤ) ∣ 1 := dvd_neg.mp hdd
    have h2 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have := hp.two_le
    omega
  obtain ⟨j, hj1, hj⟩ :=
    SharedConjecture.exists_trace_pow_congr (lucasM P) hp hc hdet hv
  refine ⟨j, hj1, ?_⟩
  rwa [trace_lucasM_pow, trace_lucasM_pow] at hj

/-- The main argument, for `P ≥ 1`. -/
theorem lucasV_prime_pow_add_not_prime_pos {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP1 : 1 ≤ P) (hPc : ¬ (c : ℤ) ∣ P) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasV P (-1) (c ^ n) + h) := by
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with hlt | hge
    · interval_cases c <;> simp_all
    · exact hge
  have hcle : 2 ≤ c := by omega
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  set t : ℕ → ℤ := fun n => lucasV P (-1) (c ^ n) + h with ht
  set H : ℕ := h.natAbs with hH
  set Bnd : ℤ := |lucasV (1 - h) (-1) c| + |lucasV (-1 - h) (-1) c| + |h| + 3 with hBnd
  set Bn : ℕ := Bnd.toNat with hBn
  set N : ℕ := max (max 5 n₀) (c + H + 5) with hNdef
  have hN5 : 5 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNn₀ : n₀ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNc : c + H + 5 ≤ N := le_max_right _ _
  have hVn : ∀ n : ℕ, (n : ℤ) ≤ lucasV P (-1) (c ^ n) := by
    intro n
    have h1 : n ≤ c ^ n := le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hcle n)
    have h2 : ((c ^ n : ℕ) : ℤ) ≤ lucasV P (-1) (c ^ n) :=
      nat_le_lucasV hP1 (Nat.one_le_pow _ _ hc.pos)
    have h3 : (n : ℤ) ≤ ((c ^ n : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  have hbig : ∀ n ≥ N, (c : ℤ) < t n := by
    intro n hn
    have hlow : (c : ℤ) + (H : ℤ) + 5 ≤ (n : ℤ) := by
      have h1 : ((c + H + 5 : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNc
      have h2 : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      push_cast at h1
      omega
    have habs : -(H : ℤ) ≤ h := by
      have : h.natAbs = H := rfl
      omega
    have := hVn n
    simp only [ht]
    omega
  have hprime : ∀ n ≥ N, Prime (t n) := fun n hn => hn₀ n (le_trans hNn₀ hn)
  have htmono : ∀ {m n : ℕ}, 1 ≤ m → m < n → t m < t n := by
    intro m n hm hmn
    have h1 : lucasV P (-1) (c ^ m) < lucasV P (-1) (c ^ n) :=
      lucasV_strictMono hP1 (Nat.one_le_pow _ _ hc.pos)
        (Nat.pow_lt_pow_right (by omega) hmn)
    simp only [ht]
    omega
  have hnat : ∀ n ≥ N, ∃ p : ℕ, p.Prime ∧ p ≠ c ∧ (p : ℤ) = t n := by
    intro n hn
    have hb := hbig n hn
    have hc0 : (0 : ℤ) < (c : ℤ) := by positivity
    refine ⟨(t n).toNat, ?_, ?_, by omega⟩
    · have := hprime n hn
      rw [Int.prime_iff_natAbs_prime] at this
      have hEq : (t n).natAbs = (t n).toNat := by omega
      rwa [hEq] at this
    · intro hEq
      have : (c : ℤ) = ((t n).toNat : ℤ) := by rw [← hEq]
      omega
  have hstep2 : ∀ n ≥ N, ∀ p : ℕ, p.Prime → (p : ℤ) = t n →
      ¬ (padicValNat c (glCard 2 p) ≤ n) := by
    intro n hn p hp hpv hv
    obtain ⟨j, hj1, hj01⟩ := exists_lucasV_prime_pow_congr P hp hc hv
    have hdvd : (p : ℤ) ∣ t (n + j) := by
      have h1 : (p : ℤ) ∣ t n := by rw [hpv]
      have h2 : t (n + j) - t n
          = lucasV P (-1) (c ^ (n + j)) - lucasV P (-1) (c ^ n) := by simp only [ht]; ring
      have h3 := dvd_add hj01 h1
      rw [← h2] at h3
      simpa using h3
    have hgt : t n < t (n + j) := htmono (by omega) (by omega)
    have hq := hprime (n + j) (by omega)
    have hqpos : 0 < t (n + j) := by have := hbig n hn; have := hc.two_le; omega
    obtain ⟨q, hqv⟩ : ∃ q : ℕ, (q : ℤ) = t (n + j) := ⟨(t (n + j)).toNat, by omega⟩
    have hqnat : q.Prime := by
      rw [Int.prime_iff_natAbs_prime] at hq
      have hEq : (t (n + j)).natAbs = q := by omega
      rwa [hEq] at hq
    have hdq : p ∣ q := by
      have : (p : ℤ) ∣ (q : ℤ) := by rw [hqv]; exact hdvd
      exact_mod_cast this
    have hp1 : 1 < p := hp.one_lt
    rcases hqnat.eq_one_or_self_of_dvd p hdq with hh | hh <;> omega
  have hstep3 : ∀ n ≥ N, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (c : ℤ) ^ (n / 2) ∣ t n - s := by
    intro n hn
    obtain ⟨p, hp, hpc, hpv⟩ := hnat n hn
    have hlt : n < padicValNat c (glCard 2 p) := by
      by_contra hle
      exact hstep2 n hn p hp hpv (by omega)
    rcases FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat hc hc2 hp hpc hlt with hd | hd
    · exact ⟨1, Or.inl rfl, by rw [← hpv]; exact hd⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [← hpv]
      simpa using hd
  -- choose `n` large
  set n : ℕ := 2 * (Bn + N + 3) with hn
  set e : ℕ := Bn + N + 3 with he
  have hne : n / 2 = e := by omega
  have hnN : N ≤ n := by omega
  have hBndpos : 0 ≤ Bnd := by positivity
  have hBncast : ((Bn : ℕ) : ℤ) = Bnd := Int.toNat_of_nonneg hBndpos
  have hbnd : Bnd < (c : ℤ) ^ e := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ e ≤ c ^ e := Nat.pow_le_pow_left hcle e
    have h3 : Bn < c ^ e := by omega
    have h4 : ((Bn : ℕ) : ℤ) < ((c ^ e : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at h4
    linarith [hBncast]
  obtain ⟨s, hs, hsd⟩ := hstep3 n hnN
  obtain ⟨s', hs', hsd'⟩ := hstep3 (n + 1) (by omega)
  rw [hne] at hsd
  have hsd'' : (c : ℤ) ^ e ∣ t (n + 1) - s' := by
    refine dvd_trans (pow_dvd_pow _ ?_) hsd'
    omega
  set x : ℤ := s - h with hx
  set x' : ℤ := s' - h with hx'
  have hVx : (c : ℤ) ^ e ∣ lucasV P (-1) (c ^ n) - x := by
    have : lucasV P (-1) (c ^ n) - x = t n - s := by simp only [ht, hx]; ring
    rw [this]; exact hsd
  have hVx' : (c : ℤ) ^ e ∣ lucasV P (-1) (c ^ (n + 1)) - x' := by
    have : lucasV P (-1) (c ^ (n + 1)) - x' = t (n + 1) - s' := by simp only [ht, hx']; ring
    rw [this]; exact hsd''
  have hcomp : lucasV P (-1) (c ^ (n + 1)) = lucasV (lucasV P (-1) (c ^ n)) (-1) c := by
    rw [pow_succ, mul_comm]
    exact lucasV_mul_odd P c hcodd.pow
  have hkey : (c : ℤ) ^ e ∣ lucasV x (-1) c - x' := by
    have h1 : (c : ℤ) ^ e ∣ lucasV (lucasV P (-1) (c ^ n)) (-1) c - lucasV x (-1) c :=
      dvd_lucasV_sub hVx c
    have e2 : lucasV x (-1) c - x'
        = (lucasV P (-1) (c ^ (n + 1)) - x')
          - (lucasV (lucasV P (-1) (c ^ n)) (-1) c - lucasV x (-1) c) := by
      rw [hcomp]; ring
    rw [e2]
    exact dvd_sub hVx' h1
  -- the growth bound forces `x = 0`
  have hxcases : x = 1 - h ∨ x = -1 - h := by
    rcases hs with hh | hh
    · exact Or.inl (by rw [hx, hh])
    · exact Or.inr (by rw [hx, hh])
  have hx0 : x = 0 := by
    by_contra hxne
    have hgr := lucasV_neg_one_growth hcodd hc3 hxne
    have hxx' : |x' - x| ≤ 2 := by
      have e : x' - x = s' - s := by rw [hx, hx']; ring
      rw [e]
      rcases hs with hh | hh <;> rcases hs' with hh' | hh' <;> rw [hh, hh'] <;> norm_num
    have hxabs : |x| ≤ |h| + 1 := by
      rcases hxcases with he | he <;> rw [he] <;>
        rcases abs_cases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [abs_le] <;> omega
    have hx'abs : |x'| ≤ |h| + 1 := by
      rcases hs' with hh | hh <;> rw [hx', hh] <;>
        rcases abs_cases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [abs_le] <;> omega
    have hLbound : |lucasV x (-1) c| ≤ |lucasV (1 - h) (-1) c| + |lucasV (-1 - h) (-1) c| := by
      rcases hxcases with he | he
      · rw [he]; have := abs_nonneg (lucasV (-1 - h) (-1) c); omega
      · rw [he]; have := abs_nonneg (lucasV (1 - h) (-1) c); omega
    have hne0 : lucasV x (-1) c - x' ≠ 0 := by
      intro hzero
      have : |lucasV x (-1) c| = |x'| := by rw [show lucasV x (-1) c = x' by omega]
      have h1 : |x| + 3 ≤ |x'| := by omega
      have h2 : |x'| ≤ |x| + 2 := by
        have := abs_sub_abs_le_abs_sub x' x
        omega
      omega
    have hle := Int.le_of_dvd (abs_pos.2 hne0) ((dvd_abs _ _).2 hkey)
    have hb : |lucasV x (-1) c - x'| ≤ |lucasV x (-1) c| + |x'| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    rw [hBnd] at hbnd
    linarith
  -- `x = 0` forces `c ∣ V(c^n)`, contradicting `V(c^n) ≡ P (mod c)`
  have hcdvd : (c : ℤ) ∣ lucasV P (-1) (c ^ n) := by
    have h1 : (c : ℤ) ^ e ∣ lucasV P (-1) (c ^ n) := by
      rw [hx0, sub_zero] at hVx; exact hVx
    refine dvd_trans ?_ h1
    exact dvd_pow_self _ (by omega)
  have := lucasV_prime_pow_mod hc hc2 P n
  exact hPc (by have := dvd_sub hcdvd this; simpa using this)

/-- **General `P`.**  For `Q = −1`, an odd prime `c ∤ P`, and every `h`, `V(c^n) + h` is composite
infinitely often.  (Same proof: `V_(c^n)(P, −1) ≡ P (mod c)` replaces step 3; `P ≠ 0` gives
growth.  If `c ∣ P` the survivors `h = ±1` genuinely appear.) -/
theorem lucasV_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP : ¬ (c : ℤ) ∣ P) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasV P (-1) (c ^ n) + h) := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hP0 : P ≠ 0 := by
    intro hzero; exact hP (by simp [hzero])
  rcases lt_or_gt_of_ne hP0 with hneg | hpos
  · -- replace `P` by `−P` and `h` by `−h`
    have hP' : ¬ (c : ℤ) ∣ -P := fun hd => hP (dvd_neg.1 hd)
    have hmain := lucasV_prime_pow_add_not_prime_pos hc hc2 (by omega : (1:ℤ) ≤ -P) hP' (-h)
    refine hmain.mono ?_
    intro n hn hpr
    refine hn ?_
    have hflip : lucasV (-P) (-1) (c ^ n) = -lucasV P (-1) (c ^ n) := by
      rw [lucasV_neg, (hcodd.pow (n := n)).neg_one_pow]
      ring
    rw [hflip]
    have : -lucasV P (-1) (c ^ n) + -h = -(lucasV P (-1) (c ^ n) + h) := by ring
    rw [this]
    exact hpr.neg
  · exact lucasV_prime_pow_add_not_prime_pos hc hc2 hpos hP h

/-- **`L(c^n) + h` is composite infinitely often, for every odd prime `c` and every `h`.** -/
theorem lucas_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasL (c ^ n) + h) := by
  have hP : ¬ (c : ℤ) ∣ (1 : ℤ) := by
    intro hd
    have := Int.le_of_dvd one_pos hd
    have := hc.two_le
    omega
  simpa [lucasL] using lucasV_prime_pow_add_not_prime hc hc2 hP h

end LeanFormalizations.Mills.LucasPrimePow

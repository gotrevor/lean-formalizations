/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.CoveringEngine

/-!
# Phase 42: 2×2 traces at odd primes — `DoubleExpTraceComposite` for `n = 2`, classified

Theorem B of `ROADMAP-PRIME-TOWERS.md`.  Take `C ∈ M₂(ℤ)` and an odd prime `c` with
`det C ≡ ε = ±1 (mod c)`, `c ∤ tr C`, `c ∤ disc C`.  Then `tr C^(c^n) + h` is composite i.o. for
**every** `h`, except when `ε = 1` and `tr C ≡ ±1 (mod c)`, i.e. `χ_C ≡ X² ∓ X + 1 = Φ₆, Φ₃`.  In that
case the `c`-adic limit is exactly `τ = ±1`, and the shifts `h ∈ {0, ∓2}` genuinely survive the
filter (Fermat-type).  Numerics: 1276 cases, 0 mismatches.

## Route
1. `trace_pow_prime_congr`: with `Q = det C` and `t_n = tr C^(c^n)`,
   `t_(n+1) ≡ lucasV t_n ε c (mod c^(n+1))`.  Use `trace_pow_eq_lucasV` (phase 35) on
   `B = C^(c^n)`: `t_(n+1) = lucasV t_n (Q^(c^n)) c` exactly; `Q ≡ ε (mod c)` gives
   `Q^(c^n) ≡ ε (mod c^(n+1))` (lifting the exponent: `(ε + c y)^(c^n)`); then `dvd_lucasV_sub`-style
   congruence in the `q` argument.
2. Filter: `SharedConjecture.exists_trace_pow_congr` (trace version) plus
   `FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat` give `t_n ≡ x_n ∈ {±1 − h}` mod
   `c^(n/2)` for all large `n` if every term is prime.
3. Finite sets ⟹ `x_(n+1) = lucasV x_n ε c` exactly for large `n`.
   - `ε = −1`: `lucasV_neg_one_growth` ⟹ `x_n = 0`, contradicting `c ∤ tr C` (since `t_n ≡ tr C`).
   - `ε = +1`: `lucasV x 1 c` (`= 2T_c(x/2)`): `|x| ≥ 3` grows (prove `|x| + 3 ≤ |lucasV x 1 c|`).
     `x ∈ {0, ±2}` are excluded by `c ∤ tr C · disc C` (`t_n ≡ tr C`, and `x = ±2` means
     `t_n² − 4 ≡ 0`, i.e. `disc ≡ 0`).  `x = ±1` with `tr C ≡ ±1` is the excluded `Φ₆`/`Φ₃`
     class; `x = ±1` otherwise contradicts `t_n ≡ tr C (mod c)`.  Also rule out 2-cycles inside
     `{x, x ± 2}` (check `lucasV x 1 c ∈ {x ± 2}` has no admissible solution).
4. `trace_phi_survivor`: in the exceptional class, `c^(n+1) ∣ tr C^(c^n) − τ` (checked
   numerically: `v_c = n + 1` exactly).  Induction with step 1: `lucasV τ 1 c = τ` for
   `τ = ±1` when `c ≡ ±1 (mod 6)`, and the derivative is `≡ 0 (mod c)`.

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.TraceClassification

open LeanFormalizations.Mills.ThreeAdic LeanFormalizations.Mills.LucasPrimePow Filter
open LeanFormalizations.Mills.FibonacciCoveringAllPrimes
open LeanFormalizations.Mills.CoveringEngine

/-! ### Congruence and lifting-the-exponent plumbing -/

/-- `lucasV x · k` respects congruences in the `q` argument. -/
theorem dvd_lucasV_sub_q {m x a b : ℤ} (h : m ∣ a - b) (k : ℕ) :
    m ∣ lucasV x a k - lucasV x b k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasV_zero]
  | one => simp [lucasV_one]
  | more k ih1 ih2 =>
      rw [lucasV_succ_succ, lucasV_succ_succ]
      have e : x * lucasV x a (k + 1) - a * lucasV x a k
            - (x * lucasV x b (k + 1) - b * lucasV x b k)
          = x * (lucasV x a (k + 1) - lucasV x b (k + 1))
            - (a * (lucasV x a k - lucasV x b k) + (a - b) * lucasV x b k) := by ring
      rw [e]
      exact dvd_sub (ih2.mul_left x) (dvd_add (ih1.mul_left a) (h.mul_right _))

/-- Lifting the exponent, one step: `a ≡ b (mod c^k)` with `k ≥ 1` implies
`a^c ≡ b^c (mod c^(k+1))`. -/
theorem pow_succ_dvd_pow_sub_pow {c : ℕ} (_hc : c.Prime) {k : ℕ} (hk : 1 ≤ k) {a b : ℤ}
    (h : (c : ℤ) ^ k ∣ a - b) : (c : ℤ) ^ (k + 1) ∣ a ^ c - b ^ c := by
  have hcab : (c : ℤ) ∣ a - b := dvd_trans (dvd_pow_self _ (by omega)) h
  have hsum : (c : ℤ) ∣ ∑ i ∈ Finset.range c, a ^ i * b ^ (c - 1 - i) := by
    have e : (∑ i ∈ Finset.range c, a ^ i * b ^ (c - 1 - i))
        = (∑ i ∈ Finset.range c, (a ^ i * b ^ (c - 1 - i) - b ^ (c - 1)))
          + (c : ℤ) * b ^ (c - 1) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const]
    rw [e]
    refine dvd_add (Finset.dvd_sum ?_) ⟨b ^ (c - 1), rfl⟩
    intro i hi
    have hilt : i < c := Finset.mem_range.1 hi
    have hb : b ^ (c - 1) = b ^ i * b ^ (c - 1 - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hb, ← sub_mul]
    exact Dvd.dvd.mul_right (dvd_trans hcab (sub_dvd_pow_sub_pow a b i)) _
  have hgs := geom_sum₂_mul a b c
  rw [← hgs, show ((c : ℤ)) ^ (k + 1) = (c : ℤ) * (c : ℤ) ^ k from by ring]
  exact mul_dvd_mul hsum h

/-- `Q ≡ ε (mod c)` with `ε = ±1`, `c` odd prime ⟹ `Q^(c^n) ≡ ε (mod c^(n+1))`. -/
theorem pow_pow_dvd_sub {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {ε Q : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hQ : (c : ℤ) ∣ Q - ε) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ Q ^ (c ^ n) - ε := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  induction n with
  | zero => simpa using hQ
  | succ n ih =>
      have h1 : (c : ℤ) ^ (n + 2) ∣ (Q ^ (c ^ n)) ^ c - ε ^ c :=
        pow_succ_dvd_pow_sub_pow hc (by omega) ih
      have he : ε ^ c = ε := by
        rcases hε with rfl | rfl
        · simp
        · simpa using hcodd.neg_one_pow
      rw [he, ← pow_mul, ← pow_succ] at h1
      exact h1

/-- The Lucas `U`-sequence with parameters `P = x`, `Q = q`. -/
def lucasU (x q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => x * lucasU x q (k + 1) - q * lucasU x q k

theorem lucasU_zero (x q : ℤ) : lucasU x q 0 = 0 := rfl
theorem lucasU_one (x q : ℤ) : lucasU x q 1 = 1 := rfl
theorem lucasU_succ_succ (x q : ℤ) (k : ℕ) :
    lucasU x q (k + 2) = x * lucasU x q (k + 1) - q * lucasU x q k := rfl

/-- `lucasU` respects congruences in both arguments. -/
theorem dvd_lucasU_sub {m x y a b : ℤ} (hx : m ∣ x - y) (hq : m ∣ a - b) (k : ℕ) :
    m ∣ lucasU x a k - lucasU y b k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasU_zero]
  | one => simp [lucasU_one]
  | more k ih1 ih2 =>
      rw [lucasU_succ_succ, lucasU_succ_succ]
      have e : x * lucasU x a (k + 1) - a * lucasU x a k
            - (y * lucasU y b (k + 1) - b * lucasU y b k)
          = (x * (lucasU x a (k + 1) - lucasU y b (k + 1)) + (x - y) * lucasU y b (k + 1))
            - (a * (lucasU x a k - lucasU y b k) + (a - b) * lucasU y b k) := by ring
      rw [e]
      exact dvd_sub (dvd_add (ih2.mul_left x) (hx.mul_right _))
        (dvd_add (ih1.mul_left a) (hq.mul_right _))

/-- `lucasV` respects congruences in both arguments. -/
theorem dvd_lucasV_sub' {m x y a b : ℤ} (hx : m ∣ x - y) (hq : m ∣ a - b) (k : ℕ) :
    m ∣ lucasV x a k - lucasV y b k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasV_zero]
  | one => simpa [lucasV_one] using hx
  | more k ih1 ih2 =>
      rw [lucasV_succ_succ, lucasV_succ_succ]
      have e : x * lucasV x a (k + 1) - a * lucasV x a k
            - (y * lucasV y b (k + 1) - b * lucasV y b k)
          = (x * (lucasV x a (k + 1) - lucasV y b (k + 1)) + (x - y) * lucasV y b (k + 1))
            - (a * (lucasV x a k - lucasV y b k) + (a - b) * lucasV y b k) := by ring
      rw [e]
      exact dvd_sub (dvd_add (ih2.mul_left x) (hx.mul_right _))
        (dvd_add (ih1.mul_left a) (hq.mul_right _))

/-- **Cayley–Hamilton, iterated**: every power of a 2×2 matrix is an explicit `ℤ`-combination
of `B` and `1`, with `lucasU` coefficients. -/
theorem pow_eq_lucasU_smul (B : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ) :
    B ^ (k + 1) = lucasU B.trace B.det (k + 1) • B
      - (B.det * lucasU B.trace B.det k) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  induction k with
  | zero => simp [lucasU_one, lucasU_zero]
  | succ k ih =>
      have hstep : B ^ (k + 2) = B ^ (k + 1) * B := by rw [pow_succ]
      rw [hstep, ih, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
        ← pow_two, sq_eq_trace_smul_sub_det, smul_sub, smul_smul, smul_smul,
        lucasU_succ_succ]
      rw [sub_smul, mul_smul]
      module

/-! ### `V_k(±1, 1)` -/

theorem lucasV_neg' (x q : ℤ) (k : ℕ) :
    lucasV (-x) q k = (-1) ^ k * lucasV x q k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasV_zero]
  | one => simp [lucasV_one]
  | more k ih1 ih2 =>
      rw [lucasV_succ_succ, lucasV_succ_succ, ih1, ih2]
      ring

private theorem vals : lucasV 1 1 2 = -1 ∧ lucasV 1 1 3 = -2 ∧ lucasV 1 1 4 = -1
    ∧ lucasV 1 1 5 = 1 ∧ lucasV 1 1 6 = 2 ∧ lucasV 1 1 7 = 1 := by
  have e2 : lucasV 1 1 2 = -1 := by
    rw [show (2:ℕ) = 0 + 2 from rfl, lucasV_succ_succ, lucasV_one, lucasV_zero]; ring
  have e3 : lucasV 1 1 3 = -2 := by
    rw [show (3:ℕ) = 1 + 2 from rfl, lucasV_succ_succ, show (1:ℕ) + 1 = 2 from rfl, e2,
      lucasV_one]; ring
  have e4 : lucasV 1 1 4 = -1 := by
    rw [show (4:ℕ) = 2 + 2 from rfl, lucasV_succ_succ, show (2:ℕ) + 1 = 3 from rfl, e3, e2]; ring
  have e5 : lucasV 1 1 5 = 1 := by
    rw [show (5:ℕ) = 3 + 2 from rfl, lucasV_succ_succ, show (3:ℕ) + 1 = 4 from rfl, e4, e3]; ring
  have e6 : lucasV 1 1 6 = 2 := by
    rw [show (6:ℕ) = 4 + 2 from rfl, lucasV_succ_succ, show (4:ℕ) + 1 = 5 from rfl, e5, e4]; ring
  have e7 : lucasV 1 1 7 = 1 := by
    rw [show (7:ℕ) = 5 + 2 from rfl, lucasV_succ_succ, show (5:ℕ) + 1 = 6 from rfl, e6, e5]; ring
  exact ⟨e2, e3, e4, e5, e6, e7⟩

theorem lucasV_one_one_period (k : ℕ) : lucasV 1 1 (k + 6) = lucasV 1 1 k := by
  induction k using Nat.twoStepInduction with
  | zero => simpa [lucasV_zero] using vals.2.2.2.2.1
  | one => simpa [lucasV_one] using vals.2.2.2.2.2
  | more k ih1 ih2 =>
      rw [show k + 2 + 6 = (k + 6) + 2 from by omega, lucasV_succ_succ 1 1 (k + 6),
        lucasV_succ_succ 1 1 k, show k + 6 + 1 = (k + 1) + 6 from by omega, ih2, ih1]

theorem lucasV_one_one_mod (q r : ℕ) : lucasV 1 1 (6 * q + r) = lucasV 1 1 r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 6 * (q + 1) + r = (6 * q + r) + 6 from by ring, lucasV_one_one_period, ih]

/-- `V_c(1, 1) = 1` for every prime `c ≥ 5` (the sequence has period 6 and `c ≡ ±1 (mod 6)`). -/
theorem lucasV_one_one_prime {c : ℕ} (hc : c.Prime) (hc5 : 5 ≤ c) : lucasV 1 1 c = 1 := by
  have h2 : c % 2 ≠ 0 := by
    intro h
    have := (hc.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h)); omega
  have h3 : c % 3 ≠ 0 := by
    intro h
    have := (hc.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)); omega
  have hr : c % 6 = 1 ∨ c % 6 = 5 := by omega
  have hd : c = 6 * (c / 6) + c % 6 := by omega
  rw [hd, lucasV_one_one_mod]
  rcases hr with h | h <;> rw [h]
  · exact lucasV_one 1 1
  · exact vals.2.2.2.1


/-- `V_c(τ, 1) = τ` for `τ = ±1` and every prime `c ≥ 5`. -/
theorem lucasV_tau_one_prime {c : ℕ} (hc : c.Prime) (hc5 : 5 ≤ c) {τ : ℤ}
    (hτ : τ = 1 ∨ τ = -1) : lucasV τ 1 c = τ := by
  have hodd : Odd c := hc.odd_of_ne_two (by omega)
  rcases hτ with rfl | rfl
  · exact lucasV_one_one_prime hc hc5
  · rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, lucasV_neg', lucasV_one_one_prime hc hc5,
      hodd.neg_one_pow]
    ring

/-- `V_7(x, 1)`, written out. -/
theorem lucasV_seven (x : ℤ) : lucasV x 1 7 = x ^ 7 - 7 * x ^ 5 + 14 * x ^ 3 - 7 * x := by
  have e2 : lucasV x 1 2 = x ^ 2 - 2 := by
    rw [show (2:ℕ) = 0 + 2 from rfl, lucasV_succ_succ, lucasV_one, lucasV_zero]; ring
  have e3 : lucasV x 1 3 = x ^ 3 - 3 * x := by
    rw [show (3:ℕ) = 1 + 2 from rfl, lucasV_succ_succ, show (1:ℕ) + 1 = 2 from rfl, e2,
      lucasV_one]; ring
  have e4 : lucasV x 1 4 = x ^ 4 - 4 * x ^ 2 + 2 := by
    rw [show (4:ℕ) = 2 + 2 from rfl, lucasV_succ_succ, show (2:ℕ) + 1 = 3 from rfl, e3, e2]; ring
  have e5 : lucasV x 1 5 = x ^ 5 - 5 * x ^ 3 + 5 * x := by
    rw [show (5:ℕ) = 3 + 2 from rfl, lucasV_succ_succ, show (3:ℕ) + 1 = 4 from rfl, e4, e3]; ring
  have e6 : lucasV x 1 6 = x ^ 6 - 6 * x ^ 4 + 9 * x ^ 2 - 2 := by
    rw [show (6:ℕ) = 4 + 2 from rfl, lucasV_succ_succ, show (4:ℕ) + 1 = 5 from rfl, e5, e4]; ring
  rw [show (7:ℕ) = 5 + 2 from rfl, lucasV_succ_succ, show (5:ℕ) + 1 = 6 from rfl, e6, e5]; ring

/-- `U_5(τ, 1) = −1` and `U_6(τ, 1) = 0` for `τ = ±1`. -/
theorem lucasU_five_six {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    lucasU τ 1 5 = -1 ∧ lucasU τ 1 6 = 0 := by
  have e2 : lucasU τ 1 2 = τ := by
    rw [show (2:ℕ) = 0 + 2 from rfl, lucasU_succ_succ, lucasU_one, lucasU_zero]; ring
  have e3 : lucasU τ 1 3 = τ ^ 2 - 1 := by
    rw [show (3:ℕ) = 1 + 2 from rfl, lucasU_succ_succ, show (1:ℕ) + 1 = 2 from rfl, e2,
      lucasU_one]; ring
  have e4 : lucasU τ 1 4 = τ ^ 3 - 2 * τ := by
    rw [show (4:ℕ) = 2 + 2 from rfl, lucasU_succ_succ, show (2:ℕ) + 1 = 3 from rfl, e3, e2]; ring
  have e5 : lucasU τ 1 5 = τ ^ 4 - 3 * τ ^ 2 + 1 := by
    rw [show (5:ℕ) = 3 + 2 from rfl, lucasU_succ_succ, show (3:ℕ) + 1 = 4 from rfl, e4, e3]; ring
  have e6 : lucasU τ 1 6 = τ ^ 5 - 4 * τ ^ 3 + 3 * τ := by
    rw [show (6:ℕ) = 4 + 2 from rfl, lucasU_succ_succ, show (4:ℕ) + 1 = 5 from rfl, e5, e4]; ring
  rcases hτ with rfl | rfl <;> rw [e5, e6] <;> norm_num

/-- `C^6 ≡ 1 (mod c)` in the `Φ₃`/`Φ₆` class. -/
theorem smulDvd_pow_six_sub_one (C : Matrix (Fin 2) (Fin 2) ℤ) {c : ℕ}
    (hdet : (c : ℤ) ∣ C.det - 1) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) (htr : (c : ℤ) ∣ C.trace - τ) :
    SmulDvd ((c : ℤ) ^ 1) (C ^ 6 - 1) := by
  obtain ⟨hu5, hu6⟩ := lucasU_five_six hτ
  have hU6 : (c : ℤ) ∣ lucasU C.trace C.det 6 := by
    have := dvd_lucasU_sub htr hdet 6
    rw [hu6] at this
    simpa using this
  have hU5 : (c : ℤ) ∣ C.det * lucasU C.trace C.det 5 + 1 := by
    have h1 : (c : ℤ) ∣ lucasU C.trace C.det 5 - (-1) := by
      have := dvd_lucasU_sub htr hdet 5
      rwa [hu5] at this
    have h2 : C.det * lucasU C.trace C.det 5 + 1
        = (C.det - 1) * lucasU C.trace C.det 5 + (lucasU C.trace C.det 5 - (-1)) := by
      ring
    rw [h2]
    exact dvd_add (hdet.mul_right _) h1
  have hexp : C ^ 6 - 1 = lucasU C.trace C.det 6 • C
      - (C.det * lucasU C.trace C.det 5 + 1) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    have h := pow_eq_lucasU_smul C 5
    rw [show (5 : ℕ) + 1 = 6 from rfl] at h
    rw [h, add_smul, one_smul]
    abel
  refine SmulDvd.of_entries _ _ (fun i j => ?_)
  rw [hexp]
  simp only [pow_one, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_sub (hU6.mul_right _) (hU5.mul_right _)


/-- The exact-composition congruence for traces at an odd prime with `det ≡ ε (mod c)`. -/
theorem trace_pow_prime_congr (C : Matrix (Fin 2) (Fin 2) ℤ) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hdet : (c : ℤ) ∣ C.det - ε) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ (C ^ (c ^ (n + 1))).trace - lucasV (C ^ (c ^ n)).trace ε c := by
  have hcomp : (C ^ (c ^ (n + 1))).trace
      = lucasV (C ^ (c ^ n)).trace ((C ^ (c ^ n)).det) c := by
    rw [show c ^ (n + 1) = c ^ n * c from by ring, pow_mul]
    exact trace_pow_eq_lucasV _ _
  rw [hcomp, Matrix.det_pow]
  exact dvd_lucasV_sub_q (pow_pow_dvd_sub hc hc2 hε hdet n) c


/-! ### Frobenius and growth for a general determinant -/

theorem abs_add_ge {a b : ℤ} : |a| - |b| ≤ |a + b| := by
  have h := abs_sub_abs_le_abs_sub a (-b)
  rw [abs_neg, sub_neg_eq_add] at h
  linarith


/-- `2 x^c ≡ 2 V_c(x, q) (mod c)` for every `q`: the binomial theorem for the two commuting
matrices `!![x, −q; 1, 0]` and `!![0, q; −1, x]`, both of trace `x` and determinant `q`. -/
theorem dvd_two_mul_lucasV_sub_pow_q {c : ℕ} (hc : c.Prime) (x q : ℤ) :
    (c : ℤ) ∣ 2 * x ^ c - 2 * lucasV x q c := by
  set B : Matrix (Fin 2) (Fin 2) ℤ := !![x, -q; 1, 0] with hB
  set B' : Matrix (Fin 2) (Fin 2) ℤ := !![0, q; -1, x] with hB'
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
  have hdetB : B.det = q := by rw [hB]; simp [Matrix.det_fin_two]
  have htrB' : B'.trace = x := by rw [hB']; simp [Matrix.trace_fin_two]
  have hdetB' : B'.det = q := by rw [hB']; simp [Matrix.det_fin_two]
  have hends : ∀ k : ℕ, (B ^ k).trace = lucasV x q k ∧ (B' ^ k).trace = lucasV x q k := by
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
  have hg0 : g 0 = lucasV x q c := by
    simp only [hg, pow_zero, Matrix.one_mul, Nat.choose_zero_right, Nat.cast_one,
      Nat.sub_zero, one_mul]
    exact (hends c).2
  have hgc : g c = lucasV x q c := by
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
  have hfin : 2 * x ^ c - 2 * lucasV x q c = ∑ i ∈ Finset.range d, g (i + 1) := by
    linarith [hsumtr]
  rw [hfin]
  exact hmid

/-- **Frobenius for every `q`.**  `V_c(x, q) ≡ x (mod c)` for a prime `c ≠ 2`. -/
theorem lucasV_prime_mod_q {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (x q : ℤ) :
    (c : ℤ) ∣ lucasV x q c - x := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hfermat : (c : ℤ) ∣ x ^ c - x := by
    have : ((x ^ c - x : ℤ) : ZMod c) = 0 := by
      push_cast
      rw [ZMod.pow_card]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have h2 := dvd_two_mul_lucasV_sub_pow_q hc x q
  have hcomb : (c : ℤ) ∣ 2 * (x - lucasV x q c) := by
    have e : 2 * (x - lucasV x q c)
        = (2 * x ^ c - 2 * lucasV x q c) - 2 * (x ^ c - x) := by ring
    rw [e]
    exact dvd_sub h2 (hfermat.mul_left 2)
  have hcZ : Prime (c : ℤ) := Nat.prime_iff_prime_int.1 hc
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with h | h
    · interval_cases c <;> simp_all
    · exact h
  rcases (hcZ.dvd_mul.1 hcomb) with hd | hd
  · have h1 := Int.le_of_dvd (by norm_num) hd
    have : (3 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc3
    omega
  · have : (c : ℤ) ∣ -(lucasV x q c - x) := by simpa [neg_sub] using hd
    exact (dvd_neg.1 this)

/-! ### Growth for `q = 1` -/

theorem lucasV_one_pos_lt {x : ℤ} (hx : 3 ≤ x) (k : ℕ) :
    1 ≤ lucasV x 1 (k + 1) ∧ lucasV x 1 (k + 1) < lucasV x 1 (k + 2) := by
  induction k with
  | zero =>
      have e1 : lucasV x 1 (0 + 1) = x := by norm_num [lucasV_one]
      have e2 : lucasV x 1 (0 + 2) = x ^ 2 - 2 := by
        rw [show (0:ℕ) + 2 = 0 + 2 from rfl, lucasV_succ_succ, lucasV_one, lucasV_zero]; ring
      rw [e1, e2]
      exact ⟨by omega, by nlinarith⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [lucasV_succ_succ] at h2 ⊢
      constructor
      · linarith
      · nlinarith

theorem lucasV_one_strictMono {x : ℤ} (hx : 3 ≤ x) {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    lucasV x 1 j < lucasV x 1 k := by
  induction k with
  | zero => omega
  | succ k ih =>
      obtain ⟨u, rfl⟩ : ∃ u, k = u + 1 := ⟨k - 1, by omega⟩
      have hstep := (lucasV_one_pos_lt hx u).2
      rcases Nat.lt_or_ge j (u + 1) with hlt | hge
      · exact lt_trans (ih hlt) hstep
      · have : j = u + 1 := by omega
        rw [this]; exact hstep

/-- For odd `c ≥ 3` and `|x| ≥ 3`, `V_c(x, 1)` is far from `x`. -/
theorem lucasV_one_growth {c : ℕ} (hc : Odd c) (hc3 : 3 ≤ c) {x : ℤ} (hx : 3 ≤ |x|) :
    |x| + 3 ≤ |lucasV x 1 c| := by
  have key : ∀ y : ℤ, 3 ≤ y → y + 3 ≤ lucasV y 1 c := by
    intro y hy
    have h3 : lucasV y 1 3 ≤ lucasV y 1 c := by
      rcases eq_or_lt_of_le hc3 with heq | hlt
      · rw [heq]
      · exact (lucasV_one_strictMono hy (by omega) hlt).le
    have e3 : lucasV y 1 3 = y ^ 3 - 3 * y := by
      rw [show (3:ℕ) = 1 + 2 from rfl, lucasV_succ_succ, show (1:ℕ) + 1 = 2 from rfl,
        show lucasV y 1 2 = y ^ 2 - 2 from by
          rw [show (2:ℕ) = 0 + 2 from rfl, lucasV_succ_succ, lucasV_one, lucasV_zero]; ring,
        lucasV_one]
      ring
    rw [e3] at h3
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ y - 3) (by nlinarith : (0:ℤ) ≤ y ^ 2 + 3 * y + 5)]
  rcases abs_cases x with ⟨he, hpos⟩ | ⟨he, hneg⟩
  · have hy : (3 : ℤ) ≤ x := by omega
    have := key x hy
    rw [abs_of_nonneg (by omega : (0:ℤ) ≤ lucasV x 1 c), he]
    omega
  · have hy : (3 : ℤ) ≤ -x := by omega
    have hk := key (-x) hy
    have hneg' : lucasV x 1 c = -lucasV (-x) 1 c := by
      have h := lucasV_neg' (-x) 1 c
      rw [neg_neg] at h
      rw [h, hc.neg_one_pow]
      ring
    rw [hneg', abs_neg, abs_of_nonneg (by omega : (0:ℤ) ≤ lucasV (-x) 1 c), he]
    omega


/-- **Theorem B.**  2×2 traces at odd primes: composite infinitely often for every shift, outside
the `Φ₆`/`Φ₃` classes. -/
theorem trace_prime_pow_add_not_prime (C : Matrix (Fin 2) (Fin 2) ℤ) {c : ℕ} (hc : c.Prime)
    (hc2 : c ≠ 2) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hdet : (c : ℤ) ∣ C.det - ε)
    (htr : ¬ (c : ℤ) ∣ C.trace) (hdisc : ¬ (c : ℤ) ∣ C.trace ^ 2 - 4 * C.det)
    (hexc : ¬ (ε = 1 ∧ ((c : ℤ) ∣ C.trace - 1 ∨ (c : ℤ) ∣ C.trace + 1)))
    (hgrow : Tendsto (fun n : ℕ => |(C ^ (c ^ n)).trace|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((C ^ (c ^ n)).trace + h) := by
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with hlt | hge
    · interval_cases c <;> simp_all
    · exact hge
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hcZ : (3 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc3
  obtain ⟨t, htdef⟩ : ∃ t : ℕ → ℤ, t = fun n => (C ^ (c ^ n)).trace := ⟨_, rfl⟩
  have hteq : ∀ n, (C ^ (c ^ n)).trace = t n := by intro n; rw [htdef]
  simp only [hteq] at hgrow ⊢
  -- Step 0: `t n ≡ tr C (mod c)`, so `c ∤ t n` and `c ∤ t n² − 4ε`
  have hmod : ∀ n, (c : ℤ) ∣ t n - C.trace := by
    intro n
    induction n with
    | zero => rw [← hteq]; simp
    | succ n ih =>
        have h1 : (c : ℤ) ∣ t (n + 1) - lucasV (t n) ε c := by
          have hh := trace_pow_prime_congr C hc hc2 hε hdet n
          rw [hteq, hteq] at hh
          exact dvd_trans (dvd_pow_self _ (by omega)) hh
        have h2 : (c : ℤ) ∣ lucasV (t n) ε c - t n := lucasV_prime_mod_q hc hc2 _ _
        have e : t (n + 1) - C.trace
            = (t (n + 1) - lucasV (t n) ε c) + (lucasV (t n) ε c - t n) + (t n - C.trace) := by
          ring
        rw [e]
        exact dvd_add (dvd_add h1 h2) ih
  have hnd : ∀ n, ¬ (c : ℤ) ∣ t n := by
    intro n hd
    refine htr ?_
    have := dvd_sub hd (hmod n)
    simpa using this
  have hdet0 : C.det ≠ 0 := by
    intro h0
    have h1 : (c : ℤ) ∣ ε := by
      have := hdet
      rw [h0] at this
      simpa using (dvd_neg.1 (by simpa using this))
    rcases hε with rfl | rfl
    · have := Int.le_of_dvd one_pos h1; omega
    · have : (c : ℤ) ∣ (1 : ℤ) := (dvd_neg.1 h1)
      have := Int.le_of_dvd one_pos this; omega
  -- growth, in the form we use
  have hgr : ∀ B : ℤ, ∃ N : ℕ, ∀ n ≥ N, B ≤ |t n| := by
    intro B
    exact eventually_atTop.1 (tendsto_atTop.1 hgrow B)
  have hlow : ∀ n : ℕ, |t n| - |h| ≤ |t n + h| := fun n => abs_add_ge
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  obtain ⟨N₁, hN₁⟩ := hgr (|h| + |C.det| + (c : ℤ) + 5)
  set Bnd : ℤ := |lucasV (1 - h) ε c| + |lucasV (-1 - h) ε c| + |h| + 3 with hBnd
  set Bn : ℕ := Bnd.toNat with hBn
  set N : ℕ := max n₀ N₁ with hNdef
  have hprime : ∀ n ≥ N, Prime (t n + h) := fun n hn => hn₀ n (by omega)
  have hTbig : ∀ n ≥ N, |C.det| + (c : ℤ) + 5 ≤ |t n + h| := by
    intro n hn
    have h1 := hN₁ n (by omega)
    have h2 := hlow n
    linarith
  have hpabs : ∀ n : ℕ, ((t n + h).natAbs : ℤ) = |t n + h| := fun n => (Int.abs_eq_natAbs _).symm
  have hpn : ∀ n ≥ N, (t n + h).natAbs.Prime := fun n hn =>
    Int.prime_iff_natAbs_prime.1 (hprime n hn)
  have hpc : ∀ n ≥ N, (t n + h).natAbs ≠ c := by
    intro n hn he
    have h1 := hTbig n hn
    have h2 := hpabs n
    rw [he] at h2
    have := abs_nonneg C.det
    omega
  have hpdet : ∀ n ≥ N, ¬ ((t n + h).natAbs : ℤ) ∣ C.det := by
    intro n hn hd
    have h1 : ((t n + h).natAbs : ℤ) ≤ |C.det| := Int.le_of_dvd (abs_pos.2 hdet0) ((dvd_abs _ _).2 hd)
    have h2 := hTbig n hn
    rw [hpabs n] at h1
    omega
  -- the return step
  have hstep : ∀ n ≥ N, padicValNat c (glCard 2 (t n + h).natAbs) ≤ n →
      ∃ j, 1 ≤ j ∧ (t (n + j) + h).natAbs = (t n + h).natAbs := by
    intro n hn hv
    obtain ⟨j, hj1, hj⟩ :=
      SharedConjecture.exists_trace_pow_congr C (hpn n hn) hc (hpdet n hn) hv
    rw [hteq, hteq] at hj
    have hdvd : ((t n + h).natAbs : ℤ) ∣ t (n + j) + h := by
      have h1 : ((t n + h).natAbs : ℤ) ∣ t n + h := Int.natAbs_dvd.2 dvd_rfl
      have h2 : t (n + j) + h = (t (n + j) - t n) + (t n + h) := by ring
      rw [h2]
      exact dvd_add hj h1
    have hq := hpn (n + j) (by omega)
    have hdq : (t n + h).natAbs ∣ (t (n + j) + h).natAbs :=
      Int.natAbs_dvd_natAbs.2 (Int.natAbs_dvd.1 hdvd)
    rcases hq.eq_one_or_self_of_dvd _ hdq with hh | hh
    · exact absurd hh (hpn n hn).ne_one
    · exact ⟨j, hj1, hh.symm⟩
  have hstep2 : ∀ n ≥ N, n < padicValNat c (glCard 2 (t n + h).natAbs) := by
    intro n hn
    by_contra hle
    push_neg at hle
    have chain : ∀ k : ℕ, ∃ n' : ℕ, n + k ≤ n' ∧ (t n' + h).natAbs = (t n + h).natAbs ∧
        padicValNat c (glCard 2 (t n' + h).natAbs) ≤ n' := by
      intro k
      induction k with
      | zero => exact ⟨n, by omega, rfl, hle⟩
      | succ k ih =>
          obtain ⟨n', hn'1, hn'2, hn'3⟩ := ih
          obtain ⟨j, hj1, hj⟩ := hstep n' (by omega) hn'3
          refine ⟨n' + j, by omega, ?_, ?_⟩
          · rw [hj]; exact hn'2
          · rw [hj]; omega
    obtain ⟨Nb, hNb⟩ := hgr (|t n + h| + |h| + 1)
    obtain ⟨n', hcc1, hcc2, _⟩ := chain (Nb + n)
    have h1 : |t n' + h| = |t n + h| := by
      rw [← hpabs n', ← hpabs n, hcc2]
    have h2 := hNb n' (by omega)
    have h3 := hlow n'
    linarith
  -- the filter's output
  have hstep3 : ∀ n ≥ N, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (c : ℤ) ^ (n / 2) ∣ t n + h - s := by
    intro n hn
    have hlt := hstep2 n hn
    obtain ⟨s0, hs0, hd⟩ : ∃ s0 : ℤ, (s0 = 1 ∨ s0 = -1) ∧
        (c : ℤ) ^ (n / 2) ∣ ((t n + h).natAbs : ℤ) - s0 := by
      rcases FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat hc hc2 (hpn n hn)
        (hpc n hn) hlt with hd | hd
      · exact ⟨1, Or.inl rfl, hd⟩
      · exact ⟨-1, Or.inr rfl, by simpa using hd⟩
    rcases Int.natAbs_eq (t n + h) with he | he
    · exact ⟨s0, hs0, by rw [he]; exact hd⟩
    · refine ⟨-s0, ?_, ?_⟩
      · rcases hs0 with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by norm_num)
      · have hrw : t n + h - -s0 = -(((t n + h).natAbs : ℤ) - s0) := by omega
        rw [hrw]
        exact dvd_neg.2 hd
  -- pick a large even index
  set n : ℕ := 2 * (Bn + N + 3) with hn
  set e : ℕ := Bn + N + 3 with he
  have hne : n / 2 = e := by omega
  have hnN : N ≤ n := by omega
  have hBndpos : 0 ≤ Bnd := by positivity
  have hBncast : ((Bn : ℕ) : ℤ) = Bnd := Int.toNat_of_nonneg hBndpos
  have hbnd : Bnd < (c : ℤ) ^ e := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ e ≤ c ^ e := Nat.pow_le_pow_left (by omega) e
    have h3 : Bn < c ^ e := by omega
    have h4 : ((Bn : ℕ) : ℤ) < ((c ^ e : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at h4
    linarith [hBncast]
  obtain ⟨s, hs, hsd⟩ := hstep3 n hnN
  obtain ⟨s', hs', hsd'⟩ := hstep3 (n + 1) (by omega)
  rw [hne] at hsd
  have hsd'' : (c : ℤ) ^ e ∣ t (n + 1) + h - s' := by
    refine dvd_trans (pow_dvd_pow _ ?_) hsd'
    omega
  set x : ℤ := s - h with hx
  set x' : ℤ := s' - h with hx'
  have hVx : (c : ℤ) ^ e ∣ t n - x := by
    have hrw : t n - x = t n + h - s := by rw [hx]; ring
    rw [hrw]; exact hsd
  have hVx' : (c : ℤ) ^ e ∣ t (n + 1) - x' := by
    have hrw : t (n + 1) - x' = t (n + 1) + h - s' := by rw [hx']; ring
    rw [hrw]; exact hsd''
  have hkey : (c : ℤ) ^ e ∣ lucasV x ε c - x' := by
    have hcong : (c : ℤ) ^ e ∣ t (n + 1) - lucasV (t n) ε c := by
      have hh := trace_pow_prime_congr C hc hc2 hε hdet n
      rw [hteq, hteq] at hh
      exact dvd_trans (pow_dvd_pow _ (by omega)) hh
    have h1 : (c : ℤ) ^ e ∣ lucasV (t n) ε c - lucasV x ε c := dvd_lucasV_sub hVx c
    have e2 : lucasV x ε c - x'
        = (t (n + 1) - x') - (t (n + 1) - lucasV (t n) ε c) - (lucasV (t n) ε c - lucasV x ε c) := by
      ring
    rw [e2]
    exact dvd_sub (dvd_sub hVx' hcong) h1
  -- the growth bound forces `lucasV x ε c = x'`
  have hxcases : x = 1 - h ∨ x = -1 - h := by
    rcases hs with hh | hh
    · exact Or.inl (by rw [hx, hh])
    · exact Or.inr (by rw [hx, hh])
  have hxx' : |x' - x| ≤ 2 := by
    have e : x' - x = s' - s := by rw [hx, hx']; ring
    rw [e]
    rcases hs with hh | hh <;> rcases hs' with hh' | hh' <;> rw [hh, hh'] <;> norm_num
  have hx'abs : |x'| ≤ |h| + 1 := by
    rcases hs' with hh | hh <;> rw [hx', hh] <;>
      rcases abs_cases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [abs_le] <;> omega
  have hfix : lucasV x ε c = x' := by
    by_contra hne0'
    have hne0 : lucasV x ε c - x' ≠ 0 := by intro hz; exact hne0' (by omega)
    have hLbound : |lucasV x ε c| ≤ |lucasV (1 - h) ε c| + |lucasV (-1 - h) ε c| := by
      rcases hxcases with hee | hee
      · rw [hee]; have := abs_nonneg (lucasV (-1 - h) ε c); omega
      · rw [hee]; have := abs_nonneg (lucasV (1 - h) ε c); omega
    have hle := Int.le_of_dvd (abs_pos.2 hne0) ((dvd_abs _ _).2 hkey)
    have hb : |lucasV x ε c - x'| ≤ |lucasV x ε c| + |x'| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    rw [hBnd] at hbnd
    linarith
  -- `x = 0` is impossible: it makes `c ∣ t n`
  have hx0 : x ≠ 0 := by
    intro hz
    refine hnd n ?_
    have h1 : (c : ℤ) ^ e ∣ t n := by rw [hz, sub_zero] at hVx; exact hVx
    exact dvd_trans (dvd_pow_self _ (by omega)) h1
  have hxsmall : |x'| ≤ |x| + 2 := by
    have := abs_sub_abs_le_abs_sub x' x
    omega
  rcases hε with rfl | rfl
  · -- `ε = 1`
    have hxabs : ¬ (3 ≤ |x|) := by
      intro hge
      have hgr3 := lucasV_one_growth hcodd hc3 hge
      rw [hfix] at hgr3
      omega
    -- so `|x| ≤ 2`, and `x ≠ 0`
    have hmodx : (c : ℤ) ∣ C.trace - x := by
      have h1 : (c : ℤ) ∣ t n - x := dvd_trans (dvd_pow_self _ (by omega)) hVx
      have e : C.trace - x = (t n - x) - (t n - C.trace) := by ring
      rw [e]
      exact dvd_sub h1 (hmod n)
    have h1x : 0 < |x| := abs_pos.2 hx0
    have habs2 : |x| = 1 ∨ |x| = 2 := by omega
    rcases habs2 with h1 | h2
    · -- `x = ±1`: the excluded `Φ₃`/`Φ₆` class
      refine hexc ⟨rfl, ?_⟩
      rcases abs_cases x with ⟨e1, _⟩ | ⟨e1, _⟩
      · left
        have : x = 1 := by omega
        rw [this] at hmodx; exact hmodx
      · right
        have hxv : x = -1 := by omega
        rw [hxv] at hmodx
        have : C.trace + 1 = C.trace - -1 := by ring
        rw [this]; exact hmodx
    · -- `x = ±2`: `c ∣ disc`
      refine hdisc ?_
      have hd4 : (c : ℤ) ∣ C.trace ^ 2 - 4 := by
        have hsq : C.trace ^ 2 - x ^ 2 = (C.trace - x) * (C.trace + x) := by ring
        have h1 : (c : ℤ) ∣ C.trace ^ 2 - x ^ 2 := by
          rw [hsq]; exact hmodx.mul_right _
        have hx2 : x ^ 2 = 4 := by
          have hsa := sq_abs x
          rw [h2] at hsa
          norm_num at hsa
          linarith
        rwa [hx2] at h1
      have e : C.trace ^ 2 - 4 * C.det = (C.trace ^ 2 - 4) - 4 * (C.det - 1) := by ring
      rw [e]
      exact dvd_sub hd4 (hdet.mul_left 4)
  · -- `ε = −1`
    have hgr3 := lucasV_neg_one_growth hcodd hc3 hx0
    rw [hfix] at hgr3
    omega


/-- **The exceptional classes really are survivors**: the traces converge to `τ = ±1`
`c`-adically at rate `c^(n+1)`. -/
theorem trace_phi_survivor (C : Matrix (Fin 2) (Fin 2) ℤ) {c : ℕ} (hc : c.Prime) (hc5 : 5 ≤ c)
    (hdet : (c : ℤ) ∣ C.det - 1) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) (htr : (c : ℤ) ∣ C.trace - τ)
    (n : ℕ) : (c : ℤ) ^ (n + 1) ∣ (C ^ (c ^ n)).trace - τ := by
  have hc2 : c ≠ 2 := by omega
  have hcZ : Prime (c : ℤ) := Nat.prime_iff_prime_int.1 hc
  have hc1 : (1 : ℤ) < (c : ℤ) := by exact_mod_cast hc.one_lt
  have hτ2 : τ ^ 2 = 1 := by rcases hτ with rfl | rfl <;> norm_num
  -- Step A: the reduction mod `c` holds at every index.
  have hmod : ∀ m : ℕ, (c : ℤ) ∣ (C ^ c ^ m).trace - τ := by
    intro m
    induction m with
    | zero => simpa using htr
    | succ m ih =>
        have h1 : (c : ℤ) ∣ (C ^ c ^ (m + 1)).trace - lucasV (C ^ c ^ m).trace 1 c :=
          dvd_trans (dvd_pow_self _ (by omega))
            (trace_pow_prime_congr C hc hc2 (Or.inl rfl) hdet m)
        have h2 : (c : ℤ) ∣ lucasV (C ^ c ^ m).trace 1 c - τ := by
          have h3 := dvd_lucasV_sub' (m := (c : ℤ)) (a := (1 : ℤ)) (b := (1 : ℤ)) ih (by norm_num) c
          rwa [lucasV_tau_one_prime hc hc5 hτ] at h3
        have e : (C ^ c ^ (m + 1)).trace - τ
            = ((C ^ c ^ (m + 1)).trace - lucasV (C ^ c ^ m).trace 1 c)
              + (lucasV (C ^ c ^ m).trace 1 c - τ) := by ring
        rw [e]
        exact dvd_add h1 h2
  -- Step B: `D^6 ≡ 1 (mod c^(n+1))` by matrix lifting-the-exponent.
  set D : Matrix (Fin 2) (Fin 2) ℤ := C ^ c ^ n with hD
  have hD6 : SmulDvd ((c : ℤ) ^ (n + 1)) (D ^ 6 - 1) := by
    have he : D ^ 6 = (C ^ 6) ^ c ^ n := by
      rw [hD, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [he]
    exact SmulDvd.pow_prime_pow (smulDvd_pow_six_sub_one C hdet hτ htr) n
  have h7 : SmulDvd ((c : ℤ) ^ (n + 1)) (D ^ 7 - D) := by
    have he : D ^ 7 - D = (D ^ 6 - 1) * D := by
      rw [Matrix.sub_mul, Matrix.one_mul, ← pow_succ]
    rw [he]
    exact hD6.mul_right D
  have htr7 : (c : ℤ) ^ (n + 1) ∣ (D ^ 7).trace - D.trace := by
    have hh := dvd_trace_of_entries (fun i j => h7.entry i j)
    rwa [Matrix.trace_sub] at hh
  have hdetD : (c : ℤ) ^ (n + 1) ∣ D.det - 1 := by
    rw [hD, Matrix.det_pow]
    exact pow_pow_dvd_sub hc hc2 (Or.inl rfl) hdet n
  -- Step C: transfer to the scalar identity `V_7(s, 1) − s = (s − τ) · W`.
  have hV : (c : ℤ) ^ (n + 1) ∣ lucasV D.trace 1 7 - D.trace := by
    have e1 : (D ^ 7).trace = lucasV D.trace D.det 7 := trace_pow_eq_lucasV D 7
    have e2 : (c : ℤ) ^ (n + 1) ∣ lucasV D.trace D.det 7 - lucasV D.trace 1 7 :=
      dvd_lucasV_sub' (by simp) hdetD 7
    have e3 : lucasV D.trace 1 7 - D.trace
        = ((D ^ 7).trace - D.trace) - (lucasV D.trace D.det 7 - lucasV D.trace 1 7) := by
      rw [e1]; ring
    rw [e3]
    exact dvd_sub htr7 e2
  set s : ℤ := D.trace with hs
  have hsτ : (c : ℤ) ∣ s - τ := hmod n
  have hsq : (c : ℤ) ∣ s ^ 2 - 1 := by
    have e : s ^ 2 - 1 = (s - τ) * (s + τ) + (τ ^ 2 - 1) := by ring
    rw [e, hτ2]
    simpa using hsτ.mul_right (s + τ)
  have hfac : lucasV s 1 7 - s = (s - τ) * ((s + τ) * s * (s ^ 2 - 2) * (s ^ 2 - 4)) := by
    rw [lucasV_seven]
    rcases hτ with rfl | rfl <;> ring
  have hW : ¬ (c : ℤ) ∣ (s + τ) * s * (s ^ 2 - 2) * (s ^ 2 - 4) := by
    intro hcon
    have habs : ∀ {k : ℤ}, (c : ℤ) ∣ k → k ≠ 0 → (c : ℤ) ≤ |k| := by
      intro k hk hk0
      exact Int.le_of_dvd (abs_pos.2 hk0) ((dvd_abs _ _).2 hk)
    rcases hcZ.dvd_mul.1 hcon with h | h4
    · rcases hcZ.dvd_mul.1 h with h | h2
      · rcases hcZ.dvd_mul.1 h with h | h1
        · -- `c ∣ s + τ` and `c ∣ s − τ` force `c ∣ 2τ`
          have h2τ : (c : ℤ) ∣ 2 * τ := by
            have e : 2 * τ = (s + τ) - (s - τ) := by ring
            rw [e]; exact dvd_sub h hsτ
          have := habs h2τ (by rcases hτ with rfl | rfl <;> norm_num)
          rcases hτ with rfl | rfl <;> simp at this <;> omega
        · -- `c ∣ s` and `c ∣ s − τ` force `c ∣ τ`
          have hτd : (c : ℤ) ∣ τ := by
            have e : τ = s - (s - τ) := by ring
            rw [e]; exact dvd_sub h1 hsτ
          have := habs hτd (by rcases hτ with rfl | rfl <;> norm_num)
          rcases hτ with rfl | rfl <;> simp at this <;> omega
      · -- `c ∣ s² − 2` with `c ∣ s² − 1` forces `c ∣ 1`
        have : (c : ℤ) ∣ (1 : ℤ) := by
          have e : (1 : ℤ) = (s ^ 2 - 1) - (s ^ 2 - 2) := by ring
          rw [e]; exact dvd_sub hsq h2
        have := Int.le_of_dvd one_pos this
        omega
    · -- `c ∣ s² − 4` with `c ∣ s² − 1` forces `c ∣ 3`
      have h3 : (c : ℤ) ∣ (3 : ℤ) := by
        have e : (3 : ℤ) = (s ^ 2 - 1) - (s ^ 2 - 4) := by ring
        rw [e]; exact dvd_sub hsq h4
      have := Int.le_of_dvd (by norm_num) h3
      have h5 : (5 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc5
      omega
  rw [hfac] at hV
  exact hcZ.pow_dvd_of_dvd_mul_right (n + 1) hW hV

end LeanFormalizations.Mills.TraceClassification

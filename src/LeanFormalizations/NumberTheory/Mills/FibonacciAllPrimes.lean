/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasPrimePow

/-!
# Phase 37: `F(c^n) + h` is composite i.o. for EVERY prime `c` and every `h`

Phases 32 (`c = 2`) and 34 (inert `c`, and `c = 5`) leave the split primes `c ≡ ±1 (mod 5)`
(Maze row).  Phase 35's exact-composition idea closes them: no non-integrality proof needed.

## Route (odd `c ≠ 5`; this also re-covers the inert primes, which is fine)
1. `fibOddPoly x j`: `Φ_0 = x`, `Φ_1 = 5x³ − 3x`, `Φ_(j+2) = (5x² − 2) Φ_(j+1) − Φ_j`.
   `fib_odd_mul`: for odd `N`, `F((2j+1) N) = Φ_j(F N)`.  Route: `F(a + 2N) + F(a − 2N) =
   F(a) L(2N)` and `L(2N) = 5F(N)² − 2` for odd `N`, together with `F(−N) = F(N)` for odd `N`
   (handle `j = 0, 1` directly and step by two).  Checked numerically for `j ≤ 5`, `N ≤ 11`.
2. `fibOddPoly_far`: for `x ≠ 0` and `j ≥ 1`, `Φ_j(x) − x ∉ {0, 2, −2}`.  (`|Φ_1| ≥ 2|x|`
   since `5x² − 3 ≥ 2`, the sequence grows in absolute value for `t = 5x² − 2 ≥ 3`; the only
   close call is `x = ±1 ↦ ±F(2j+1)`, where `F(3) = 2` gives difference `±1`.)
3. `not_dvd_fib_prime_pow`: for a prime `c ≠ 5`, `c ∤ F(c^n)`.  Route: `F(c)^2 ≡ 1 (mod c)`
   (binomial formula `2^(c−1) F(c) ≡ 5^((c−1)/2) (mod c)` plus Fermat, or Cassini
   `F(c−1)F(c+1) = F(c)² − 1` with `Nat.fib_gcd`); then `gcd(F(c^n), F(c−1) F(c+1)) = 1`.
   `c = 2` is also fine (`F(2^n)` is odd, phase 32).
4. Main theorem for odd `c ≠ 5`.  Assume `p_n = F(c^n) + h` is prime for `n ≥ n₀`.  The filter
   (`exists_entry_pow_congr` + `pow_dvd_sub_or_add_of_lt_padicValNat`, as in phase 34) gives
   `F(c^n) ≡ x_n (mod c^(n/2))` with `x_n ∈ {1 − h, −1 − h}`.  With `c^(n+1) = c · c^n`,
   `c = 2j+1`, `c^n` odd: `x_(n+1) ≡ Φ_j(x_n)`; finite sets ⟹ equality for large `n`;
   step 2 ⟹ `x_n = 0`; then `c^(n/2) ∣ F(c^n)`, contradicting step 3.
5. `fib_prime_pow_add_not_prime_all`: combine with phase 32 (`c = 2`), phase 34
   (`fib_five_pow_add_not_prime`), and step 4.

Frozen: every statement and def below; statements of all earlier Mills phase files and
`Literature/`.  Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.FibonacciAllPrimes

open LeanFormalizations.Mills.ThreeAdic Filter
open LeanFormalizations.Mills.FibonacciPrimePow LeanFormalizations.Mills.LucasPrimePow

/-- `Φ_j` with `F((2j+1)N) = Φ_j(F N)` for odd `N`. -/
def fibOddPoly (x : ℤ) : ℕ → ℤ
  | 0 => x
  | 1 => 5 * x ^ 3 - 3 * x
  | j + 2 => (5 * x ^ 2 - 2) * fibOddPoly x (j + 1) - fibOddPoly x j

/-! ### Step 1: the composition identity `F((2j+1)N) = Φ_j(F N)` for odd `N` -/

/-- The normalized companion: `fibOddPoly x j = x * fibOddAux (5x²−2) j`. -/
def fibOddAux (t : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => t - 1
  | j + 2 => t * fibOddAux t (j + 1) - fibOddAux t j

theorem fibOddPoly_eq_mul (x : ℤ) (j : ℕ) :
    fibOddPoly x j = x * fibOddAux (5 * x ^ 2 - 2) j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [fibOddPoly, fibOddAux]
  | one => simp only [fibOddPoly, fibOddAux]; ring
  | more j ih1 ih2 =>
      simp only [fibOddPoly, fibOddAux, ih1, ih2]
      ring

/-- `fibM ^ M` has `F M` in position `(0,1)`. -/
theorem fibM_pow_apply (M : ℕ) : (fibM ^ M) 0 1 = (Nat.fib M : ℤ) := by
  simp [fibM_pow]

theorem one_apply_zero_one : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by simp

theorem fibM_pow_trace_sq (N : ℕ) (hN : Odd N) :
    (fibM ^ N).trace ^ 2 = 5 * (Nat.fib N : ℤ) ^ 2 - 4 := by
  have hc := cassini_int N
  rw [hN.neg_one_pow] at hc
  have ht : (fibM ^ N).trace
      = (Nat.fib (N + 1) : ℤ) + ((Nat.fib (N + 1) : ℤ) - (Nat.fib N : ℤ)) := by
    rw [fibM_pow]; simp [Matrix.trace_fin_two]
  rw [ht]
  nlinarith [hc]

theorem fibM_pow_det_odd {N : ℕ} (hN : Odd N) : (fibM ^ N).det = -1 := by
  rw [Matrix.det_pow, fibM_det, hN.neg_one_pow]

theorem fib_odd_mul (j : ℕ) {N : ℕ} (hN : Odd N) :
    (Nat.fib ((2 * j + 1) * N) : ℤ) = fibOddPoly (Nat.fib N) j := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, A = fibM ^ N := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = A.trace := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = 5 * (Nat.fib N : ℤ) ^ 2 - 2 := ⟨_, rfl⟩
  have hdet : A.det = -1 := by rw [hA]; exact fibM_pow_det_odd hN
  have hLsq : L ^ 2 = 5 * (Nat.fib N : ℤ) ^ 2 - 4 := by
    rw [hL, hA]; exact fibM_pow_trace_sq N hN
  have hentry : ∀ k : ℕ, (A ^ k) 0 1 = (Nat.fib (k * N) : ℤ) := by
    intro k
    rw [hA, ← pow_mul, mul_comm N k, fibM_pow_apply]
  have hA01 : A 0 1 = (Nat.fib N : ℤ) := by
    have := hentry 1
    rwa [pow_one, one_mul] at this
  -- Cayley–Hamilton for `A`
  have hA2 : A ^ 2 = L • A + 1 := by
    have h := sq_eq_trace_smul_sub_det A
    rw [hdet, ← hL] at h
    rw [h]
    simp
  -- `B = A²` has trace `T` and determinant `1`
  have hB : (A ^ 2).trace = T := by
    rw [hA2, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, ← hL, Matrix.trace_one, hT]
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    linear_combination hLsq
  have hBdet : (A ^ 2).det = 1 := by rw [Matrix.det_pow, hdet]; ring
  have hA4 : A ^ 4 = T • A ^ 2 - 1 := by
    have h := sq_eq_trace_smul_sub_det (A ^ 2)
    rw [hB, hBdet, ← pow_mul] at h
    simpa using h
  have hone : (A ^ 3) 0 1 = 5 * (Nat.fib N : ℤ) ^ 3 - 3 * Nat.fib N := by
    have h3 : A ^ 3 = (L ^ 2 + 1) • A + L • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      have e : A ^ 3 = A * A ^ 2 := by rw [← pow_succ']
      rw [e, hA2, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← pow_two, hA2,
        smul_add, smul_smul]
      module
    rw [h3]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hA01, one_apply_zero_one, hLsq]
    ring
  have key : ∀ k : ℕ, (A ^ (2 * k + 1)) 0 1 = fibOddPoly (Nat.fib N) k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simpa [fibOddPoly] using hA01
    | one => simpa [fibOddPoly] using hone
    | more k ih1 ih2 =>
        have hsplit : A ^ (2 * (k + 2) + 1) = A ^ (2 * k + 1) * A ^ 4 := by
          rw [← pow_add]; ring_nf
        have hmul : A ^ (2 * k + 1) * A ^ 2 = A ^ (2 * (k + 1) + 1) := by
          rw [← pow_add]; ring_nf
        rw [hsplit, hA4, Matrix.mul_sub, Matrix.mul_smul, hmul, Matrix.mul_one]
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        rw [ih1, ih2]
        simp only [fibOddPoly]
        rw [hT]
  have h := key j
  rw [hentry (2 * j + 1)] at h
  exact h

/-! ### Step 2: `Φ_j(x)` is far from `x` -/

theorem fibOddPoly_neg (x : ℤ) (j : ℕ) : fibOddPoly (-x) j = - fibOddPoly x j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [fibOddPoly]
  | one => simp only [fibOddPoly]; ring
  | more j ih1 ih2 => simp only [fibOddPoly, ih1, ih2]; ring

theorem fibOddAux_growth {t : ℤ} (ht : 3 ≤ t) (j : ℕ) :
    1 ≤ fibOddAux t j ∧ fibOddAux t j < fibOddAux t (j + 1) := by
  induction j with
  | zero =>
      refine ⟨by simp [fibOddAux], ?_⟩
      simp only [fibOddAux]
      omega
  | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨by omega, ?_⟩
      have he : fibOddAux t (j + 2) = t * fibOddAux t (j + 1) - fibOddAux t j := rfl
      rw [he]
      nlinarith

theorem fibOddAux_mono {t : ℤ} (ht : 3 ≤ t) {a b : ℕ} (hab : a ≤ b) :
    fibOddAux t a ≤ fibOddAux t b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans ih (le_of_lt (fibOddAux_growth ht n).2)

theorem fibOddPoly_far_pos {x : ℤ} (hx : 1 ≤ x) {j : ℕ} (hj : 1 ≤ j) :
    fibOddPoly x j - x = 1 ∨ 4 ≤ fibOddPoly x j - x := by
  have hxsq : 1 ≤ x ^ 2 := by nlinarith
  have ht : 3 ≤ 5 * x ^ 2 - 2 := by nlinarith
  have hd : fibOddPoly x j - x = x * (fibOddAux (5 * x ^ 2 - 2) j - 1) := by
    rw [fibOddPoly_eq_mul]; ring
  have h1v : fibOddAux (5 * x ^ 2 - 2) 1 = 5 * x ^ 2 - 2 - 1 := rfl
  have hA1 : 5 * x ^ 2 - 2 - 1 ≤ fibOddAux (5 * x ^ 2 - 2) j := by
    have h := fibOddAux_mono ht (a := 1) hj
    omega
  rcases eq_or_lt_of_le hx with hx1 | hx2
  · -- `x = 1`, so `t = 3`
    have hxe : x = 1 := hx1.symm
    subst hxe
    norm_num at hd h1v hA1 ⊢
    rcases eq_or_lt_of_le hj with hj1 | hj2
    · left
      have : fibOddAux (3 : ℤ) j = 2 := by rw [← hj1]; norm_num [fibOddAux]
      omega
    · right
      have h2v : fibOddAux (3 : ℤ) 2 = 5 := by norm_num [fibOddAux]
      have := fibOddAux_mono (t := (3 : ℤ)) (by norm_num) (a := 2) (b := j) (by omega)
      omega
  · -- `|x| ≥ 2`
    right
    have hx2' : 2 ≤ x := hx2
    have hxsq4 : 4 ≤ x ^ 2 := by nlinarith
    rw [hd]
    nlinarith

theorem fibOddPoly_far {x : ℤ} (hx : x ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    fibOddPoly x j - x ≠ 0 ∧ fibOddPoly x j - x ≠ 2 ∧ fibOddPoly x j - x ≠ -2 := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hy : 1 ≤ -x := by omega
    have h := fibOddPoly_far_pos hy hj
    rw [fibOddPoly_neg] at h
    omega
  · have h := fibOddPoly_far_pos (show 1 ≤ x by omega) hj
    omega

/-! ### Step 3: `c ∤ F(c^n)` for a prime `c ≠ 5` -/

/-- `L(m)² − 5F(m)² = 4(−1)^m`. -/
theorem lucas_sq_sub_fib_sq (m : ℕ) :
    (lucasL (m + 1)) ^ 2 - 5 * (Nat.fib (m + 1) : ℤ) ^ 2 = 4 * (-1) ^ (m + 1) := by
  have hL := lucasL_eq_fib m
  have hf : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := m))
  have hc := cassini_int m
  rw [hL, hf, pow_succ]
  linear_combination (-4 : ℤ) * hc

theorem not_dvd_fib_prime_pow {c : ℕ} (hc : c.Prime) (h5 : c ≠ 5) (n : ℕ) :
    ¬ (c : ℤ) ∣ Nat.fib (c ^ n) := by
  intro hdvd
  have hpos : 1 ≤ c ^ n := Nat.one_le_pow _ _ hc.pos
  obtain ⟨m, hm⟩ : ∃ m, c ^ n = m + 1 := ⟨c ^ n - 1, by omega⟩
  have hid : (lucasL (c ^ n)) ^ 2 - 5 * (Nat.fib (c ^ n) : ℤ) ^ 2
      = 4 * (-1) ^ (c ^ n) := by rw [hm]; exact lucas_sq_sub_fib_sq m
  have hL := lucas_prime_pow_mod hc n
  have hL2 : (c : ℤ) ∣ (lucasL (c ^ n)) ^ 2 - 1 := by
    have e : (lucasL (c ^ n)) ^ 2 - 1 = (lucasL (c ^ n) - 1) * (lucasL (c ^ n) + 1) := by ring
    rw [e]; exact hL.mul_right _
  have hF : (c : ℤ) ∣ 5 * (Nat.fib (c ^ n) : ℤ) ^ 2 := by
    rw [pow_two]; exact (hdvd.mul_right _).mul_left 5
  have hfin : (c : ℤ) ∣ 4 * (-1 : ℤ) ^ (c ^ n) - 1 := by
    have e : 4 * (-1 : ℤ) ^ (c ^ n) - 1
        = ((lucasL (c ^ n)) ^ 2 - 1) - 5 * (Nat.fib (c ^ n) : ℤ) ^ 2 := by
      rw [← hid]; ring
    rw [e]; exact dvd_sub hL2 hF
  rcases Nat.even_or_odd (c ^ n) with hev | hod
  · rw [hev.neg_one_pow] at hfin
    norm_num at hfin
    have hcd : c ∣ 3 := by exact_mod_cast hfin
    have hc3 : c = 3 := by
      rcases (Nat.prime_three.eq_one_or_self_of_dvd c hcd) with h | h
      · exact absurd h hc.one_lt.ne'
      · exact h
    subst hc3
    have : Odd (3 ^ n) := (by decide : Odd 3).pow
    exact (Nat.not_even_iff_odd.2 this) hev
  · rw [hod.neg_one_pow] at hfin
    norm_num at hfin
    have hcd : c ∣ 5 := by exact_mod_cast hfin
    rcases (Nat.prime_five.eq_one_or_self_of_dvd c hcd) with h | h
    · exact absurd h hc.one_lt.ne'
    · exact h5 h

/-- **`F(c^n) + h` is composite infinitely often, for every prime `c` and every integer `h`.** -/
theorem fib_prime_pow_add_not_prime_all {c : ℕ} (hc : c.Prime) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.FibonacciAllPrimes

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

/-! ### Step 4: the main theorem for an odd prime `c ≠ 5` -/

/-- `Φ_j` respects congruences: it is a polynomial with integer coefficients. -/
theorem dvd_fibOddPoly_sub {M a b : ℤ} (h : M ∣ a - b) (j : ℕ) :
    M ∣ fibOddPoly a j - fibOddPoly b j := by
  induction j using Nat.twoStepInduction with
  | zero => simpa [fibOddPoly] using h
  | one =>
      simp only [fibOddPoly]
      have e : 5 * a ^ 3 - 3 * a - (5 * b ^ 3 - 3 * b)
          = (a - b) * (5 * (a ^ 2 + a * b + b ^ 2) - 3) := by ring
      rw [e]
      exact h.mul_right _
  | more j ih1 ih2 =>
      simp only [fibOddPoly]
      have e : (5 * a ^ 2 - 2) * fibOddPoly a (j + 1) - fibOddPoly a j
            - ((5 * b ^ 2 - 2) * fibOddPoly b (j + 1) - fibOddPoly b j)
          = (a - b) * (5 * (a + b) * fibOddPoly b (j + 1))
            + (5 * a ^ 2 - 2) * (fibOddPoly a (j + 1) - fibOddPoly b (j + 1))
            - (fibOddPoly a j - fibOddPoly b j) := by ring
      rw [e]
      exact dvd_sub (dvd_add (h.mul_right _) (ih2.mul_left _)) ih1

/-- **The odd-prime case.** -/
theorem fib_prime_pow_add_not_prime_odd {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hc5 : c ≠ 5)
    (h : ℤ) : ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hcodd' : Odd c := hcodd
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    omega
  have hcle : 2 ≤ c := by omega
  obtain ⟨j, hj⟩ := hcodd
  have hj1 : 1 ≤ j := by omega
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  -- abbreviations
  set t : ℕ → ℤ := fun n => (Nat.fib (c ^ n) : ℤ) + h with htdef
  set H : ℕ := h.natAbs with hH
  -- the bound the two candidate residues need to beat
  set B : ℕ := (fibOddPoly (1 - h) j).natAbs + (fibOddPoly (-1 - h) j).natAbs + 2 * H + 8
    with hB
  set N : ℕ := max (max 5 n₀) (max (c + H + 5) (B + 5)) with hNdef
  have hN5 : 5 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNn₀ : n₀ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNc : c + H + 5 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNB : B + 5 ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hbig : ∀ n ≥ N, (c : ℤ) < t n := by
    intro n hn
    have hn5 : 5 ≤ n := le_trans hN5 hn
    have hgrow : (n : ℤ) ≤ (Nat.fib (c ^ n) : ℤ) := by
      exact_mod_cast le_fib_prime_pow hcle hn5
    have hlow : (c : ℤ) + (H : ℤ) + 5 ≤ (n : ℤ) := by
      have h1 : ((c + H + 5 : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNc
      have h2 : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      push_cast at h1
      omega
    have habs : -(H : ℤ) ≤ h := by omega
    simp only [htdef]
    omega
  have hprime : ∀ n ≥ N, Prime (t n) := fun n hn => hn₀ n (le_trans hNn₀ hn)
  have htmono : ∀ {m n : ℕ}, N ≤ m → m < n → t m < t n := by
    intro m n hm hmn
    have h1 := fib_prime_pow_lt hcle (show 1 ≤ m by omega) hmn
    have h2 : (Nat.fib (c ^ m) : ℤ) < (Nat.fib (c ^ n) : ℤ) := by exact_mod_cast h1
    simp only [htdef]
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
    obtain ⟨k, hk1, hk01⟩ := exists_fib_prime_pow_congr hp hc hv
    have hdvd : (p : ℤ) ∣ t (n + k) := by
      have h1 : (p : ℤ) ∣ t n := by rw [hpv]
      have h2 : t (n + k) - t n = (Nat.fib (c ^ (n + k)) : ℤ) - Nat.fib (c ^ n) := by
        simp only [htdef]; ring
      have h3 := dvd_add hk01 h1
      rw [← h2] at h3
      simpa using h3
    have hgt : t n < t (n + k) := htmono hn (by omega)
    have hq := hprime (n + k) (by omega)
    have hqpos : 0 < t (n + k) := by have := hbig n hn; have := hc.two_le; omega
    obtain ⟨q, hqv⟩ : ∃ q : ℕ, (q : ℤ) = t (n + k) := ⟨(t (n + k)).toNat, by omega⟩
    have hqnat : q.Prime := by
      rw [Int.prime_iff_natAbs_prime] at hq
      have hEq : (t (n + k)).natAbs = q := by omega
      rwa [hEq] at hq
    have hdq : p ∣ q := by
      have : (p : ℤ) ∣ (q : ℤ) := by rw [hqv]; exact hdvd
      exact_mod_cast this
    have hp1 : 1 < p := hp.one_lt
    rcases hqnat.eq_one_or_self_of_dvd p hdq with hh | hh <;> omega
  -- the filter output: `F(c^n) ≡ x_n (mod c^(n/2))` with `x_n ∈ {1 − h, −1 − h}`
  have hstep3 : ∀ n ≥ N, ∃ x : ℤ, (x = 1 - h ∨ x = -1 - h) ∧
      (c : ℤ) ^ (n / 2) ∣ (Nat.fib (c ^ n) : ℤ) - x := by
    intro n hn
    obtain ⟨p, hp, hpc, hpv⟩ := hnat n hn
    have hlt : n < padicValNat c (glCard 2 p) := by
      by_contra hle
      exact hstep2 n hn p hp hpv (by omega)
    rcases pow_dvd_sub_or_add_of_lt_padicValNat hc hc2 hp hpc hlt with hd | hd
    · refine ⟨1 - h, Or.inl rfl, ?_⟩
      rw [hpv] at hd
      have e : (Nat.fib (c ^ n) : ℤ) - (1 - h) = t n - 1 := by simp only [htdef]; ring
      rw [e]; exact hd
    · refine ⟨-1 - h, Or.inr rfl, ?_⟩
      rw [hpv] at hd
      have e : (Nat.fib (c ^ n) : ℤ) - (-1 - h) = t n + 1 := by simp only [htdef]; ring
      rw [e]; exact hd
  -- pick one large `n` and compare levels `n` and `n + 1`
  obtain ⟨n, hnN, hne⟩ : ∃ n, N ≤ n ∧ 2 * (B + 1) ≤ n / 2 :=
    ⟨2 * (B + 1) + 2 * N, by omega, by omega⟩
  set e : ℕ := n / 2 with hedef
  have hcpow : ((B : ℤ) + 1) < (c : ℤ) ^ e := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ e ≤ c ^ e := Nat.pow_le_pow_left hcle e
    have h3 : B + 1 < c ^ e := by omega
    exact_mod_cast h3
  obtain ⟨x, hx, hxd⟩ := hstep3 n hnN
  obtain ⟨y, hy, hyd⟩ := hstep3 (n + 1) (by omega)
  have hyd' : (c : ℤ) ^ e ∣ (Nat.fib (c ^ (n + 1)) : ℤ) - y :=
    dvd_trans (pow_dvd_pow _ (by omega)) hyd
  -- the composition step
  have hcomp : (Nat.fib (c ^ (n + 1)) : ℤ) = fibOddPoly (Nat.fib (c ^ n)) j := by
    have hoddn : Odd (c ^ n) := hcodd'.pow
    have hidx : c ^ (n + 1) = (2 * j + 1) * c ^ n := by
      rw [pow_succ, mul_comm]
      rw [← hj]
    rw [hidx]
    exact fib_odd_mul j hoddn
  have hphi : (c : ℤ) ^ e ∣ fibOddPoly (Nat.fib (c ^ n)) j - fibOddPoly x j :=
    dvd_fibOddPoly_sub hxd j
  have hkey : (c : ℤ) ^ e ∣ y - fibOddPoly x j := by
    have ee : y - fibOddPoly x j
        = (fibOddPoly (Nat.fib (c ^ n)) j - fibOddPoly x j)
          - ((Nat.fib (c ^ (n + 1)) : ℤ) - y) := by rw [hcomp]; ring
    rw [ee]
    exact dvd_sub hphi hyd'
  -- both `x` and `y` lie in `{1 − h, −1 − h}`, so `|y − Φ_j(x)| ≤ B`
  have hxb : |x| ≤ (H : ℤ) + 1 := by
    rcases hx with rfl | rfl <;> rw [abs_le] <;> omega
  have hbnd : |y - fibOddPoly x j| ≤ (B : ℤ) := by
    have hBz : ((fibOddPoly (1 - h) j).natAbs : ℤ) + ((fibOddPoly (-1 - h) j).natAbs : ℤ)
        + 2 * (H : ℤ) + 8 = (B : ℤ) := by rw [hB]; push_cast; ring
    have hyb : |y| ≤ (H : ℤ) + 1 := by
      rcases hy with rfl | rfl <;> rw [abs_le] <;> omega
    have hz1 : (0 : ℤ) ≤ ((fibOddPoly (1 - h) j).natAbs : ℤ) := Int.natCast_nonneg _
    have hz2 : (0 : ℤ) ≤ ((fibOddPoly (-1 - h) j).natAbs : ℤ) := Int.natCast_nonneg _
    have hxb2 : |fibOddPoly x j| ≤ ((fibOddPoly (1 - h) j).natAbs : ℤ)
        + ((fibOddPoly (-1 - h) j).natAbs : ℤ) := by
      rcases hx with rfl | rfl
      · rw [Int.abs_eq_natAbs]; omega
      · rw [Int.abs_eq_natAbs]; omega
    have hH0 : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg _
    rcases abs_cases y with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (fibOddPoly x j) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases abs_cases (y - fibOddPoly x j) with ⟨e3, _⟩ | ⟨e3, _⟩ <;> omega
  have hzero : y - fibOddPoly x j = 0 := by
    by_contra hnz
    have hle := Int.le_of_dvd (abs_pos.2 hnz) ((dvd_abs _ _).2 hkey)
    omega
  -- so `Φ_j(x) = y`, and `y − x ∈ {0, 2, −2}`
  have hdiff : fibOddPoly x j - x = 0 ∨ fibOddPoly x j - x = 2 ∨ fibOddPoly x j - x = -2 := by
    have hyx : fibOddPoly x j = y := by omega
    rw [hyx]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
  -- step 2 forces `x = 0`
  have hx0 : x = 0 := by
    by_contra hxn
    obtain ⟨g1, g2, g3⟩ := fibOddPoly_far hxn hj1
    rcases hdiff with hh | hh | hh
    · exact g1 hh
    · exact g2 hh
    · exact g3 hh
  -- then `c ∣ F(c^n)`, contradicting step 3
  rw [hx0, sub_zero] at hxd
  have hc1 : (c : ℤ) ∣ (Nat.fib (c ^ n) : ℤ) := by
    exact dvd_trans (dvd_pow_self (c : ℤ) (show e ≠ 0 by omega)) hxd
  exact not_dvd_fib_prime_pow hc hc5 n hc1

/-! ### Step 5: assembly -/

/-- **`F(c^n) + h` is composite infinitely often, for every prime `c` and every integer `h`.** -/
theorem fib_prime_pow_add_not_prime_all {c : ℕ} (hc : c.Prime) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  rcases eq_or_ne c 2 with rfl | hc2
  · exact SaitoFibonacci.fib_two_pow_add_not_prime h
  rcases eq_or_ne c 5 with rfl | hc5
  · exact fib_five_pow_add_not_prime h
  exact fib_prime_pow_add_not_prime_odd hc hc2 hc5 h

end LeanFormalizations.Mills.FibonacciAllPrimes

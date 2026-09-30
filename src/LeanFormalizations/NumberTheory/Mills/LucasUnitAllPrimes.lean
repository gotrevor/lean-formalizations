/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasInert
import LeanFormalizations.NumberTheory.Mills.FibonacciAllPrimes

/-!
# Phase 38: `U_(c^n)(P, ±1) + h` is composite i.o. at every odd prime `c ∤ D`

Phase 37's exact-composition route (Fibonacci at every prime) for every non-degenerate Lucas
sequence with `Q = ±1` (`D = P² − 4Q`).  It covers split and inert `c` alike, so there is no
Frobenius and no non-integrality argument.  Checked numerically for `|P| ≤ 6`, `N ≤ 7`,
`j ≤ 4`, `c ≤ 13`.

## Route
1. `lucasOddPoly D ε x j`: `Φ_0 = x`, `Φ_1 = D x³ + 3ε x`,
   `Φ_(j+2) = (D x² + 2ε) Φ_(j+1) − Φ_j`.
   `lucasU_odd_mul`: for `Q ∈ {1, −1}` and odd `N`,
   `U_((2j+1)N) = lucasOddPoly (P² − 4Q) Q (U_N) j`.  Route: `U_(a+b) + Q^b U_(a−b) = U_a V_b`
   with `b = 2N`, `V_(2N) = D U_N² + 2Q^N` (from `V² − D U² = 4Q^N`), `Q^N = Q` for odd `N`,
   and `U_(−N) = −Q^(−N) U_N`.  Generalize phase 37's `fib_odd_mul`.
2. `lucasOddPoly_far`: for `x ≠ 0`, `j ≥ 1`, `D = P² − 4ε ≥ 5` (the abstract `D = 6, ε = −1`
   is a genuine exception, `Φ_1(±1) = ±3`, but is not of the form `P² + 4`):
   `Φ_j(x) − x ∉ {0, 2, −2}`.  With `t = D x² + 2ε ≥ 3`, `|Φ_1| = |x| (D x² + 3ε) ≥ 2|x|` and the
   recurrence grows.  Generalize phase 37's `fibOddPoly_far`.
3. `not_dvd_lucasU_prime_pow`: odd prime `c ∤ D`, `Q = ±1` ⟹ `c ∤ U(c^n)`.  Route: `U_c ≡ (D/c)
   (mod c)` (`2^(c−1) U_c = Σ binom(c, 2i+1) P^(c−2i−1) D^i`), then induct with step 1 and
   `Φ_j(x) ≡ (D/c) x^c (mod c)`, or use the rank of apparition `c ∣ U_(c − (D/c))` plus
   `gcd(U_m, U_k) = U_gcd` (strong divisibility; `Q = ±1` makes `gcd(P, Q) = 1`).
4. Main theorem.  The filter (`exists_entry_pow_congr` on `A = !![P, −Q; 1, 0]`, `det A = Q = ±1`,
   and `pow_dvd_sub_or_add_of_lt_padicValNat`) gives `U(c^n) ≡ x_n ∈ {1 − h, −1 − h}` mod
   `c^(n/2)`.  Step 1 gives `x_(n+1) = Φ_j(x_n)` for large `n` (finite sets), step 2 gives
   `x_n = 0`, and step 3 gives the contradiction.  Growth: `|U(c^n)| → ∞` follows from the
   hypotheses, but it is assumed below (frozen) to keep the statement simple.

Frozen: every statement and def below; statements of all earlier Mills phase files and
`Literature/`.  Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.LucasUnitAllPrimes

open LeanFormalizations.Mills.ThreeAdic LeanFormalizations.Mills.LucasTwoPow Filter
open LeanFormalizations.Mills.LucasInert LeanFormalizations.Mills.LucasPrimePow
open LeanFormalizations.Mills.FibonacciPrimePow LeanFormalizations.Mills.FibonacciAllPrimes

/-- `Φ_j` with `U_((2j+1)N) = Φ_j(U_N)` for odd `N`, when `Q = ε = ±1` and `D = P² − 4Q`. -/
def lucasOddPoly (D ε x : ℤ) : ℕ → ℤ
  | 0 => x
  | 1 => D * x ^ 3 + 3 * ε * x
  | j + 2 => (D * x ^ 2 + 2 * ε) * lucasOddPoly D ε x (j + 1) - lucasOddPoly D ε x j

/-! ### Matrix preliminaries: the entries of `A^N` -/

theorem lucasU_zero (P Q : ℤ) : lucasU P Q 0 = 0 := by
  simp [lucasU, Matrix.one_apply]

theorem lucasU_one (P Q : ℤ) : lucasU P Q 1 = 1 := by simp [lucasU]

/-- `(A^N) 0 1 = -Q * U(N)`. -/
theorem lucasA_pow_apply_zero_one (P Q : ℤ) (N : ℕ) :
    (lucasA P Q ^ N) 0 1 = -Q * lucasU P Q N := by
  cases N with
  | zero => simp [lucasU_zero, Matrix.one_apply]
  | succ m => rw [lucasA_pow_succ_apply_one, lucasA_pow_apply_zero_zero]

/-- `(A^(m+1)) 1 1 = -Q * U(m)`. -/
theorem lucasA_pow_succ_apply_one_one (P Q : ℤ) (m : ℕ) :
    (lucasA P Q ^ (m + 1)) 1 1 = -Q * lucasU P Q m := by
  rw [lucasA_pow_succ_apply_one, lucasA_pow_apply_one_zero]

/-- `V(N)² = D U(N)² + 4 Q^N` for `N ≥ 1`, where `V = tr(A^N)` and `D = P² − 4Q`. -/
theorem lucasA_pow_trace_sq (P Q : ℤ) (m : ℕ) :
    (lucasA P Q ^ (m + 1)).trace ^ 2
      = (P ^ 2 - 4 * Q) * lucasU P Q (m + 1) ^ 2 + 4 * Q ^ (m + 1) := by
  have hdet : (lucasA P Q ^ (m + 1)).det = Q ^ (m + 1) := by
    rw [Matrix.det_pow, lucasA_det]
  rw [Matrix.det_fin_two, lucasA_pow_apply_zero_zero, lucasA_pow_succ_apply_one_one,
    lucasA_pow_apply_zero_one, lucasA_pow_apply_one_zero] at hdet
  rw [Matrix.trace_fin_two, lucasA_pow_apply_zero_zero, lucasA_pow_succ_apply_one_one]
  have hrec := lucasU_add_two P Q m
  linear_combination (4 : ℤ) * hdet
    + (lucasU P Q (m + 2) + Q * lucasU P Q m + P * lucasU P Q (m + 1)) * hrec

/-! ### Step 1: the composition identity `U((2j+1)N) = Φ_j(U N)` for odd `N` -/

/-- The normalized companion: `lucasOddPoly D ε x j = x * lucasOddAux ε (D x² + 2ε) j`. -/
def lucasOddAux (ε t : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => t + ε
  | j + 2 => t * lucasOddAux ε t (j + 1) - lucasOddAux ε t j

theorem lucasOddPoly_eq_mul (D ε x : ℤ) (j : ℕ) :
    lucasOddPoly D ε x j = x * lucasOddAux ε (D * x ^ 2 + 2 * ε) j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [lucasOddPoly, lucasOddAux]
  | one => simp only [lucasOddPoly, lucasOddAux]; ring
  | more j ih1 ih2 => simp only [lucasOddPoly, lucasOddAux, ih1, ih2]; ring

theorem lucasU_odd_mul {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1) (j : ℕ) {N : ℕ} (hN : Odd N) :
    lucasU P Q ((2 * j + 1) * N) = lucasOddPoly (P ^ 2 - 4 * Q) Q (lucasU P Q N) j := by
  obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by rcases hN with ⟨k, hk⟩; omega⟩
  have hQN : Q ^ N = Q := by
    rcases hQ with rfl | rfl
    · simp
    · rw [hN.neg_one_pow]
  have hQ2 : Q ^ 2 = 1 := by rcases hQ with rfl | rfl <;> norm_num
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, A = lucasA P Q ^ N := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = A.trace := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = (P ^ 2 - 4 * Q) * lucasU P Q N ^ 2 + 2 * Q := ⟨_, rfl⟩
  have hdet : A.det = Q := by rw [hA, Matrix.det_pow, lucasA_det, hQN]
  have hLsq : L ^ 2 = (P ^ 2 - 4 * Q) * lucasU P Q N ^ 2 + 4 * Q := by
    rw [hL, hA, hm]
    rw [lucasA_pow_trace_sq P Q m, ← hm, hQN]
  have hentry : ∀ k : ℕ, (A ^ k) 1 0 = lucasU P Q (k * N) := by
    intro k
    rw [hA, ← pow_mul, mul_comm N k, lucasA_pow_apply_one_zero]
  have hA10 : A 1 0 = lucasU P Q N := by
    have := hentry 1
    rwa [pow_one, one_mul] at this
  have hA2 : A ^ 2 = L • A - Q • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    have h := sq_eq_trace_smul_sub_det A
    rw [hdet, ← hL] at h
    exact h
  have hB : (A ^ 2).trace = T := by
    rw [hA2, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      ← hL, Matrix.trace_one, hT]
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    linear_combination hLsq
  have hBdet : (A ^ 2).det = 1 := by rw [Matrix.det_pow, hdet, hQ2]
  have hA4 : A ^ 4 = T • A ^ 2 - 1 := by
    have h := sq_eq_trace_smul_sub_det (A ^ 2)
    rw [hB, hBdet, ← pow_mul] at h
    simpa using h
  have hone : (A ^ 3) 1 0
      = (P ^ 2 - 4 * Q) * lucasU P Q N ^ 3 + 3 * Q * lucasU P Q N := by
    have h3 : A ^ 3 = (L ^ 2 - Q) • A - (L * Q) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      have e : A ^ 3 = A * A ^ 2 := by rw [← pow_succ']
      rw [e, hA2, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
        ← pow_two, hA2]
      rw [smul_sub, smul_smul, smul_smul]
      module
    rw [h3]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hA10, show (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 from by simp, hLsq]
    ring
  have key : ∀ k : ℕ, (A ^ (2 * k + 1)) 1 0 = lucasOddPoly (P ^ 2 - 4 * Q) Q (lucasU P Q N) k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simpa [lucasOddPoly] using hA10
    | one => simpa [lucasOddPoly] using hone
    | more k ih1 ih2 =>
        have hsplit : A ^ (2 * (k + 2) + 1) = A ^ (2 * k + 1) * A ^ 4 := by
          rw [← pow_add]; ring_nf
        have hmul : A ^ (2 * k + 1) * A ^ 2 = A ^ (2 * (k + 1) + 1) := by
          rw [← pow_add]; ring_nf
        rw [hsplit, hA4, Matrix.mul_sub, Matrix.mul_smul, hmul, Matrix.mul_one]
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        rw [ih1, ih2]
        simp only [lucasOddPoly]
        rw [hT]
  have h := key j
  rw [hentry (2 * j + 1)] at h
  exact h

/-! ### Step 2: `Φ_j(x)` is far from `x` -/

theorem lucasOddPoly_neg (D ε x : ℤ) (j : ℕ) :
    lucasOddPoly D ε (-x) j = - lucasOddPoly D ε x j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [lucasOddPoly]
  | one => simp only [lucasOddPoly]; ring
  | more j ih1 ih2 => simp only [lucasOddPoly, ih1, ih2]; ring

theorem lucasOddAux_growth {ε t : ℤ} (hε : ε = 1 ∨ ε = -1) (ht : 3 ≤ t) (j : ℕ) :
    1 ≤ lucasOddAux ε t j ∧ lucasOddAux ε t j < lucasOddAux ε t (j + 1) := by
  induction j with
  | zero =>
      refine ⟨by simp [lucasOddAux], ?_⟩
      have he : lucasOddAux ε t 1 = t + ε := rfl
      have h0 : lucasOddAux ε t 0 = 1 := rfl
      rw [he, h0]
      rcases hε with rfl | rfl <;> omega
  | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨by omega, ?_⟩
      have he : lucasOddAux ε t (j + 2) = t * lucasOddAux ε t (j + 1) - lucasOddAux ε t j := rfl
      rw [he]
      nlinarith

theorem lucasOddAux_mono {ε t : ℤ} (hε : ε = 1 ∨ ε = -1) (ht : 3 ≤ t) {a b : ℕ} (hab : a ≤ b) :
    lucasOddAux ε t a ≤ lucasOddAux ε t b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans ih (le_of_lt (lucasOddAux_growth hε ht n).2)

theorem lucasOddPoly_far_pos {P ε x : ℤ} (hε : ε = 1 ∨ ε = -1) (hD : 5 ≤ P ^ 2 - 4 * ε)
    (hx : 1 ≤ x) {j : ℕ} (hj : 1 ≤ j) :
    1 ≤ lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ∧
      lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ≠ 2 := by
  set D : ℤ := P ^ 2 - 4 * ε with hDdef
  set t : ℤ := D * x ^ 2 + 2 * ε with htdef
  have hxsq : 1 ≤ x ^ 2 := by nlinarith
  have ht : 3 ≤ t := by rcases hε with rfl | rfl <;> [nlinarith; nlinarith]
  have hd : lucasOddPoly D ε x j - x = x * (lucasOddAux ε t j - 1) := by
    rw [lucasOddPoly_eq_mul]; ring
  have hA1 : lucasOddAux ε t 1 = t + ε := rfl
  have hAj : t + ε ≤ lucasOddAux ε t j := by
    have := lucasOddAux_mono hε ht (a := 1) (b := j) hj
    omega
  have hAge : 2 ≤ t + ε := by rcases hε with rfl | rfl <;> omega
  refine ⟨by rw [hd]; nlinarith, ?_⟩
  rw [hd]
  intro hcon
  -- `x * (A − 1) = 2` with `x ≥ 1` and `A − 1 ≥ 1`
  have hA1' : 1 ≤ lucasOddAux ε t j - 1 := by omega
  have hxle : x ≤ 2 := by nlinarith
  -- case `x = 2` is impossible: then `t` is huge
  have hx1 : x = 1 := by
    rcases (by omega : x = 1 ∨ x = 2) with h | h
    · exact h
    · exfalso
      have hx4 : x ^ 2 = 4 := by rw [h]; norm_num
      have : 18 ≤ t := by rw [htdef, hx4]; rcases hε with rfl | rfl <;> omega
      nlinarith
  -- so `x = 1` and `lucasOddAux ε t j = 3`
  have hA3 : lucasOddAux ε t j = 3 := by rw [hx1] at hcon; omega
  have hxsq1 : x ^ 2 = 1 := by rw [hx1]; norm_num
  have hteq : t = D + 2 * ε := by rw [htdef, hxsq1]; ring
  -- either `lucasOddAux ε t 1 ≥ 4` (and monotonicity kills it), or `t = 3, ε = -1, D = 5`
  rcases hε with rfl | rfl
  · -- `ε = 1`: `t = D + 2 ≥ 7`, so `lucasOddAux 1 t j ≥ 8`
    have : 7 ≤ t := by omega
    omega
  · -- `ε = -1`: `t = D − 2`, `D = P² + 4`
    have hDP : D = P ^ 2 + 4 := by rw [hDdef]; ring
    have hP2 : P ^ 2 ≠ 2 := by
      intro hP
      have h1 : -1 ≤ P := by nlinarith [sq_nonneg (P + 2)]
      have h2 : P ≤ 1 := by nlinarith [sq_nonneg (P - 2)]
      interval_cases P <;> norm_num at hP
    have hDne : D ≠ 6 := by omega
    rcases (by omega : t = 3 ∨ 5 ≤ t) with h3 | h5
    · -- `t = 3`: the aux sequence is `1, 2, 5, 13, …`, never `3`
      have h1v : lucasOddAux (-1 : ℤ) t 1 = 2 := by rw [hA1, h3]; ring
      have h2v : lucasOddAux (-1 : ℤ) t 2 = 5 := by
        have he : lucasOddAux (-1 : ℤ) t 2
            = t * lucasOddAux (-1 : ℤ) t 1 - lucasOddAux (-1 : ℤ) t 0 := rfl
        rw [he, h1v, h3]; norm_num [lucasOddAux]
      rcases (by omega : j = 1 ∨ 2 ≤ j) with hj1 | hj2
      · rw [hj1, h1v] at hA3; omega
      · have := lucasOddAux_mono (ε := (-1 : ℤ)) (t := t) (by norm_num) (by omega)
            (a := 2) (b := j) hj2
        omega
    · omega

theorem lucasOddPoly_far {P ε x : ℤ} (hε : ε = 1 ∨ ε = -1) (hD : 5 ≤ P ^ 2 - 4 * ε)
    (hx : x ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ≠ 0 ∧ lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ≠ 2 ∧
      lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ≠ -2 := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hy : 1 ≤ -x := by omega
    obtain ⟨g1, g2⟩ := lucasOddPoly_far_pos hε hD hy hj
    rw [lucasOddPoly_neg] at g1 g2
    refine ⟨by omega, by omega, by omega⟩
  · obtain ⟨g1, g2⟩ := lucasOddPoly_far_pos hε hD (show 1 ≤ x by omega) hj
    refine ⟨by omega, by omega, by omega⟩

/-! ### Step 3: `c ∤ U(c^n)` for an odd prime `c ∤ D` -/

theorem not_dvd_of_unit {Q : ℤ} (hQ : Q = 1 ∨ Q = -1) {c : ℕ} (hc : c.Prime) :
    ¬ (c : ℤ) ∣ Q := by
  have hc2 := hc.two_le
  rcases hQ with rfl | rfl
  · intro hd
    have := Int.le_of_dvd one_pos hd
    omega
  · intro hd
    have hd' : (c : ℤ) ∣ (1 : ℤ) := by
      have h := dvd_neg.mpr hd
      simpa using h
    have := Int.le_of_dvd one_pos hd'
    omega

theorem two_ne_zero_zmod {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) : (2 : ZMod c) ≠ 0 := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hcast : ((2 : ℕ) : ZMod c) = (2 : ZMod c) := by norm_num
  rw [← hcast, Ne, ZMod.natCast_eq_zero_iff]
  intro hdd
  exact hc2 ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).1 hdd)

/-- **The split case**: if `D` is a nonzero square mod `c`, then `U(c^n) ≡ 1 (mod c)`. -/
theorem lucasU_prime_pow_split_eq_one {P Q : ℤ} {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hsq : IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) (n : ℕ) :
    ((lucasU P Q (c ^ n) : ℤ) : ZMod c) = 1 := by
  haveI : Fact c.Prime := ⟨hc⟩
  obtain ⟨d, hd⟩ := hsq
  have h2ne : (2 : ZMod c) ≠ 0 := two_ne_zero_zmod hc hc2
  obtain ⟨u, hu⟩ : ∃ u : ZMod c, (2 : ZMod c) * u = 1 :=
    ⟨(2 : ZMod c)⁻¹, mul_inv_cancel₀ h2ne⟩
  obtain ⟨α, hα⟩ : ∃ α : ZMod c, α = ((P : ZMod c) + d) * u := ⟨_, rfl⟩
  have h2A : 2 * α = (P : ZMod c) + d := by
    rw [hα]; linear_combination ((P : ZMod c) + d) * hu
  have h4u : (4 : ZMod c) * (u * u) = 1 := by linear_combination (2 * u + 1) * hu
  have hDcast : ((P ^ 2 - 4 * Q : ℤ) : ZMod c) = (P : ZMod c) ^ 2 - 4 * (Q : ZMod c) := by
    push_cast; ring
  have hdd : d * d = (P : ZMod c) ^ 2 - 4 * (Q : ZMod c) := by rw [← hDcast, ← hd]
  have hbig : (2 * α) ^ 2 - 2 * (P : ZMod c) * (2 * α) + 4 * (Q : ZMod c) = 0 := by
    rw [h2A]; linear_combination hdd
  have hαroot : α ^ 2 = (P : ZMod c) * α - (Q : ZMod c) := by
    have e : α ^ 2 - (P : ZMod c) * α + (Q : ZMod c)
        = (u * u) * ((2 * α) ^ 2 - 2 * (P : ZMod c) * (2 * α) + 4 * (Q : ZMod c)) := by
      linear_combination (-(α ^ 2) + (P : ZMod c) * α - (Q : ZMod c)) * h4u
    rw [hbig, mul_zero] at e
    linear_combination e
  obtain ⟨β, hβ⟩ : ∃ β : ZMod c, β = (P : ZMod c) - α := ⟨_, rfl⟩
  have hβroot : β ^ 2 = (P : ZMod c) * β - (Q : ZMod c) := by
    rw [hβ]; linear_combination hαroot
  have hdne : α - β ≠ 0 := by
    have hab : α - β = d := by rw [hβ]; linear_combination h2A
    rw [hab]
    intro h0
    rw [h0] at hd
    rw [mul_zero] at hd
    exact hD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ c).1 hd)
  have hpow : ∀ z : ZMod c, z ^ (c ^ n) = z := by
    intro z
    induction n with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  obtain ⟨N, hN⟩ : ∃ N, c ^ n = N + 1 :=
    ⟨c ^ n - 1, by have := Nat.one_le_pow n c hc.pos; omega⟩
  have hae := pow_eq_lucasU P Q hαroot N
  have hbe := pow_eq_lucasU P Q hβroot N
  rw [← hN, hpow α] at hae
  rw [← hN, hpow β] at hbe
  have hz : (α - β) * (((lucasU P Q (c ^ n) : ℤ) : ZMod c) - 1) = 0 := by
    linear_combination hbe - hae
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h hdne
  · linear_combination h

theorem not_dvd_lucasU_prime_pow {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1) {c : ℕ} (hc : c.Prime)
    (hc2 : c ≠ 2) (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q) (n : ℕ) :
    ¬ (c : ℤ) ∣ lucasU P Q (c ^ n) := by
  haveI : Fact c.Prime := ⟨hc⟩
  intro hdvd
  by_cases hsq : IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)
  · have h1 := lucasU_prime_pow_split_eq_one hc hc2 hD hsq n
    have h0 : ((lucasU P Q (c ^ n) : ℤ) : ZMod c) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).2 hdvd
    rw [h0] at h1
    exact zero_ne_one h1
  · have hmod := lucasU_prime_pow_mod hc (not_dvd_of_unit hQ hc) hsq n
    have h1 : (c : ℤ) ∣ (-1 : ℤ) ^ n := by
      have e : (-1 : ℤ) ^ n = lucasU P Q (c ^ n) - (lucasU P Q (c ^ n) - (-1) ^ n) := by ring
      rw [e]
      exact dvd_sub hdvd hmod
    have h2 : ((-1 : ℤ) ^ n).natAbs = 1 := by
      rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_one_pow]; norm_num
      · rw [ho.neg_one_pow]; norm_num
    have h3 : c ∣ 1 := by
      have := Int.natAbs_dvd_natAbs.2 h1
      rwa [Int.natAbs_natCast, h2] at this
    have h4 := Nat.le_of_dvd one_pos h3
    have := hc.two_le
    omega

/-! ### Step 4: the main theorem -/

/-- **The mechanism** (prime as modulus), read off entry `(1,0)` of `A = !![P, −Q; 1, 0]`. -/
theorem exists_lucasU_prime_pow_congr {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1) {c p m : ℕ}
    (hp : p.Prime) (hc : c.Prime) (hv : padicValNat c (glCard 2 p) ≤ m) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ lucasU P Q (c ^ (m + j)) - lucasU P Q (c ^ m) := by
  have hdet : ¬ (p : ℤ) ∣ (lucasA P Q).det := by
    rw [lucasA_det]; exact not_dvd_of_unit hQ hp
  obtain ⟨jj, hj1, hjj⟩ := SaitoFibonacci.exists_entry_pow_congr (lucasA P Q) hp hc hdet hv
  refine ⟨jj, hj1, ?_⟩
  have hh := hjj 1 0
  rwa [lucasA_pow_apply_one_zero, lucasA_pow_apply_one_zero] at hh

/-- `Φ_j` respects congruences: it is a polynomial with integer coefficients. -/
theorem dvd_lucasOddPoly_sub {D ε M a b : ℤ} (hM : M ∣ a - b) (j : ℕ) :
    M ∣ lucasOddPoly D ε a j - lucasOddPoly D ε b j := by
  induction j using Nat.twoStepInduction with
  | zero => simpa [lucasOddPoly] using hM
  | one =>
      simp only [lucasOddPoly]
      have e : D * a ^ 3 + 3 * ε * a - (D * b ^ 3 + 3 * ε * b)
          = (a - b) * (D * (a ^ 2 + a * b + b ^ 2) + 3 * ε) := by ring
      rw [e]
      exact hM.mul_right _
  | more j ih1 ih2 =>
      simp only [lucasOddPoly]
      have e : (D * a ^ 2 + 2 * ε) * lucasOddPoly D ε a (j + 1) - lucasOddPoly D ε a j
            - ((D * b ^ 2 + 2 * ε) * lucasOddPoly D ε b (j + 1) - lucasOddPoly D ε b j)
          = (a - b) * (D * (a + b) * lucasOddPoly D ε b (j + 1))
            + (D * a ^ 2 + 2 * ε)
              * (lucasOddPoly D ε a (j + 1) - lucasOddPoly D ε b (j + 1))
            - (lucasOddPoly D ε a j - lucasOddPoly D ε b j) := by ring
      rw [e]
      exact dvd_sub (dvd_add (hM.mul_right _) (ih2.mul_left _)) ih1

/-- A prime `p` dividing a prime `x` pins `|x| = p`. -/
theorem abs_eq_of_prime_dvd_prime {p : ℕ} (hp : p.Prime) {x : ℤ} (hd : (p : ℤ) ∣ x)
    (hx : Prime x) : |x| = (p : ℤ) := by
  have hn : x.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hx
  have hd' : p ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd
    simpa using this
  rcases hn.eq_one_or_self_of_dvd p hd' with hh | hh
  · exact absurd hh hp.one_lt.ne'
  · rw [Int.abs_eq_natAbs, hh]

/-- **`U_(c^n)(P, ±1) + h` is composite infinitely often**, for every odd prime `c ∤ D`,
`D = P² − 4Q ≥ 5`, and every integer `h`. -/
theorem lucasU_unit_prime_pow_add_not_prime {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1)
    (hD5 : 5 ≤ P ^ 2 - 4 * Q) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (c ^ n) + h) := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hcodd' : Odd c := hcodd
  obtain ⟨j, hj⟩ := hcodd
  have hcle : 2 ≤ c := hc.two_le
  have hj1 : 1 ≤ j := by omega
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  set U : ℕ → ℤ := fun n => lucasU P Q (c ^ n) with hUdef
  set t : ℕ → ℤ := fun n => U n + h with htdef
  set H : ℕ := h.natAbs with hH
  have hhabs : |h| = (H : ℤ) := Int.abs_eq_natAbs h
  have hH0 : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg _
  have hprime : ∀ n ≥ n₀, Prime (t n) := fun n hn => hn₀ n hn
  have hgr : ∀ B : ℤ, ∃ N : ℕ, ∀ n ≥ N, B ≤ |U n| := by
    intro B
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hgrow B)
    exact ⟨N, hN⟩
  have hlowabs : ∀ n : ℕ, |U n| - (H : ℤ) ≤ |t n| := by
    intro n
    have hab := abs_sub_abs_le_abs_add' (a := U n) (b := h)
    simp only [htdef]
    omega
  -- ### the no-return step
  have hstep2 : ∀ n ≥ n₀, ∀ p : ℕ, p.Prime → (p : ℤ) = |t n| →
      ¬ (padicValNat c (glCard 2 p) ≤ n) := by
    intro n hn p hp hpv hv
    have hiter : ∀ k : ℕ, ∃ m, n + k ≤ m ∧ (p : ℤ) = |t m| ∧
        padicValNat c (glCard 2 p) ≤ m := by
      intro k
      induction k with
      | zero => exact ⟨n, by omega, hpv, hv⟩
      | succ k ih =>
          obtain ⟨m, hm, hpm, hvm⟩ := ih
          obtain ⟨jj, hjj1, hjj⟩ := exists_lucasU_prime_pow_congr hQ hp hc hvm
          have hpt : (p : ℤ) ∣ t m := by
            have hda : (p : ℤ) ∣ |t m| := by rw [← hpm]
            exact (dvd_abs _ _).mp hda
          have hdvd : (p : ℤ) ∣ t (m + jj) := by
            have e : t (m + jj) = (U (m + jj) - U m) + t m := by
              simp only [htdef, hUdef]; ring
            rw [e]
            exact dvd_add hjj hpt
          have hq := hprime (m + jj) (by omega)
          have habs := abs_eq_of_prime_dvd_prime hp hdvd hq
          exact ⟨m + jj, by omega, habs.symm, by omega⟩
    obtain ⟨K, hK⟩ := hgr ((p : ℤ) + (H : ℤ) + 1)
    obtain ⟨m, hm, hpm, -⟩ := hiter K
    have h1 := hK m (by omega)
    have h2 := hlowabs m
    omega
  -- ### the filter output
  obtain ⟨Na, hNa⟩ := hgr ((c : ℤ) + (H : ℤ) + 1)
  set N : ℕ := max n₀ Na with hNdef
  have hstep3 : ∀ n ≥ N, ∃ x : ℤ, (x = 1 - h ∨ x = -1 - h) ∧ (c : ℤ) ^ (n / 2) ∣ U n - x := by
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hNa' : Na ≤ n := le_trans (le_max_right _ _) hn
    have hUb := hNa n hNa'
    have hlow := hlowabs n
    have htp := hprime n hn₀'
    obtain ⟨p, hpv⟩ : ∃ p : ℕ, (p : ℤ) = |t n| := ⟨(t n).natAbs, (Int.abs_eq_natAbs _).symm⟩
    have hp : p.Prime := by
      have hn' : (t n).natAbs.Prime := Int.prime_iff_natAbs_prime.1 htp
      have : p = (t n).natAbs := by
        have := Int.abs_eq_natAbs (t n)
        omega
      rwa [this]
    have hpc : p ≠ c := by
      intro hEq
      rw [hEq] at hpv
      omega
    have hlt : n < padicValNat c (glCard 2 p) := by
      by_contra hle
      exact hstep2 n hn₀' p hp hpv (by omega)
    have hsgn : (p : ℤ) = t n ∨ (p : ℤ) = -t n := by
      rcases abs_cases (t n) with ⟨e1, _⟩ | ⟨e1, _⟩
      · left; omega
      · right; omega
    have hout : (c : ℤ) ^ (n / 2) ∣ t n - 1 ∨ (c : ℤ) ^ (n / 2) ∣ t n + 1 := by
      rcases pow_dvd_sub_or_add_of_lt_padicValNat hc hc2 hp hpc hlt with hdd | hdd
      · rcases hsgn with he | he
        · left; rw [he] at hdd; exact hdd
        · right
          rw [he] at hdd
          have hne : (c : ℤ) ^ (n / 2) ∣ -(t n + 1) := by
            have e : -(t n + 1) = -t n - 1 := by ring
            rw [e]; exact hdd
          exact dvd_neg.mp hne
      · rcases hsgn with he | he
        · right; rw [he] at hdd; exact hdd
        · left
          rw [he] at hdd
          have hne : (c : ℤ) ^ (n / 2) ∣ -(t n - 1) := by
            have e : -(t n - 1) = -t n + 1 := by ring
            rw [e]; exact hdd
          exact dvd_neg.mp hne
    rcases hout with hdd | hdd
    · refine ⟨1 - h, Or.inl rfl, ?_⟩
      have e : U n - (1 - h) = t n - 1 := by simp only [htdef]; ring
      rw [e]; exact hdd
    · refine ⟨-1 - h, Or.inr rfl, ?_⟩
      have e : U n - (-1 - h) = t n + 1 := by simp only [htdef]; ring
      rw [e]; exact hdd
  -- ### the endgame: compare levels `n` and `n + 1`
  set D : ℤ := P ^ 2 - 4 * Q with hDdef
  set B : ℕ := (lucasOddPoly D Q (1 - h) j).natAbs + (lucasOddPoly D Q (-1 - h) j).natAbs
    + 2 * H + 8 with hB
  obtain ⟨n, hnN, hne⟩ : ∃ n, N ≤ n ∧ B + 1 ≤ n / 2 :=
    ⟨2 * (B + 1) + 2 * N, by omega, by omega⟩
  set e : ℕ := n / 2 with hedef
  have hcpow : ((B : ℤ) + 1) < (c : ℤ) ^ e := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ e ≤ c ^ e := Nat.pow_le_pow_left hcle e
    have h3 : B + 1 < c ^ e := by omega
    exact_mod_cast h3
  obtain ⟨x, hx, hxd⟩ := hstep3 n hnN
  obtain ⟨y, hy, hyd⟩ := hstep3 (n + 1) (by omega)
  have hyd' : (c : ℤ) ^ e ∣ U (n + 1) - y := dvd_trans (pow_dvd_pow _ (by omega)) hyd
  have hcomp : U (n + 1) = lucasOddPoly D Q (U n) j := by
    have hoddn : Odd (c ^ n) := hcodd'.pow
    have hidx : c ^ (n + 1) = (2 * j + 1) * c ^ n := by rw [pow_succ, mul_comm, ← hj]
    simp only [hUdef]
    rw [hidx]
    exact lucasU_odd_mul hQ j hoddn
  have hphi : (c : ℤ) ^ e ∣ lucasOddPoly D Q (U n) j - lucasOddPoly D Q x j :=
    dvd_lucasOddPoly_sub hxd j
  have hkey : (c : ℤ) ^ e ∣ y - lucasOddPoly D Q x j := by
    have ee : y - lucasOddPoly D Q x j
        = (lucasOddPoly D Q (U n) j - lucasOddPoly D Q x j) - (U (n + 1) - y) := by
      rw [hcomp]; ring
    rw [ee]
    exact dvd_sub hphi hyd'
  have hxb : |x| ≤ (H : ℤ) + 1 := by rcases hx with rfl | rfl <;> rw [abs_le] <;> omega
  have hbnd : |y - lucasOddPoly D Q x j| ≤ (B : ℤ) := by
    have hBz : ((lucasOddPoly D Q (1 - h) j).natAbs : ℤ)
        + ((lucasOddPoly D Q (-1 - h) j).natAbs : ℤ) + 2 * (H : ℤ) + 8 = (B : ℤ) := by
      rw [hB]; push_cast; ring
    have hyb : |y| ≤ (H : ℤ) + 1 := by rcases hy with rfl | rfl <;> rw [abs_le] <;> omega
    have hz1 : (0 : ℤ) ≤ ((lucasOddPoly D Q (1 - h) j).natAbs : ℤ) := Int.natCast_nonneg _
    have hz2 : (0 : ℤ) ≤ ((lucasOddPoly D Q (-1 - h) j).natAbs : ℤ) := Int.natCast_nonneg _
    have hxb2 : |lucasOddPoly D Q x j| ≤ ((lucasOddPoly D Q (1 - h) j).natAbs : ℤ)
        + ((lucasOddPoly D Q (-1 - h) j).natAbs : ℤ) := by
      rcases hx with rfl | rfl
      · rw [Int.abs_eq_natAbs]; omega
      · rw [Int.abs_eq_natAbs]; omega
    rcases abs_cases y with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (lucasOddPoly D Q x j) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases abs_cases (y - lucasOddPoly D Q x j) with ⟨e3, _⟩ | ⟨e3, _⟩ <;> omega
  have hzero : y - lucasOddPoly D Q x j = 0 := by
    by_contra hnz
    have hle := Int.le_of_dvd (abs_pos.2 hnz) ((dvd_abs _ _).2 hkey)
    omega
  have hdiff : lucasOddPoly D Q x j - x = 0 ∨ lucasOddPoly D Q x j - x = 2 ∨
      lucasOddPoly D Q x j - x = -2 := by
    have hyx : lucasOddPoly D Q x j = y := by omega
    rw [hyx]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
  have hx0 : x = 0 := by
    by_contra hxn
    obtain ⟨g1, g2, g3⟩ := lucasOddPoly_far (P := P) hQ hD5 hxn hj1
    rw [← hDdef] at g1 g2 g3
    rcases hdiff with hh | hh | hh
    · exact g1 hh
    · exact g2 hh
    · exact g3 hh
  rw [hx0, sub_zero] at hxd
  have hc1 : (c : ℤ) ∣ U n := dvd_trans (dvd_pow_self (c : ℤ) (show e ≠ 0 by omega)) hxd
  exact not_dvd_lucasU_prime_pow hQ hc hc2 hD n hc1

end LeanFormalizations.Mills.LucasUnitAllPrimes

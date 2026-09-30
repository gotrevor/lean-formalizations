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

/-- **`U_(c^n)(P, ±1) + h` is composite infinitely often**, for every odd prime `c ∤ D`,
`D = P² − 4Q ≥ 5`, and every integer `h`. -/
theorem lucasU_unit_prime_pow_add_not_prime {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1)
    (hD5 : 5 ≤ P ^ 2 - 4 * Q) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (c ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.LucasUnitAllPrimes

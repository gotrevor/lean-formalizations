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

/-- `Φ_j` with `U_((2j+1)N) = Φ_j(U_N)` for odd `N`, when `Q = ε = ±1` and `D = P² − 4Q`. -/
def lucasOddPoly (D ε x : ℤ) : ℕ → ℤ
  | 0 => x
  | 1 => D * x ^ 3 + 3 * ε * x
  | j + 2 => (D * x ^ 2 + 2 * ε) * lucasOddPoly D ε x (j + 1) - lucasOddPoly D ε x j

theorem lucasU_odd_mul {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1) (j : ℕ) {N : ℕ} (hN : Odd N) :
    lucasU P Q ((2 * j + 1) * N) = lucasOddPoly (P ^ 2 - 4 * Q) Q (lucasU P Q N) j := by
  sorry

theorem lucasOddPoly_far {P ε x : ℤ} (hε : ε = 1 ∨ ε = -1) (hD : 5 ≤ P ^ 2 - 4 * ε)
    (hx : x ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ≠ 0 ∧ lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ≠ 2 ∧
      lucasOddPoly (P ^ 2 - 4 * ε) ε x j - x ≠ -2 := by
  sorry

theorem not_dvd_lucasU_prime_pow {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1) {c : ℕ} (hc : c.Prime)
    (hc2 : c ≠ 2) (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q) (n : ℕ) :
    ¬ (c : ℤ) ∣ lucasU P Q (c ^ n) := by
  sorry

/-- **`U_(c^n)(P, ±1) + h` is composite infinitely often**, for every odd prime `c ∤ D`,
`D = P² − 4Q ≥ 5`, and every integer `h`. -/
theorem lucasU_unit_prime_pow_add_not_prime {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1)
    (hD5 : 5 ≤ P ^ 2 - 4 * Q) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (c ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.LucasUnitAllPrimes

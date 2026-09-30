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

/-- `Φ_j` with `F((2j+1)N) = Φ_j(F N)` for odd `N`. -/
def fibOddPoly (x : ℤ) : ℕ → ℤ
  | 0 => x
  | 1 => 5 * x ^ 3 - 3 * x
  | j + 2 => (5 * x ^ 2 - 2) * fibOddPoly x (j + 1) - fibOddPoly x j

theorem fib_odd_mul (j : ℕ) {N : ℕ} (hN : Odd N) :
    (Nat.fib ((2 * j + 1) * N) : ℤ) = fibOddPoly (Nat.fib N) j := by
  sorry

theorem fibOddPoly_far {x : ℤ} (hx : x ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    fibOddPoly x j - x ≠ 0 ∧ fibOddPoly x j - x ≠ 2 ∧ fibOddPoly x j - x ≠ -2 := by
  sorry

theorem not_dvd_fib_prime_pow {c : ℕ} (hc : c.Prime) (h5 : c ≠ 5) (n : ℕ) :
    ¬ (c : ℤ) ∣ Nat.fib (c ^ n) := by
  sorry

/-- **`F(c^n) + h` is composite infinitely often, for every prime `c` and every integer `h`.** -/
theorem fib_prime_pow_add_not_prime_all {c : ℕ} (hc : c.Prime) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.FibonacciAllPrimes

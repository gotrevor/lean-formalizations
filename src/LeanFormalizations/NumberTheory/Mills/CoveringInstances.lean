/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.CoveringEngine
import LeanFormalizations.NumberTheory.Mills.LucasUnitAllPrimes

/-!
# Phase 43: prime-free intervals around `F(c^n)` for EVERY prime, and around `U_(c^n)(P, ±1)`

Completes Theorem C (`ROADMAP-PRIME-TOWERS.md`) for the binary families using the phase 41 engine.

## Route
1. `covering_of_good_finset`: a variant of `CoveringEngine.covering_of_good` /
   `prime_free_of_good` for an arbitrary finite set of shifts `S : Finset ℤ` in place of
   `{h : |h| ≤ H}`.  Refactor, or reprove by the same argument.
2. `fib_five_pow_prime_free`: for `h ∉ {1, −1}`, the good-prime hypothesis holds (window at
   one `n` ⟹ `F(5^n) + h ≡ ±1 (mod 5^(n/2))`, but `5^n ∣ F(5^n)`
   (`FibonacciPrimePow.five_pow_dvd_fib_five_pow`), so `h ≡ ±1`: impossible for large `n` when
   `h ≠ ±1`).  For `h = ±1`: `F(5^n) ± 1` is composite for all `n ≥ 2` by
   `F(4k+1) + 1 = F(2k+1) L(2k)`, `F(4k+1) − 1 = F(2k) L(2k+1)` (phase 34: `FibonacciPrimePow.fib_four_mul_add_one_add_one`,
   `fib_four_mul_add_one_sub_one`, `not_prime_of_mul`), with
   `5^n = 4k + 1`.  Combine: along the progression from step 1 (for `S = {|h| ≤ H} ∖ {±1}`),
   every `h` is non-prime.
3. `fib_prime_pow_prime_free_all`: every prime `c` (`c = 5` from step 2; else
   `CoveringEngine.fib_prime_pow_prime_free`).
4. `lucasU_unit_prime_pow_prime_free`: `Q = ±1`, `P² − 4Q ≥ 5`, odd prime `c ∤ D`.  Good-prime
   hypothesis as in phase 41's instances:
   - window at one `n` ⟹ `U(c^n) ≡ x (mod c^(n/2))`;
   - descend with `U(c^(k+2)) ≡ U(c^k) (mod c^(k+1))` (numerically checked, 156 cases; from
     `lucasU_odd_mul` with `2j + 1 = c²` and the LTE argument);
   - get `lucasOddPoly D Q x j ≡ x (mod c^(r−1))`;
   - `lucasOddPoly_far` bounds it unless `x = 0`, and `not_dvd_lucasU_prime_pow` excludes `x = 0`.

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.CoveringInstances

open LeanFormalizations.Mills.LucasTwoPow Filter

/-- **Prime-free intervals around `F(5^n)`.** -/
theorem fib_five_pow_prime_free (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + h) := by
  sorry

/-- **Prime-free intervals of every fixed length around `F(c^n)`, for EVERY prime `c`.** -/
theorem fib_prime_pow_prime_free_all {c : ℕ} (hc : c.Prime) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  sorry

/-- **Prime-free intervals around `U_(c^n)(P, ±1)`**, odd prime `c ∤ D`, `D = P² − 4Q ≥ 5`. -/
theorem lucasU_unit_prime_pow_prime_free {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1)
    (hD5 : 5 ≤ P ^ 2 - 4 * Q) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (lucasU P Q (c ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.CoveringInstances

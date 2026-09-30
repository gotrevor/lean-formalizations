/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasTwoPow

/-!
# Phase 34: `F(c^n) + h` is composite i.o. for every inert prime `c` and for `c = 5`

Generalizes phase 32 (Saito's Problem 1.8, `c = 2`) to the other primes `c`.  See
`SWEEP-PRIME-MODULUS.md`.

## Route (inert `c`, i.e. `c % 5 = 2 ∨ c % 5 = 3`; `c = 2` is included)
1. `fib_frobenius_inert`: `c ∣ F(c+1)` and `c ∣ F(c) + 1`.  These are the facts `A^(c+1) ≡ −I (mod c)`
   for `A = !![1,1;1,0]`.  Route: `X^2 − X − 1` is irreducible over `ZMod c` (5 is a non-residue:
   quadratic reciprocity, `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` or `legendreSym`
   lemmas; `c = 2` by `decide`), so in `K = AdjoinRoot` (a field with `c^2` elements) Frobenius
   sends the root `x` to the other root `1 − x = −x⁻¹`.  Hence `x^(c+1) = −1`, and the matrix
   statement follows through `F ∣` polynomial divisibility plus Cayley–Hamilton, as in phase 31
   `Projective.lean` (`dvd_trace_of_irreducible_mod`).  Any other correct route is fine.
2. `fib_prime_pow_succ_add`: `c^(n+1) ∣ F(c^(n+1)) + F(c^n)`.  Lift step 1:
   `A^(c+1) = −I + c·X` with `X` commuting with `A`, so `A^(c^n (c+1)) ≡ (−1)^(c^n) I (mod c^(n+1))`
   (binomial theorem, `c ∣ binom c i`).  Then take entry `(0,1)` and use
   `A^(−N)` entries (`F(−N) = (−1)^(N+1) F(N)`), or equivalently multiply through by `A^(c^n)`.
3. Filter: `SaitoFibonacci.exists_entry_pow_congr` with base `c`; the analogue of
   `two_pow_dvd_sub_or_add_of_lt_padicValNat` for an odd prime `c`:
   `v_c(p(p−1)^2(p+1)) = 2 v_c(p−1) + v_c(p+1)` and `c` divides at most one of `p ∓ 1`.
4. Contradiction as in phase 32: `s + s' ≡ 2h`; for odd `c` also `h = ±1` dies because
   `F(c^n) ≡ (−1)^n (mod c)` is a unit (from step 2 with `F(1) = 1`).  `h = 0`: `F(c^n) ∣ F(c^(n+1))`.

## Route (`c = 5`)
`5^n ∣ F(5^n)` (from `F(5m) = F(m)(25F(m)^4 ± 25F(m)^2 + 5)`, or any route), so the filter
leaves only `h = ±1`.  Those are killed by `F(4k+1) + 1 = F(2k+1) L(2k)` and
`F(4k+1) − 1 = F(2k) L(2k+1)` (`5^n ≡ 1 mod 4`), where both factors exceed 1 for large `k`.

Frozen: every statement below; statements of `SaitoFibonacci`, `LucasTwoPow`, `ThreeAdic`,
`SharedConjecture`, `Projective`, and `Literature/`.  Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.FibonacciPrimePow

open LeanFormalizations.Mills.ThreeAdic Filter

/-- Frobenius for Fibonacci at an inert prime: `A^(c+1) ≡ −I (mod c)`, entrywise. -/
theorem fib_frobenius_inert {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3) :
    (c : ℤ) ∣ Nat.fib (c + 1) ∧ (c : ℤ) ∣ (Nat.fib c : ℤ) + 1 := by
  sorry

/-- **The sign flip at an inert prime.** -/
theorem fib_prime_pow_succ_add {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ (Nat.fib (c ^ (n + 1)) : ℤ) + Nat.fib (c ^ n) := by
  sorry

/-- The filter's `c`-adic output for an odd prime `c`. -/
theorem pow_dvd_sub_or_add_of_lt_padicValNat {c p k : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hp : p.Prime) (hpc : p ≠ c) (hk : k < padicValNat c (glCard 2 p)) :
    (c : ℤ) ^ (k / 2) ∣ (p : ℤ) - 1 ∨ (c : ℤ) ^ (k / 2) ∣ (p : ℤ) + 1 := by
  sorry

/-- **`F(c^n) + h` is composite infinitely often, for every inert prime `c` and every `h`.** -/
theorem fib_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3)
    (h : ℤ) : ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  sorry

/-- `5^n ∣ F(5^n)`. -/
theorem five_pow_dvd_fib_five_pow (n : ℕ) : (5 : ℤ) ^ n ∣ Nat.fib (5 ^ n) := by
  sorry

/-- **`F(5^n) + h` is composite infinitely often, for every `h`.** -/
theorem fib_five_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.FibonacciPrimePow

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciAllPrimes

/-!
# Phase 40: prime-free intervals around `F(2^n)` — Dubickas's (D1) for a NON-reversible tower

Saito (arXiv:2504.14968) extends Dubickas's covering theorem (D1) and prime-free intervals (D2)
to compositions `R₀ ∘ R₁ ∘ ⋯` of linear recurrences, but only when the inner sequences are
**reversible**; `2^n` is not, and he writes *"We desire to remove the reversibility."*  This file
does it for Fibonacci along `2^n` (Theorem C of `ROADMAP-PRIME-TOWERS.md`):

  for every `H` there are `m`, `L ≥ 1` and primes `p_h` (`|h| ≤ H`) with
  `p_h ∣ F(2^(L k + m)) + h` for all `k`, hence `[F(2^n) − H, F(2^n) + H]` is prime-free for all
  large `n ≡ m (mod L)`.

Concrete instance (`scripts/fib-d1-demo.py`): `H = 6`, `m = 4`, `L = 60`, primes
`{2, 3, 23, 197, 983, 991}`.

## Route
1. `five_mul_fib_two_pow_sq`: `2^(n+1) ∣ 5 F(2^n)^2 + 3` for `n ≥ 1`.  From `5F(N)² = L(N)² − 4`
   (`N` even; Cassini / `LucasPrimePow.lucasL`) and `2^(n+1) ∣ L(2^n) + 1` (phase 32's
   `two_pow_dvd_lucas_two_pow_add_one`, or reprove).
2. `exists_good_prime_factor`: for `n` large relative to `|h|` (explicitly: `2^(n/2 − 1) > 5(|h|+1)² + 3`
   suffices), `F(2^n) + h` has a prime factor `p` with `padicValNat 2 (glCard 2 p) ≤ n`.
   Otherwise every prime factor `q` (odd, since `2` itself is good: `glCard 2 2 = 6`) satisfies
   `q ≡ ±1 (mod 2^(n/2))` (`two_pow_dvd_sub_or_add_of_lt_padicValNat`), so the product
   `F(2^n) + h ≡ ±1 (mod 2^(n/2))`; with step 1 this gives `2^(n/2) ∣ 5(h ∓ 1)² + 3`, too big.
3. `dvd_fib_two_pow_add_of_good`: a good prime `p ∣ F(2^m) + h` divides `F(2^(m + k j)) + h` for all
   `k`, for some `j ≥ 1`.  Strengthen `SaitoFibonacci.exists_entry_pow_congr`'s proof (it shows
   `D^(c^(m+j)) = D^(c^m)` over `ZMod p`; iterate).
4. `fib_two_pow_covering`: choose `m` large for all `|h| ≤ H` at once (step 2), `L = ∏ j_h` (or lcm).
5. `fib_two_pow_prime_free`: for `k ≥ 1`, `F(2^(Lk+m)) + h > p_h`, so it is not prime.

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.FibonacciCovering

open LeanFormalizations.Mills.ThreeAdic Filter

theorem five_mul_fib_two_pow_sq (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n + 1) ∣ 5 * (Nat.fib (2 ^ n) : ℤ) ^ 2 + 3 := by
  sorry

/-- A value near `F(2^n)` has a prime factor whose `GL₂` order has a small `2`-part. -/
theorem exists_good_prime_factor (h : ℤ) :
    ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (Nat.fib (2 ^ n) : ℤ) + h ∧
      padicValNat 2 (glCard 2 p) ≤ n := by
  sorry

/-- **(D1) for Fibonacci along the non-reversible tower `2^n`.** -/
theorem fib_two_pow_covering (H : ℕ) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h : ℤ, |h| ≤ H →
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ (Nat.fib (2 ^ (L * k + m)) : ℤ) + h := by
  sorry

/-- **Prime-free intervals of any fixed length around `F(2^n)`, infinitely often.** -/
theorem fib_two_pow_prime_free (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (2 ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.FibonacciCovering

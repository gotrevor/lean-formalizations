/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SharedConjecture

/-!
# Saito's Problem 1.8: `F(2^n) + h` is composite infinitely often (phase 32)

K. Saito, *Intervals without primes near an iterated linear recurrence sequence*,
arXiv:2504.14968, Problem 1.8: *"Let (F(n)) be the Fibonacci sequence.  Let h be an arbitrary
integer.  Prove or disprove that the numbers F(2^n) + h are composite for infinitely many n."*

We prove it for every `h`, unconditionally.  Full argument: `PROBE-SAITO-FIBONACCI.md`.

## Route
- **Odd `h`**: `fib_two_pow_odd`, so `F(2^n) + h` is even and eventually `> 2`.
- **`h = 0`**: `Nat.fib_dvd` gives `F(2^n) ∣ F(2^(n+1))`, with `1 < F(2^n) < F(2^(n+1))` for `n ≥ 2`.
- **Even `h ≠ 0`**: assume `p_n = F(2^n) + h` is prime for all `n ≥ n₀`.
  1. `exists_fib_two_pow_congr`: the phase-29/30 mechanism for the matrix `A = !![1,1;1,0]`,
     with `F(N) = (A^N) 0 1` (mathlib: `Matrix.fib`-style lemmas, or prove by induction).  Adapt
     the proof of `SharedConjecture.exists_trace_pow_congr`, which already shows
     `D^(c^(m+j)) = D^(c^m)` over `ZMod p`; read off entry `(0,1)` instead of the trace.
     `det A = -1`, so `p ∤ det A` is free.
  2. Hence (as in `lt_padicValNat_glCard_prime_base`) `n < padicValNat 2 (glCard 2 p_n)` for all
     large `n`: otherwise `p_n ∣ p_(n+j)` with `p_(n+j) > p_n` prime.
  3. `two_pow_dvd_sub_or_add_of_lt_padicValNat`: `glCard 2 p = (p^2-1)(p^2-p) = p(p-1)^2(p+1)`,
     and for odd `p` one of `v₂(p-1)`, `v₂(p+1)` is `1`, so `p ≡ ±1 (mod 2^(n/2))`.
  4. `two_pow_dvd_fib_two_pow_succ_add`: `F(2^(n+1)) + F(2^n) = F(2^n)(L(2^n)+1)` where
     `L(m) = 2F(m+1) - F(m)` (from `Nat.fib_two_mul`), and `v₂(L(2^n)+1) ≥ n+1` by induction via
     `L(2^(n+1)) + 1 = (L(2^n) - 1)(L(2^n) + 1)`, `L(2^n) - 1 ≡ 2 (mod 4)`.  Work in `ℤ`.
  5. Add steps 3 at `n` and `n+1`, use step 4: `s + s' ≡ 2h (mod 2^(n/2))`, `s, s' ∈ {±1}`.
     `h` even ⟹ `s + s' = 0` (as `±2 ≢ 0 mod 4`) ⟹ `2^(n/2) ∣ 2h` for all large `n` ⟹ `h = 0`.

Frozen: every statement below, everything in `ThreeAdic.lean`, `SharedConjecture.lean`,
`Projective.lean`, and all of `Literature/`.  Helper lemmas may be added freely (private or not).
-/

namespace LeanFormalizations.Mills.SaitoFibonacci

open LeanFormalizations.Mills.ThreeAdic Filter

/-- `F(2^n)` is odd for every `n`. -/
theorem fib_two_pow_odd (n : ℕ) : Odd (Nat.fib (2 ^ n)) := by
  sorry

/-- **The sign flip.**  `F(2^(n+1)) ≡ -F(2^n) (mod 2^(n+1))` for `n ≥ 1`. -/
theorem two_pow_dvd_fib_two_pow_succ_add (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n + 1) ∣ (Nat.fib (2 ^ (n + 1)) : ℤ) + Nat.fib (2 ^ n) := by
  sorry

/-- **The mechanism** (prime as modulus): if `v₂|GL₂(𝔽_p)| ≤ m`, the sequence `F(2^k) mod p`
returns to `F(2^m) mod p`. -/
theorem exists_fib_two_pow_congr {p m : ℕ} (hp : p.Prime)
    (hv : padicValNat 2 (glCard 2 p) ≤ m) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (Nat.fib (2 ^ (m + j)) : ℤ) - Nat.fib (2 ^ m) := by
  sorry

/-- A large `2`-part of `|GL₂(𝔽_p)|` forces `p ≡ ±1` modulo a large power of `2`. -/
theorem two_pow_dvd_sub_or_add_of_lt_padicValNat {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : k < padicValNat 2 (glCard 2 p)) :
    (2 : ℤ) ^ (k / 2) ∣ (p : ℤ) - 1 ∨ (2 : ℤ) ^ (k / 2) ∣ (p : ℤ) + 1 := by
  sorry

/-- **Saito's Problem 1.8 (arXiv:2504.14968), answered.**  For every integer `h`, `F(2^n) + h`
is not prime for infinitely many `n`. -/
theorem fib_two_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (2 ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.SaitoFibonacci

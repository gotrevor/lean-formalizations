/-
# Mills' theorem, conditional on primes between consecutive cubes

W. H. Mills, *A prime-representing function*, Bull. Amer. Math. Soc. **53** (1947), 604:
there is a real `A > 1` with `⌊A^(3^n)⌋` prime for every `n ≥ 1`.

Mills' proof has two halves:

* an **analytic input**: for all sufficiently large `n` there is a prime strictly between `n³`
  and `(n+1)³` (Ingham 1937; explicitly for `n ≥ exp(exp(33.3))`, Dudek 2016);
* an **elementary nested-interval construction** turning that input into `A`.

This file does the second half, with the analytic input as an explicit hypothesis
`PrimeBetweenCubesFrom N`.  Nothing here proves Ingham's theorem, so the headline
`exists_mills_of_primeBetweenCubes` is **conditional**.

## Faithfulness

`IsMills` and `IsMinMills` are copied verbatim from google-deepmind/formal-conjectures,
`FormalConjectures/Wikipedia/Mills.lean` (`Mills.IsMills`, `Mills.IsMinMills`), so a
discharge of the hypothesis closes their `Mills.exists'` and `Mills.exists_least` as stated.

## Proof plan (the construction)

Pick a prime `p₀ ≥ max N 2` (`Nat.exists_infinite_primes`) and define `p (k+1)` as a prime
strictly between `(p k)³` and `(p k + 1)³` (the hypothesis, applied at `p k ≥ N`).  Then:

1. `(p k + 1)³ − 1 = p k · ((p k)² + 3 p k + 3)` is composite, so `p (k+1) + 1 < (p k + 1)³`.
2. `u k = (p k) ^ (3⁻ᵏ)` is monotone, `v k = (p k + 1) ^ (3⁻ᵏ)` is strictly antitone, and
   `u k < v k`.
3. `A = ⨆ k, u k` satisfies `p k ≤ A^(3^k) < p k + 1`, so `⌊A^(3^k)⌋₊ = p k`.
4. Re-index: `IsMills` quantifies over `n : ℕ+` with exponent `3^n`, so use `A` built from a
   sequence whose `k = 0` term is chosen so that the `n ≥ 1` terms are the primes.  (Either
   start the chain at `p 0` and take `A := ⨆ k, u k` with `⌊A^(3^n)⌋₊ = p n`, `n ≥ 1`, or
   shift; `A > 1` because `A ≥ u 0 = p 0 ≥ 2`.)

The **least** Mills number (`exists_least_of_exists`) is unconditional given one Mills number:
each constraint `⌊A^(3^n)⌋₊ = p` cuts out a left-closed interval `[p^(3⁻ⁿ), (p+1)^(3⁻ⁿ))`,
so the set `{A > 1 | IsMills A}` is closed under limits of antitone sequences, and it is
bounded below by `2^(1/3)`.  Take the infimum and show it is attained.
-/
import Mathlib

namespace LeanFormalizations.Mills

/-- **Verbatim from formal-conjectures** `Mills.IsMills`: `⌊A^(3^n)⌋₊` is prime for every
positive `n`. -/
abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊

/-- **Verbatim from formal-conjectures** `Mills.IsMinMills`: `A` is the least Mills number. -/
abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

/-- The analytic input to Mills' theorem: from `N` on, every gap between consecutive cubes
contains a prime.  True for some `N` by Ingham (1937); Dudek (2016) makes `N` explicit. -/
def PrimeBetweenCubesFrom (N : ℕ) : Prop :=
  ∀ n ≥ N, ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3

/-- Step 1 of the plan: a prime below `(n+1)³` is at most `(n+1)³ − 2`, because
`(n+1)³ − 1 = n (n² + 3n + 3)` is composite for `n ≥ 2`. -/
theorem prime_add_one_lt_cube {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hlt : p < (n + 1) ^ 3) :
    p + 1 < (n + 1) ^ 3 := by
  sorry

/-- **Mills' theorem, conditional on primes between consecutive cubes.** -/
theorem exists_mills_of_primeBetweenCubes {N : ℕ} (h : PrimeBetweenCubesFrom N) :
    ∃ A > 1, IsMills A := by
  sorry

/-- **The least Mills number exists** as soon as one Mills number does.  Unconditional. -/
theorem exists_least_of_exists (h : ∃ A > 1, IsMills A) : ∃ A, IsMinMills A := by
  sorry

/-- **Mills' constant exists, conditional on primes between consecutive cubes.** -/
theorem exists_least_of_primeBetweenCubes {N : ℕ} (h : PrimeBetweenCubesFrom N) :
    ∃ A, IsMinMills A :=
  exists_least_of_exists (exists_mills_of_primeBetweenCubes h)

end LeanFormalizations.Mills

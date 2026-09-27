/-
# Wright's prime-representing power tower

E. M. Wright, *A prime-representing function*, Amer. Math. Monthly **58** (1951), 616–618:
there is a real `ω` such that, with `g 0 = ω` and `g (n+1) = 2 ^ g n`,
`⌊g n⌋` is prime for every `n ≥ 1`.  (`ω ≈ 1.9287800`, OEIS A086238.)

Unlike Mills' theorem this is **unconditional from Bertrand's postulate**
(`Nat.exists_prime_lt_and_le_two_mul`), which mathlib already has.

## Proof plan

Build primes `q 1 < q 2 < …` with `2 ^ q k < q (k+1) < 2 ^ (q k + 1)`: Bertrand at
`m = 2 ^ q k` gives a prime in `(m, 2m]`, and `2m = 2^(q k + 1)` is not prime once
`q k ≥ 1`, so the upper inequality is strict.  Pull the intervals back through the tower:
`log₂` applied `k` times to `[q k, q k + 1)` gives nested intervals `[a k, b k)` in `ω`-space
(`a` monotone, `b` antitone — this is where `2 ^ q k < q (k+1)` and `q (k+1) + 1 ≤ 2^(q k + 1)`
are used).  Take `ω := ⨆ k, a k`; then `q k ≤ tower ω k < q k + 1`.  Commit a helper for the
inverse tower (`iterate Real.logb 2`) and its monotonicity before the limit argument.
-/
import Mathlib

namespace LeanFormalizations.Mills

/-- The power tower `2^2^…^2^ω` with `n` twos. -/
noncomputable def tower (ω : ℝ) : ℕ → ℝ
  | 0 => ω
  | n + 1 => (2 : ℝ) ^ tower ω n

/-- **Wright's theorem (1951).**  Some `ω` makes every tower `2^2^…^2^ω` with at least one `2`
have prime floor. -/
theorem wright : ∃ ω : ℝ, ∀ n : ℕ, 1 ≤ n → (⌊tower ω n⌋₊).Prime := by
  sorry

end LeanFormalizations.Mills

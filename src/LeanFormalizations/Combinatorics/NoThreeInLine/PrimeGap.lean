/-
# Prime-gap input to the HJSW lower bound — sharpening the general-`N` constant

The HJSW construction `shearSel p` gives `3(p−1)` no-three-collinear points inside `[0,2p)²`, so for
any prime `p` with `2p ≤ N` we get `3(p−1) ≤ maxNoThreeInLine N`
(`maxNoThreeInLine_ge_of_two_mul_prime_le`, the *prime-gap interface*). The general-`N` lower constant
is therefore exactly `3/2 · (largest prime ≤ N/2)/(N/2)` — pinned by **how close to `N/2` we can
guarantee a prime**:

* **Bertrand** (`Nat.exists_prime_lt_and_le_two_mul`, in mathlib): a prime in `(N/4, N/2]` ⟹ constant
  `3/4` (`maxNoThreeInLine_ge_three_quarters`).
* **Nagura 1952** (`nagura_prime` below): a prime in `(n, 6n/5]` for `n ≥ 25` ⟹ constant `5/4`
  (`maxNoThreeInLine_ge_five_fourths`).
* **PNT-strength gaps** (prime in `((1−ε)N/2, N/2]`): the full `3/2 − o(1)`, matching `hjsw_lower_bound`
  at the natural sizes `N = 2p` for *all* large `N`.

`nagura_prime` is the **active frontier crux** of this thread: it is *proven mathematics* (Nagura
1952), so it is honest 🟡 debt, not an open conjecture — but mathlib lacks the prerequisite (a
Chebyshev **lower** bound `c·x ≤ θ x`; it has only the upper bound `theta_le_log4_mul_x` and the
primorial bound `primorial_le_four_pow`). It is left as a disclosed `sorry` and is the cross-lap
target; the payoff `maxNoThreeInLine_ge_five_fourths` is wired and ready. See `PENDING_WORK.md` for the
central-binomial attack plan. The repo's **headline** theorems (`hjsw_lower_bound`,
`maxNoThreeInLine_bounds`, …) do not depend on this file and remain axiom-clean.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Statement

namespace LeanFormalizations.NoThreeInLine

/-- **Nagura's theorem (1952).** For every `n ≥ 25` there is a prime `p` in the interval `(n, 6n/5]`
(i.e. `n < p` and `5p ≤ 6n`). This sharpens Bertrand's postulate (`p ≤ 2n`) to ratio `6/5`.

**Status: disclosed `sorry` — the active frontier crux of the HJSW general-`N` thread.** This is a
*theorem* (proven by Nagura in 1952), not a conjecture; it is 🟡 debt, formalizable but gated on
infrastructure mathlib does not yet provide.

**Attack plan** (mirrors mathlib's `Nat.exists_prime_lt_and_le_two_mul`, sharpened):
* Lower bound on the central binomial: `4^n ≤ n · C(2n,n)` (`Nat.four_pow_lt_mul_centralBinom`).
* If there were **no** prime in `(n, 6n/5]`, the primes `> n` dividing `C(2n,n)` lie in `(6n/5, 2n]`,
  so by `centralBinom_factorization_small`-style bounds plus `primorial_le_four_pow` the coefficient is
  bounded above by `(2n)^√(2n) · 4^(6n/5) · (contribution of (6n/5,2n])`.
* The missing ingredient vs. Bertrand: one must *lower-bound* the prime mass in `(6n/5, 2n]` — i.e. a
  Chebyshev lower bound `θ(x) ≥ c·x` (equivalently `ψ(x) ≥ log C(2n,n) ≥ n·log 4 − log n` via
  `C(2n,n) ≤ ∏_{p^k ≤ 2n} p = exp(ψ(2n))`). mathlib has the upper Chebyshev bound only.
* Small `n ∈ [25, N₀)` are discharged by an explicit descending prime list (as in Bertrand's small
  cases). Submitted to Aristotle as a self-contained job. -/
theorem nagura_prime {n : ℕ} (hn : 25 ≤ n) : ∃ p, p.Prime ∧ n < p ∧ 5 * p ≤ 6 * n := by
  sorry

/-- **HJSW general-`N` lower bound at constant `5/4`** (conditional on `nagura_prime`). For `N ≥ 60`,
applying Nagura at `n = ⌊5N/12⌋` yields a prime `p ∈ (⌊5N/12⌋, N/2]`, whose sheared construction gives
`3(p−1) ≥ 3⌊5N/12⌋ ≈ 5N/4` points. This is the `5/4` rung between Bertrand's `3/4`
(`maxNoThreeInLine_ge_three_quarters`) and the conjectural `3/2 − o(1)`.

The conclusion is stated in the exact floor form `3·⌊5N/12⌋` (asymptotically `5N/4`), paralleling the
`3·⌊N/4⌋ = 3·⌊3N/12⌋` form of the Bertrand bound: the improvement `3/12 → 5/12` of the inner
coefficient is the constant `3/4 → 5/4`. -/
theorem maxNoThreeInLine_ge_five_fourths {N : ℕ} (hN : 60 ≤ N) :
    3 * (5 * N / 12) ≤ maxNoThreeInLine N := by
  obtain ⟨p, hp, hlo, hhi⟩ := nagura_prime (n := 5 * N / 12) (by omega)
  have h2p : 2 * p ≤ N := by omega
  have := maxNoThreeInLine_ge_of_two_mul_prime_le hp h2p
  omega

end LeanFormalizations.NoThreeInLine

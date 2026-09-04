/-
# N5 — the arithmetic place: `d_n = lcm(1,…,n) ≤ exp(1.01 n)` eventually

Mathlib already supplies `Chebyshev.psi_eq_log_lcmUpto : ψ n = log (lcmUpto n)`, and the in-repo
`PrimeNumberTheoremAnd` dependency supplies `WeakPNT'' : ψ ~[atTop] id`.  Together:
`log d_n / n → 1`, hence `d_n ≤ e^{1.01 n}` eventually.  No prime-by-prime accounting, no `Φ_n`
saving — the elementary route pays full price for the denominators and still closes, because the
real place gives `-21.657` against `21`.

`1.01` is arbitrary in `(1, 21.3/21) = (1, 1.0142…)`; see `Bound.lean` for the ledger arithmetic.
-/
import Mathlib
import PrimeNumberTheoremAnd.Consequences
import LeanFormalizations.NumberTheory.DirichletBeta.LinearForm

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- **N5 (denominator growth).**  `lcm(1,…,n) ≤ e^{1.01 n}` for all large `n`. -/
theorem dn_le_exp : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (dn n : ℝ) ≤ Real.exp (1.01 * n) := by
  sorry

end LeanFormalizations.DirichletBeta

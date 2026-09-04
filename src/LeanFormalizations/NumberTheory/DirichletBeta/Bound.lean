/-
# N4 — the real-place bound: `|r_21,n| ≤ exp(-21.3 n)` eventually

The elementary route (no saddle point, no Nesterenko criterion): bound `|r_n|` by
`poly(n) · max_u |R_n(n+1+u-½)|` — legitimate here because the ledger probe shows the **max-term
rate equals the exact rate**, i.e. the alternating sum loses nothing to cancellation — then bound
the peak term by explicit factorial/Stirling inequalities.

The true rate at `s = 21` is `lim |r_n|^{1/n} = e^{-21.657}`
(`papers/catalan-beta-ledger.py`: `logL = -21.657`, with the measured `log|r_n|/n = -22.514` at
`n = 40`, approaching `-21.657` from below).  The constant frozen below is **`-21.3`**, leaving
`0.357/n` of slack against the true rate — deliberately loose, so a coarse Stirling bound suffices.

Ledger arithmetic that this constant must satisfy, together with `Lcm.lean`'s `1.01`:

    21 · 1.01 = 21.21  <  21.3.

⚠️ Do **not** tighten `-21.3` toward `-21.657`; the margin is the whole point, and any constant in
`(-21.657, -21.21)` closes the proof.
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Rational

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- **N4 (real-place bound).**  At `s = 21`, `|r_n| ≤ e^{-21.3 n}` for all large even `n`. -/
theorem abs_rForm_le_exp :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → |rForm 21 n| ≤ Real.exp (-21.3 * n) := by
  sorry

end LeanFormalizations.DirichletBeta

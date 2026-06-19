/-
# Hall–Jackson–Sudbery–Wild `3N/2` lower bound — FRONTIER (in progress)

The best *proven* lower bound for the no-three-in-line problem (1975), unimproved since.
Improves Erdős's `~N` parabola to `3(N−2)/2` via the hyperbola `x·y ≡ k (mod p)`.

**This file is the active treadmill target.** The headline below is a `sorry` placeholder so the
`--allow-stop` sorry-gate stays CLOSED until HJSW is genuinely proven. Discharge it (and surface
the faithful headline in `Statement.lean`) to complete the frontier; see `PLAN.md` and `HANDOFF.md`.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.UpperBound
import LeanFormalizations.Combinatorics.NoThreeInLine.Parabola

namespace LeanFormalizations.NoThreeInLine

/-- **HJSW lower bound (TARGET — not yet proven).** For prime `p`, the `2p × 2p` grid admits
`3(p−1)` points with no three collinear — the hyperbola `x·y ≡ k (mod p)` construction, i.e. the
`3(n−2)/2` count with `n = 2p` (since `3(2p−2)/2 = 3(p−1)`).

⚠️ VERIFY this exact constant and form against Hall–Jackson–Sudbery–Wild (1975) before/while
proving, and **refine the statement here if the faithful count differs** — the statement is the
entire trust surface. The non-collinearity proof reuses `collinear_imp_det3_zero` + "`ZMod p` is a
domain" (as in `Parabola.lean`); the `3/2` covering count is the real work. -/
theorem hjsw_lower {p : ℕ} (hp : p.Prime) : 3 * (p - 1) ≤ maxNoThreeInLine (2 * p) := by
  sorry

end LeanFormalizations.NoThreeInLine

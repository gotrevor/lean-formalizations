/-
# Goodstein's theorem: every Goodstein sequence terminates — Goodstein (1944)

**Designated audit surface** (with `Defs.lean` and `Anchors.lean`). The proof
engine lives in sibling files; this statement delegates.

## What this says
For every starting value `m`, the Goodstein sequence seeded at `m` (see `Defs.lean`)
eventually reaches `0`. Despite the early astronomical growth (the `m = 4` sequence
peaks around `3·2^402653211` before descending), it always terminates.

## Proof (positive theorem, provable here)
Map each term `G k`, written in hereditary base `k+2`, to an ordinal by replacing
the base `k+2` with `ω`. The base-bump `k+2 ↦ k+3` leaves this ordinal unchanged
(it is `ω` regardless of base); the subtract-one strictly decreases it. So the
ordinal sequence is strictly decreasing, and `Ordinal` is well-founded
(`Ordinal.wellFoundedLT`) — no infinite descent — so it must reach `0`, forcing
`G k = 0`. mathlib supplies the Cantor-normal-form machinery
(`Ordinal.CNF`, `Ordinal.coeff`/`Ordinal.eval`) and well-foundedness.

## Scope — POSITIVE theorem only
This is Goodstein's theorem proper (true; provable in ZFC, hence trivially in
Lean's stronger logic). The **Kirby–Paris independence result** — that Peano
Arithmetic cannot prove this theorem (Kirby & Paris 1982, via `Goodstein ⟹ Con(PA)`
+ Gödel II) — is a *metamathematical* statement about PA and is explicitly OUT OF
SCOPE. See `README.md`.
-/
import LeanFormalizations.Logic.Goodstein.Defs
import LeanFormalizations.Logic.Goodstein.Anchors
import LeanFormalizations.Logic.Goodstein.Engine

namespace LeanFormalizations.Logic.Goodstein

/-- **Goodstein's theorem.** For every starting value `m`, the Goodstein sequence
seeded at `m` eventually reaches `0`. (The ordinal-descent proof lives in
`Engine.lean`; this is the thin, faithful audit statement.) -/
theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0 :=
  goodstein_terminates_engine m

end LeanFormalizations.Logic.Goodstein

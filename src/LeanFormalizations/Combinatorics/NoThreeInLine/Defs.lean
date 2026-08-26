/-
# No-three-in-line problem — core definitions

The no-three-in-line problem (Dudeney 1917; Ben Green's open problem 72): how many
points can be placed on an `N × N` grid so that no three are collinear?

This file fixes the faithful definitions that the headline theorems are stated against.
A grid point is a pair `(i, j) : ℕ × ℕ`; collinearity is the genuine geometric notion
`Collinear ℝ` over the real plane (via `toReal`), so "no three in line" means no three
*distinct* grid points lie on a common real line — every line of every rational slope,
not just rows/columns/diagonals.

This is the audited definition. It agrees with the `formal-conjectures` entry
`Green72.AllowedSet` (stated there for general `k`; ours is the `k = 3` instance).
An early revision of that entry stated `not_collinear` without its negation; upstream
fixed it in google-deepmind/formal-conjectures#4182 (2026-06-12).
-/
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Real.Basic

namespace LeanFormalizations.NoThreeInLine

/-- Embed a grid point `(i, j) : ℕ × ℕ` into the real plane `ℝ × ℝ`. -/
def toReal (p : ℕ × ℕ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

/-- `s` lies inside the `N × N` grid `[0, N) × [0, N)`. -/
def IsGridSet (N : ℕ) (s : Finset (ℕ × ℕ)) : Prop := ∀ p ∈ s, p.1 < N ∧ p.2 < N

/-- A set in the `N × N` grid also sits in any larger `M × M` grid. -/
theorem IsGridSet.mono {N M : ℕ} {s : Finset (ℕ × ℕ)} (h : IsGridSet N s) (hNM : N ≤ M) :
    IsGridSet M s :=
  fun p hp => ⟨(h p hp).1.trans_le hNM, (h p hp).2.trans_le hNM⟩

/-- **No three distinct points of `s` are collinear.** Any collinear triple drawn
from `s` must repeat a point — equivalently, no three pairwise-distinct points of `s`
lie on a common real line. -/
def NoThreeCollinear (s : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s,
    Collinear ℝ ({toReal p, toReal q, toReal r} : Set (ℝ × ℝ)) →
      p = q ∨ p = r ∨ q = r

/-- The maximum number of points placeable in the `N × N` grid with no three collinear.
(The defining set is bounded above by `2 * N`, see `UpperBound.lean`, so this `sSup` is
attained.) -/
noncomputable def maxNoThreeInLine (N : ℕ) : ℕ :=
  sSup {n | ∃ s : Finset (ℕ × ℕ), n = s.card ∧ IsGridSet N s ∧ NoThreeCollinear s}

end LeanFormalizations.NoThreeInLine

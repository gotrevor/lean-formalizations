/-
# Anti-vacuity anchors for the no-three-in-line definitions

The headline theorems are stated against `Collinear ℝ` (via `toReal`). A faithful audit must rule
out the two ways such a definition could be silently vacuous:

* `Collinear ℝ` could be **always false** on grid points — then `NoThreeCollinear` would hold
  trivially. Refuted by `collinear_diagonal`: three real grid points genuinely *are* collinear.
* `Collinear ℝ` could be **always true** — then no nonempty set would satisfy `NoThreeCollinear`.
  Refuted by `not_collinear_corner` (a genuine non-collinear triple) together with
  `Parabola.parabola_noThreeCollinear` (a proven nonempty no-three-collinear family).

Together with the exact criterion `collinear_iff_det3_zero`, these pin the predicate to its
intended geometric meaning. They are tiny `norm_num` computations on explicit points — concrete
witnesses in the spirit of the other modules' `Anchors.lean`.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.Collinearity

namespace LeanFormalizations.NoThreeInLine

/-- Three grid points on the main diagonal genuinely *are* collinear: `Collinear ℝ` fires, so
`NoThreeCollinear` is not vacuously true. -/
theorem collinear_diagonal :
    Collinear ℝ ({toReal (0, 0), toReal (1, 1), toReal (2, 2)} : Set (ℝ × ℝ)) := by
  apply det3_zero_imp_collinear
  norm_num [det3, toReal]

/-- A right-angle corner triple is *not* collinear: `Collinear ℝ` is not always true, so
`NoThreeCollinear` is a genuine constraint (not unsatisfiable). -/
theorem not_collinear_corner :
    ¬ Collinear ℝ ({toReal (0, 0), toReal (1, 0), toReal (0, 1)} : Set (ℝ × ℝ)) := by
  intro h
  have hd := collinear_imp_det3_zero h
  norm_num [det3, toReal] at hd

end LeanFormalizations.NoThreeInLine

/-
# Planar Kakeya set conjecture (Davies 1971) — audit surface

This is the faithful **audit surface** for the formalization. To check faithfulness, read
exactly two things against the literature:

* the definitions `IsKakeya` and `KakeyaSetConjectureDim` in `Defs.lean` — these mirror
  `google-deepmind/formal-conjectures`' `FormalConjectures/Wikipedia/Kakeya.lean` verbatim;
* the headline `davies_kakeya_2d` below, which states exactly `KakeyaSetConjectureDim 2`.

The proof delegates to `Engine.lean`:

* `dimH_le_two` (the `≤ 2` half) is **proven** and axiom-clean;
* `two_le_dimH` (the `≥ 2` half — Davies' actual theorem) is the open crux of this run.

Reference: R. O. Davies, *Some remarks on the Kakeya problem*, Math. Proc. Cambridge
Philos. Soc. **69** (1971), 417–421.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Wiring

namespace LeanFormalizations.Kakeya2D

/-- **The planar Kakeya set conjecture (Davies 1971).** Every Kakeya set in `ℝ²` — a set
containing a unit line segment in every direction — has Hausdorff dimension `2`. -/
theorem davies_kakeya_2d : KakeyaSetConjectureDim 2 := by
  intro S h
  exact le_antisymm (dimH_le_two S) (two_le_dimH S h)

end LeanFormalizations.Kakeya2D

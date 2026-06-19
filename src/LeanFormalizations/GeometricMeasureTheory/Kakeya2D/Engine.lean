/-
# Davies' theorem — proof engine (planar Kakeya dimension)

The headline `dimH S = 2` splits into the two inequalities:

* `dimH_le_two` — the **trivial** half: any subset of `ℝ²` has Hausdorff dimension `≤ 2`,
  by monotonicity into `univ`, whose dimension is `finrank ℝ (ℝ²) = 2`. **Proven.**
* `two_le_dimH` — **Davies 1971**, the genuine content: a planar Kakeya set has Hausdorff
  dimension `≥ 2`. This is the run's open crux (`sorry`). Strategy: Córdoba's dual / "bush"
  `L²` argument — see `PLAN.md`.

Only `two_le_dimH` uses `IsKakeya`; the upper bound holds for every set in the plane.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Defs

open Set MeasureTheory

namespace LeanFormalizations.Kakeya2D

/-- The trivial upper bound: every subset of the plane has Hausdorff dimension at most `2`.
(Holds for any set, Kakeya or not — `dimH` is monotone and `dimH (univ : Set ℝ²) = 2`.) -/
theorem dimH_le_two (S : Set (EuclideanSpace ℝ (Fin 2))) : dimH S ≤ 2 := by
  have huniv : dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) = 2 := by
    simp [Real.dimH_univ_eq_finrank]
  calc dimH S ≤ dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) := dimH_mono (subset_univ S)
    _ = 2 := huniv

/-- **Davies 1971.** A Kakeya set in `ℝ²` has Hausdorff dimension at least `2`.

This is the genuine content of the planar Kakeya set conjecture (the upper bound is free).
Open crux of this run; see `PLAN.md` for the Córdoba bush/`L²` strategy. -/
theorem two_le_dimH (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    2 ≤ dimH S := by
  sorry

end LeanFormalizations.Kakeya2D

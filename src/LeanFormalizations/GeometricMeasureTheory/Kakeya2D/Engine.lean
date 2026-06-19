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
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Frostman
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open Set MeasureTheory
open scoped NNReal ENNReal

namespace LeanFormalizations.Kakeya2D

/-- The trivial upper bound: every subset of the plane has Hausdorff dimension at most `2`.
(Holds for any set, Kakeya or not — `dimH` is monotone and `dimH (univ : Set ℝ²) = 2`.) -/
theorem dimH_le_two (S : Set (EuclideanSpace ℝ (Fin 2))) : dimH S ≤ 2 := by
  have huniv : dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) = 2 := by
    simp [Real.dimH_univ_eq_finrank]
  calc dimH S ≤ dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) := dimH_mono (subset_univ S)
    _ = 2 := huniv

/-- **The concrete crux (Davies 1971, measure form).** For a Kakeya set `S ⊆ ℝ²`, every
`d`-dimensional Hausdorff measure with `d < 2` is *positive*: `μH[d] S ≠ 0`.

This is the genuine analytic content; `two_le_dimH` is a free `ℝ≥0∞`-density wrapper around it.
The route to discharge it is the Córdoba `L²`/bush argument (`PLAN.md`, ladder K2–K5):
δ-tube overlap bound ⟹ Minkowski-content lower bound `vol(Sδ) ≳ 1/log(1/δ)` ⟹ a Frostman
measure witnessing `μH[d] S > 0` for every `d < 2`.

**Status (this run).** K2–K4 are **proven, axiom-clean**: the content bound
`vol(Sδ) ≳ 1/log(1/δ)` is `volume_thickening_log_ge`. K5 brick 1 (`hausdorffMeasure_ne_zero_of_frostmanExists`,
`Frostman.lean`) reduces this crux to **constructing a Frostman measure** of every exponent `d < 2`
on `S` (`FrostmanMeasureExists S d`) — done below via that wrapper. The lone remaining `sorry` is
now exactly that measure construction (the dyadic mass-distribution limit fed by K4), not the raw
Hausdorff statement. -/
theorem hausdorffMeasure_pos_of_isKakeya
    (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    ∀ d : ℝ≥0, (d : ℝ≥0∞) < 2 → μH[(d : ℝ)] S ≠ 0 := by
  intro d _
  refine hausdorffMeasure_ne_zero_of_frostmanExists (S := S) (d := (d : ℝ)) ?_
  -- **The remaining deep obligation (K5 core):** build the Frostman measure of exponent `d` on the
  -- Kakeya set from the K4 content bound, by distributing mass over the δ-tube family across dyadic
  -- scales. See `PLAN.md` / `PENDING_WORK.md`.
  sorry

/-- **Davies 1971.** A Kakeya set in `ℝ²` has Hausdorff dimension at least `2`.

This is the genuine content of the planar Kakeya set conjecture (the upper bound is free).
Reduced (K1, axiom-clean) to the measure-positivity crux `hausdorffMeasure_pos_of_isKakeya`:
Frostman's lemma `le_dimH_of_hausdorffMeasure_ne_zero` lifts each `μH[d] S ≠ 0` (with `d < 2`)
to `↑d ≤ dimH S`, and `ENNReal.le_of_forall_nnreal_lt` pushes the supremum over `d < 2` up to `2`. -/
theorem two_le_dimH (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    2 ≤ dimH S := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  exact le_dimH_of_hausdorffMeasure_ne_zero (hausdorffMeasure_pos_of_isKakeya S h r hr)

end LeanFormalizations.Kakeya2D

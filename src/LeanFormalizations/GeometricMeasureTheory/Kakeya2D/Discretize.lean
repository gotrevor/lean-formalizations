/-
# δ-discretization of a planar Kakeya set (ladder K3)

A Kakeya set `S` contains a unit segment in *every* direction. δ-thickening turns each such
segment into a δ-tube; this file establishes the bridge

  `IsKakeya S` ⟹ for every unit direction `v`, some δ-tube in direction `v` lies in `Sδ`,

where `Sδ := cthickening δ S` is the closed δ-neighbourhood. This is what lets the Córdoba `L²`
overlap estimate (K4) be run against `Sδ`: it contains a δ-tube of *every* direction, with the
two-tube overlaps controlled by `volume_inter_tube_le` (K2, done). The `δ`-net of directions on
the unit circle (compactness) then gives a finite family of `~δ⁻¹` tubes inside `Sδ`.

Reference: A. Córdoba (1977); R. O. Davies (1971). See `PLAN.md`.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Tube

open Set MeasureTheory Metric

namespace LeanFormalizations.Kakeya2D

/-- The closed **δ-neighbourhood** of a set `S` in the plane (`Sδ`). The δ-discretization lives
here: it is a *fattened* version of the (possibly measure-zero) Kakeya set whose Lebesgue area
the Córdoba argument lower-bounds. -/
def thickening (S : Set Plane) (δ : ℝ) : Set Plane := Metric.cthickening δ S

@[simp] theorem thickening_def (S : Set Plane) (δ : ℝ) :
    thickening S δ = Metric.cthickening δ S := rfl

theorem isClosed_thickening (S : Set Plane) (δ : ℝ) : IsClosed (thickening S δ) :=
  isClosed_cthickening

theorem measurableSet_thickening (S : Set Plane) (δ : ℝ) : MeasurableSet (thickening S δ) :=
  (isClosed_thickening S δ).measurableSet

theorem subset_thickening (S : Set Plane) (δ : ℝ) : S ⊆ thickening S δ :=
  self_subset_cthickening _

/-- **A core segment in `S` thickens to a δ-tube in `Sδ`.** If the segment `[a, a+v]` lies in `S`,
then the whole δ-tube about it lies in the δ-neighbourhood `Sδ`. -/
theorem tube_subset_thickening {S : Set Plane} {a v : Plane} {δ : ℝ}
    (h : affineSegment ℝ a (a + v) ⊆ S) : tube a v δ ⊆ thickening S δ :=
  cthickening_subset_of_subset δ h

/-- **K3 selection.** For a Kakeya set `S` and *every* unit direction `v`, there is a base point
`a` whose δ-tube lies in the δ-neighbourhood `Sδ`. So `Sδ` contains a δ-tube of every direction —
exactly the hypothesis the Córdoba `L²` estimate consumes. -/
theorem exists_tube_subset_thickening {S : Set Plane} (h : IsKakeya S) {δ : ℝ}
    (v : Plane) (hv : ‖v‖ = 1) : ∃ a, tube a v δ ⊆ thickening S δ := by
  obtain ⟨a, ha⟩ := h v hv
  exact ⟨a, tube_subset_thickening ha⟩

end LeanFormalizations.Kakeya2D

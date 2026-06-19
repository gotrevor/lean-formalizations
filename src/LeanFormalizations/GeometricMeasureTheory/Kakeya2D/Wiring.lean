/-
# The honest (measurable-selection) route — the wiring (W)

This file assembles the proven measurable-selection spine (`MeasurableRoute.lean`:
`measurable_coveredLength`, `exists_continuum_dominant_scale`, `exists_shift_ge_integral`,
`exists_continuum_caseA_numerator`, and the zero-`ediam` negligibility helpers) with the proven
single-scale content brick (`NetThinning.caseA_content`) into the headline-shaped Hausdorff content
bound, taking a **measurable base-point selection** as a *hypothesis* (zero new axioms).

This is the route that replaces the murky `Engine.kakeya_subresolution_content` (Case-B residual) with
the clean, citable Jankov–von Neumann measurable selection. Once `hsel` is discharged (the deep crux,
descriptive set theory), the headline `davies_kakeya_2d` can be rewired through this lemma and the
Case-B axiom retired. See `STATUS.md` ledger, `PENDING_WORK.md` §Reflection-2026-06-19, and
`Kakeya2D/CASE_B_ANALYSIS.md`.

Architecture note: this file imports BOTH `Engine` (for `content_ratio_lower`, `Plane`,
`HausdorffContentBound`) and `MeasurableRoute` (the spine). `Engine` does not import `MeasurableRoute`,
so the graph is acyclic; keeping the wiring here (not in `MeasurableRoute`) leaves room for the
eventual headline switch to call it from `Engine`-level code.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Engine
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.MeasurableRoute

open MeasureTheory
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **The Hausdorff content bound from a measurable base-point selection (the wiring W).**
Given, for every measurable cover `C` of the Kakeya set `S`, a **measurable** selection
`a : ℝ → Plane` whose unit segments over the direction arc `θ∈[0,1]` lie in `⋃ C n` (`hsel`), the
Hausdorff content bound `HausdorffContentBound S d` holds for every `d∈(0,2)`. No new axioms: the
selection is a *hypothesis* here (it is the one deep input, Jankov–von Neumann, to be discharged
separately). The proof reduces the cover to closed pieces, takes the measurable selection, extracts
the cap-free continuum dominant scale + base angle via `exists_continuum_caseA_numerator`, and feeds
the genuine scale-`j` sub-fiber to `caseA_content` (the zero-`ediam` pieces are dropped via
`volume_coveredFiber_biUnion_subsingleton_zero` — they carry no covered length). NO Case B. -/
theorem kakeya_hausdorffContentBound_of_measurableSelection
    {S : Set Plane} {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2)
    (hsel : ∀ (C : ℕ → Set Plane), (∀ n, MeasurableSet (C n)) → S ⊆ ⋃ n, C n →
        ∃ a : ℝ → Plane, Measurable a ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1, Set.Icc (0 : ℝ) 1 ⊆ {t | a θ + t • dir θ ∈ ⋃ n, C n}) :
    HausdorffContentBound S d := by
  obtain ⟨cR, hcRpos, hcR⟩ := content_ratio_lower hd0 hd2
  set D : ℝ≥0∞ := volume (Metric.closedBall (0 : Plane) 1) with hD
  have hDpos : 0 < D := volume_closedBall_one_pos
  have hDtop : D ≠ ⊤ := volume_closedBall_one_ne_top
  refine ⟨1, zero_lt_one, D⁻¹ * ENNReal.ofReal cR, ?_, ?_⟩
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hDtop) (ENNReal.ofReal_pos.mpr hcRpos).ne'
  · intro t hcov hdiam
    -- Reduce to closed cover pieces (same `ediam`, still covering `S`); they are measurable.
    set U : ℕ → Set Plane := fun n => closure (t n) with hUdef
    have hUcl : ∀ n, IsClosed (U n) := fun n => isClosed_closure
    have hUmeas : ∀ n, MeasurableSet (U n) := fun n => (hUcl n).measurableSet
    have hediam_eq : ∀ n, Metric.ediam (U n) = Metric.ediam (t n) :=
      fun n => Metric.ediam_closure (t n)
    have hUcov : S ⊆ ⋃ n, U n := hcov.trans (Set.iUnion_mono fun n => subset_closure)
    have hUdiam : ∀ n, Metric.ediam (U n) ≤ 1 := fun n => (hediam_eq n).le.trans (hdiam n)
    rw [show (∑' n, Metric.ediam (t n) ^ d) = ∑' n, Metric.ediam (U n) ^ d from by
      simp_rw [hediam_eq]]
    -- The measurable base-point selection (the hypothesis).
    obtain ⟨a, ha, hcov_arc⟩ := hsel U hUmeas hUcov
    -- Uncapped dyadic scale function (zero-diameter pieces → bucket `0`).
    set g : ℕ → ℕ := fun n =>
      if 0 < (Metric.ediam (U n)).toReal then dyadicIdx (Metric.ediam (U n)).toReal else 0 with hgdef
    -- Cap-free continuum dominant scale + base angle, with the discrete numerator in hand.
    obtain ⟨j, α, hnum⟩ := exists_continuum_caseA_numerator ha hUmeas g hcov_arc
    -- Feed the genuine scale-`j` sub-fiber to `caseA_content` (drop the null zero-`ediam` pieces).
    -- TODO(W): assemble — genuine sub-fiber `s0 = {n : g n = j ∧ ediam > 0}` (window via
    -- `dyadicIdx_window`), transport `vol(A i)` across the null zero-`ediam` set via
    -- `volume_coveredFiber_biUnion_subsingleton_zero`, finite/infinite-fiber split as in `Engine`.
    sorry

end LeanFormalizations.Kakeya2D

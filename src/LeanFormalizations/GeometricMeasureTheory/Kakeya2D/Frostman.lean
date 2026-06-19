/-
# The mass-distribution (Frostman) reduction (ladder K5, brick 1)

The Córdoba content bound (K4, `volume_thickening_log_ge`) gives `vol(Sδ) ≳ 1/log(1/δ)` at every
scale — a *Minkowski-content* statement, which by itself does **not** pin the Hausdorff dimension
(box dimension ≥ Hausdorff dimension always). The bridge to `μH[d] S ≠ 0` is the **mass
distribution principle**: if some measure `μ` puts positive mass on `S` yet spreads it so thinly
that `μ s ≤ diam(s)^d` for all small `s`, then `μ ≤ μH[d]`, hence `μH[d] S ≥ μ S > 0`.

`mathlib` provides the spreading direction as `MeasureTheory.Measure.le_hausdorffMeasure`. This file
packages it into the exact shape Engine's crux consumes, reducing

  `hausdorffMeasure_pos_of_isKakeya`  ⟸  *for every `d < 2`, a Frostman measure of exponent `d`
  charging `S` exists*.

Constructing that measure from the K4 tube family (a mass-distribution / limiting argument across
dyadic scales) is the remaining deep content of K5 — see `PLAN.md` / `PENDING_WORK.md`.

Reference: Mattila, *Geometry of Sets and Measures*, §8 (mass distribution principle / Frostman). -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.CordobaL2
import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **Mass distribution principle (Frostman lower bound), packaged.** If a measure `μ` charges `S`
(`μ S ≠ 0`) and obeys the Frostman bound `μ s ≤ diam(s)^d` on all sets of diameter `≤ ε`, then the
`d`-dimensional Hausdorff measure of `S` is positive. This is the bridge from a constructed
mass-distribution to `μH[d] S ≠ 0`. -/
theorem hausdorffMeasure_ne_zero_of_frostman {S : Set Plane} {d : ℝ}
    (μ : Measure Plane) (ε : ℝ≥0∞) (hε : 0 < ε)
    (hfrost : ∀ s : Set Plane, Metric.ediam s ≤ ε → μ s ≤ Metric.ediam s ^ d)
    (hpos : μ S ≠ 0) :
    μH[d] S ≠ 0 := by
  have hle : μ ≤ μH[d] := MeasureTheory.Measure.le_hausdorffMeasure d μ ε hε hfrost
  intro hzero
  exact hpos (le_antisymm (le_trans (Measure.le_iff'.1 hle S) (le_of_eq hzero)) (zero_le _))

/-- **Mass distribution principle, with a Frostman constant.** The realistic form: a measure with
`μ s ≤ C · diam(s)^d` (any finite `C > 0`) charging `S` still forces `μH[d] S ≠ 0` — rescale by
`C⁻¹` to land in the `C = 1` hypothesis of `Measure.le_hausdorffMeasure`. This is the shape an
actual mass-distribution construction produces. -/
theorem hausdorffMeasure_ne_zero_of_frostman_const {S : Set Plane} {d : ℝ}
    (μ : Measure Plane) (C ε : ℝ≥0∞) (hC0 : C ≠ 0) (hC : C ≠ ⊤) (hε : 0 < ε)
    (hfrost : ∀ s : Set Plane, Metric.ediam s ≤ ε → μ s ≤ C * Metric.ediam s ^ d)
    (hpos : μ S ≠ 0) :
    μH[d] S ≠ 0 := by
  have hfrost' : ∀ s : Set Plane, Metric.ediam s ≤ ε → (C⁻¹ • μ) s ≤ Metric.ediam s ^ d := by
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul]
    calc C⁻¹ * μ s ≤ C⁻¹ * (C * Metric.ediam s ^ d) := by gcongr; exact hfrost s hs
      _ = C⁻¹ * C * Metric.ediam s ^ d := by rw [mul_assoc]
      _ = Metric.ediam s ^ d := by rw [ENNReal.inv_mul_cancel hC0 hC, one_mul]
  have hle : C⁻¹ • μ ≤ μH[d] := MeasureTheory.Measure.le_hausdorffMeasure d (C⁻¹ • μ) ε hε hfrost'
  intro hzero
  have hSle : (C⁻¹ • μ) S ≤ μH[d] S := Measure.le_iff'.1 hle S
  rw [hzero, Measure.smul_apply, smul_eq_mul] at hSle
  rcases mul_eq_zero.1 (le_antisymm hSle (zero_le _)) with hc | hm
  · exact (ENNReal.inv_ne_zero.2 hC) hc
  · exact hpos hm

/-- **K5 target (the remaining deep obligation), stated.** Engine's crux
`hausdorffMeasure_pos_of_isKakeya` follows from: *for every `d < 2`, a Frostman measure of exponent
`d` (with some finite constant) charging the Kakeya set `S` exists.*
`hausdorffMeasure_ne_zero_of_frostman_const` discharges the implication; building the measure from
the K4 content bound is what remains (`PENDING_WORK.md`). -/
def FrostmanMeasureExists (S : Set Plane) (d : ℝ) : Prop :=
  ∃ (μ : Measure Plane) (C ε : ℝ≥0∞), C ≠ 0 ∧ C ≠ ⊤ ∧ 0 < ε ∧
    (∀ s : Set Plane, Metric.ediam s ≤ ε → μ s ≤ C * Metric.ediam s ^ d) ∧ μ S ≠ 0

/-- The K5 reduction in one line: a Frostman measure of exponent `d` ⟹ `μH[d] S ≠ 0`. -/
theorem hausdorffMeasure_ne_zero_of_frostmanExists {S : Set Plane} {d : ℝ}
    (h : FrostmanMeasureExists S d) : μH[d] S ≠ 0 := by
  obtain ⟨μ, C, ε, hC0, hC, hε, hfrost, hpos⟩ := h
  exact hausdorffMeasure_ne_zero_of_frostman_const μ C ε hC0 hC hε hfrost hpos

end LeanFormalizations.Kakeya2D

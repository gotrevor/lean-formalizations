/-
# δ-tubes in the plane — infrastructure for Davies' theorem (ladder K2)

A **δ-tube** is the closed `δ`-neighbourhood of a unit line segment. These are the basic
objects of every proof of the planar Kakeya bound: a Kakeya set, δ-discretized, contains a
δ-tube in (essentially) every direction, and the **two-tube overlap bound** controls how much
two tubes of differing directions can intersect. That overlap bound is the geometric heart of
Córdoba's `L²`/bush argument (`PLAN.md`, ladder K2).

This file:
* defines `tube a v δ` = `cthickening δ (affineSegment ℝ a (a+v))` and the elementary structural
  facts (closed/measurable, contains its core segment, monotone in `δ`);
* states the two quantitative estimates the ladder needs:
  - `volume_tube_le` : a single δ-tube has area `≲ δ` (thin tube, `≈ 1 × 2δ`);
  - `volume_inter_tube_le` : **the overlap bound** `vol(Tᵥ ∩ T_w) ≲ δ² / (θ + δ)` for unit
    directions `v,w` at angle `θ`.

Reference: A. Córdoba, *The Kakeya maximal function and the spherical summation multipliers*,
Amer. J. Math. **99** (1977); R. O. Davies (1971).
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Set MeasureTheory Metric RealInnerProductSpace
open scoped NNReal ENNReal

namespace LeanFormalizations.Kakeya2D

/-- Abbreviation for the planar Euclidean space `Plane`. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The **δ-tube** through `a` in direction `v`: the closed `δ`-neighbourhood of the segment
`[a, a+v]`. For unit `v` and small `δ` this is a `1 × 2δ` rectangle capped by half-disks. -/
def tube (a v : Plane) (δ : ℝ) : Set Plane :=
  Metric.cthickening δ (affineSegment ℝ a (a + v))

@[simp] theorem tube_def (a v : Plane) (δ : ℝ) :
    tube a v δ = Metric.cthickening δ (affineSegment ℝ a (a + v)) := rfl

/-- A δ-tube is closed (a `cthickening` always is). -/
theorem isClosed_tube (a v : Plane) (δ : ℝ) : IsClosed (tube a v δ) :=
  isClosed_cthickening

/-- A δ-tube is measurable. -/
theorem measurableSet_tube (a v : Plane) (δ : ℝ) : MeasurableSet (tube a v δ) :=
  (isClosed_tube a v δ).measurableSet

/-- A δ-tube contains its core segment. -/
theorem affineSegment_subset_tube (a v : Plane) (δ : ℝ) :
    affineSegment ℝ a (a + v) ⊆ tube a v δ :=
  self_subset_cthickening _

/-- Tubes grow monotonically with the radius `δ`. -/
theorem tube_mono {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) (a v : Plane) :
    tube a v δ₁ ⊆ tube a v δ₂ :=
  cthickening_mono h _

/-- The core segment in explicit parametric form. -/
theorem affineSegment_eq (a v : Plane) :
    affineSegment ℝ a (a + v) = (fun t : ℝ => a + t • v) '' Icc 0 1 := by
  rw [affineSegment]
  congr 1
  funext t
  rw [AffineMap.lineMap_apply]
  simp [vsub_eq_sub, vadd_eq_add, add_comm]

/-- The core segment is compact. -/
theorem isCompact_core (a v : Plane) : IsCompact (affineSegment ℝ a (a + v)) := by
  rw [affineSegment_eq]
  exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

/-- **Every point of a δ-tube lies within `δ` of a point of the core segment.** This unwinds the
`cthickening` definition for the (compact) core: it is the union of closed `δ`-balls about the
segment. The witness parameter `t ∈ [0,1]` is what drives both thinness bounds below. -/
theorem exists_core_witness {a v : Plane} {δ : ℝ} (hδ : 0 ≤ δ) {x : Plane}
    (hx : x ∈ tube a v δ) : ∃ t ∈ Icc (0 : ℝ) 1, dist x (a + t • v) ≤ δ := by
  rw [tube_def, (isCompact_core a v).isClosed.cthickening_eq_biUnion_closedBall hδ] at hx
  simp only [affineSegment_eq, mem_iUnion, mem_image, mem_Icc, mem_closedBall,
    exists_prop, exists_exists_and_eq_and] at hx
  obtain ⟨t, ht, hd⟩ := hx
  exact ⟨t, ht, hd⟩

/-- **Transverse thinness.** In any unit direction `u` *orthogonal* to `v`, the tube is `δ`-thin:
`|⟪u, x - a⟫| ≤ δ` for every `x` in the tube. (This is the perpendicular width of the tube.) -/
theorem tube_transverse {a v u : Plane} {δ : ℝ} (hδ : 0 ≤ δ) (hu : ‖u‖ = 1)
    (huv : ⟪u, v⟫ = 0) {x : Plane} (hx : x ∈ tube a v δ) :
    |⟪u, x - a⟫| ≤ δ := by
  obtain ⟨t, _, hdist⟩ := exists_core_witness hδ hx
  have hxa : x - a = (x - (a + t • v)) + t • v := by abel
  rw [hxa, inner_add_right, real_inner_smul_right, huv, mul_zero, add_zero]
  calc |⟪u, x - (a + t • v)⟫| ≤ ‖u‖ * ‖x - (a + t • v)‖ := abs_real_inner_le_norm _ _
    _ = dist x (a + t • v) := by rw [hu, one_mul, dist_eq_norm]
    _ ≤ δ := hdist

/-- **Longitudinal extent.** Along the direction `v`, the tube about a *unit* segment occupies
exactly `⟪v, x - a⟫ ∈ [-δ, 1+δ]`: the segment spans `[0,1]` and the `δ`-thickening adds `δ` at
each end. -/
theorem tube_longitudinal {a v : Plane} {δ : ℝ} (hδ : 0 ≤ δ) (hv : ‖v‖ = 1)
    {x : Plane} (hx : x ∈ tube a v δ) :
    ⟪v, x - a⟫ ∈ Icc (-δ) (1 + δ) := by
  obtain ⟨t, ht, hdist⟩ := exists_core_witness hδ hx
  obtain ⟨ht0, ht1⟩ := ht
  have key : |⟪v, x - a⟫ - t| ≤ δ := by
    have hxa : x - a = (x - (a + t • v)) + t • v := by abel
    have heq : ⟪v, x - a⟫ - t = ⟪v, x - (a + t • v)⟫ := by
      rw [hxa, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]; ring
    rw [heq]
    calc |⟪v, x - (a + t • v)⟫| ≤ ‖v‖ * ‖x - (a + t • v)‖ := abs_real_inner_le_norm _ _
      _ = dist x (a + t • v) := by rw [hv, one_mul, dist_eq_norm]
      _ ≤ δ := hdist
  rw [abs_le] at key
  exact ⟨by linarith [key.1], by linarith [key.2]⟩

/-- The **coordinate box** of a unit tube in an orthonormal frame `(v, u)` (with `u ⊥ v`):
`⟪v, x-a⟫ ∈ [-δ, 1+δ]` (longitudinal) and `⟪u, x-a⟫ ∈ [-δ, δ]` (transverse). A `(1+2δ)×(2δ)`
rectangle in the rotated coordinates `(⟪v,·⟫, ⟪u,·⟫)`. -/
def coordBox (a v u : Plane) (δ : ℝ) : Set Plane :=
  {x | ⟪v, x - a⟫ ∈ Icc (-δ) (1 + δ) ∧ ⟪u, x - a⟫ ∈ Icc (-δ) δ}

/-- **The tube sits inside its coordinate box.** Combines longitudinal extent and transverse
thinness: this is the precise rectangle-containment underlying the single-tube area bound. -/
theorem tube_subset_coordBox {a v u : Plane} {δ : ℝ} (hδ : 0 ≤ δ) (hv : ‖v‖ = 1)
    (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0) : tube a v δ ⊆ coordBox a v u δ := by
  intro x hx
  refine ⟨tube_longitudinal hδ hv hx, ?_⟩
  have h := tube_transverse hδ hu huv hx
  rw [abs_le] at h
  exact ⟨h.1, h.2⟩

/-- **Single-tube volume bound.** A δ-tube about a *unit* segment has area `≲ δ`.

Geometrically the tube sits inside the `(1+2δ) × 2δ` rectangle aligned with `v`, so its area is
at most `(1+2δ)·2δ ≤ 6δ` for `0 ≤ δ ≤ 1`. (`6` is a convenient explicit constant, not sharp.)

TODO(K2): prove via containment in an isometric image of `Icc (-δ) (1+δ) ×ˢ Icc (-δ) δ` and
isometry-invariance of `volume`. -/
theorem volume_tube_le {a v : Plane} (hv : ‖v‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    volume (tube a v δ) ≤ ENNReal.ofReal (6 * δ) := by
  sorry

/-- **Two-tube overlap bound** (the geometric heart of K2). For unit directions `v, w` whose
angle is `θ` (so `‖v - w‖ ≈ θ` for small `θ`), the intersection of the two δ-tubes has area
`≲ δ² / (θ + δ)`.

Stated with the chord length `s := ‖v - w‖` as the separation surrogate (comparable to the
angle for unit vectors). The constant is left as `C`; sharpness is not needed downstream — only
the `1/(s+δ)` decay, which is what makes Córdoba's `L²` sum converge to `δ·log(1/δ)`.

TODO(K2): elementary planar geometry — the intersection lies in a parallelogram of side `≲ δ`
and the `transversal` length `≲ δ/(s+δ)`; integrate. -/
theorem volume_inter_tube_le {a b v w : Plane} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      volume (tube a v δ ∩ tube b w δ) ≤ ENNReal.ofReal (C * δ ^ 2 / (‖v - w‖ + δ)) := by
  sorry

end LeanFormalizations.Kakeya2D

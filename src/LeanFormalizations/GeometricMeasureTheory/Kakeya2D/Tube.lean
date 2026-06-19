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
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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

/-! ### The orthonormal frame and the area of a coordinate box

To turn the rectangle-containment `tube_subset_coordBox` into a volume bound we transport the
coordinate box to a genuine product box via the measure-preserving orthonormal-frame isometry
`x ↦ (⟪v, x-a⟫, ⟪u, x-a⟫)`. -/

/-- The orthonormal pair `![v, u]` for a unit vector `v` and a unit vector `u ⊥ v`. -/
theorem orthonormal_pair {v u : Plane} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0) :
    Orthonormal ℝ ![v, u] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hv, hu, huv, real_inner_comm u v]

/-- The orthonormal frame `(v, u)` of the plane (`u ⊥ v`, both unit) as an `OrthonormalBasis`. -/
noncomputable def frame {v u : Plane} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0) :
    OrthonormalBasis (Fin 2) ℝ Plane :=
  (basisOfLinearIndependentOfCardEqFinrank
      (orthonormal_pair hv hu huv).linearIndependent (by simp)).toOrthonormalBasis
    (by rw [coe_basisOfLinearIndependentOfCardEqFinrank]; exact orthonormal_pair hv hu huv)

theorem frame_zero {v u : Plane} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0) :
    frame hv hu huv 0 = v := by
  rw [frame, Module.Basis.coe_toOrthonormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

theorem frame_one {v u : Plane} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0) :
    frame hv hu huv 1 = u := by
  rw [frame, Module.Basis.coe_toOrthonormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

theorem frame_coord_zero {v u : Plane} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0)
    (a x : Plane) : (WithLp.ofLp ((frame hv hu huv).repr (x - a))) 0 = ⟪v, x - a⟫ := by
  show (frame hv hu huv).repr (x - a) 0 = ⟪v, x - a⟫
  rw [OrthonormalBasis.repr_apply_apply, frame_zero]

theorem frame_coord_one {v u : Plane} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0)
    (a x : Plane) : (WithLp.ofLp ((frame hv hu huv).repr (x - a))) 1 = ⟪u, x - a⟫ := by
  show (frame hv hu huv).repr (x - a) 1 = ⟪u, x - a⟫
  rw [OrthonormalBasis.repr_apply_apply, frame_one]

/-- **Exact area of the coordinate box.** Transport along the measure-preserving map
`x ↦ ofLp ((frame).repr (x-a))` (orthonormal isometry ∘ translation) to a product box in
`Fin 2 → ℝ`, where the volume is the product of the two interval lengths. -/
theorem volume_coordBox {v u : Plane} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0)
    (a : Plane) (δ : ℝ) :
    volume (coordBox a v u δ)
      = ENNReal.ofReal (1 + δ - (-δ)) * ENNReal.ofReal (δ - (-δ)) := by
  have hmp : MeasurePreserving
      (fun x : Plane => WithLp.ofLp ((frame hv hu huv).repr (x - a))) volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 2)).comp
      ((frame hv hu huv).measurePreserving_repr.comp (measurePreserving_sub_right volume a))
  have hset : coordBox a v u δ
      = (fun x : Plane => WithLp.ofLp ((frame hv hu huv).repr (x - a))) ⁻¹'
          (Set.univ.pi (fun i : Fin 2 => ![Icc (-δ) (1 + δ), Icc (-δ) δ] i)) := by
    ext x
    simp only [coordBox, mem_setOf_eq, mem_preimage, Set.mem_univ_pi, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      frame_coord_zero hv hu huv a x, frame_coord_one hv hu huv a x]
  rw [hset, hmp.measure_preimage]
  · rw [volume_pi_pi]; simp [Fin.prod_univ_two, Real.volume_Icc]
  · exact (MeasurableSet.univ_pi fun i => by fin_cases i <;> exact measurableSet_Icc).nullMeasurableSet

/-- 90° rotation of a planar vector, `(x₀, x₁) ↦ (-x₁, x₀)`; supplies a unit normal `perp v ⊥ v`. -/
def perp (v : Plane) : Plane := !₂[-(v 1), v 0]

@[simp] theorem perp_zero (v : Plane) : perp v 0 = -(v 1) := rfl
@[simp] theorem perp_one (v : Plane) : perp v 1 = v 0 := rfl

theorem sq_add_sq_of_norm_one {v : Plane} (hv : ‖v‖ = 1) : (v 0) ^ 2 + (v 1) ^ 2 = 1 := by
  have h := hv
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at h
  have h2 : (v 0) ^ 2 + (v 1) ^ 2 = 1 ^ 2 := by
    rw [← h, Real.sq_sqrt (by positivity)]; simp [Real.norm_eq_abs, sq_abs]
  simpa using h2

theorem norm_perp {v : Plane} (hv : ‖v‖ = 1) : ‖perp v‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, perp_zero, perp_one,
    show ‖-(v 1)‖ ^ 2 = (v 1) ^ 2 by simp [Real.norm_eq_abs, sq_abs],
    show ‖v 0‖ ^ 2 = (v 0) ^ 2 by simp [Real.norm_eq_abs, sq_abs], add_comm,
    sq_add_sq_of_norm_one hv]
  exact Real.sqrt_one

theorem inner_perp (v : Plane) : ⟪perp v, v⟫ = 0 := by
  have hr : ∀ a b : ℝ, ⟪a, b⟫ = b * a := fun _ _ => rfl
  simp only [PiLp.inner_apply, Fin.sum_univ_two, perp_zero, perp_one, hr]; ring

/-- **Single-tube volume bound.** A δ-tube about a *unit* segment has area `≲ δ`. **Proven**
(axiom-clean): the tube sits inside its `(1+2δ)×(2δ)` coordinate box (`tube_subset_coordBox`),
whose exact area `volume_coordBox` is `(1+2δ)·2δ ≤ 6δ` for `0 ≤ δ ≤ 1`. (`6` is convenient,
not sharp.) The normal direction is supplied by `perp v`. -/
theorem volume_tube_le {a v : Plane} (hv : ‖v‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    volume (tube a v δ) ≤ ENNReal.ofReal (6 * δ) := by
  calc volume (tube a v δ)
      ≤ volume (coordBox a v (perp v) δ) :=
        measure_mono (tube_subset_coordBox hδ hv (norm_perp hv) (inner_perp v))
    _ = ENNReal.ofReal (1 + δ - (-δ)) * ENNReal.ofReal (δ - (-δ)) :=
        volume_coordBox hv (norm_perp hv) (inner_perp v) a δ
    _ ≤ ENNReal.ofReal (6 * δ) := by
        rw [← ENNReal.ofReal_mul (by linarith)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg hδ (by linarith : (0:ℝ) ≤ 1 - δ)]

/-- **Two-slab containment of the overlap.** A point in *both* tubes is `δ`-close to *both*
core lines transversally: it lies in the parallelogram cut out by the two transverse slabs
`|⟪perp v, x-a⟫| ≤ δ` and `|⟪perp w, x-b⟫| ≤ δ`. When `v ∦ w` the normals `perp v, perp w` are
independent, so this parallelogram is bounded and its area `= (2δ)(2δ)/|sin∠(v,w)|` is the
overlap bound. (This reduces `volume_inter_tube_le` to a determinant/area computation.) -/
theorem inter_tube_subset_parallelogram {a b v w : Plane} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    tube a v δ ∩ tube b w δ ⊆
      {x | |⟪perp v, x - a⟫| ≤ δ ∧ |⟪perp w, x - b⟫| ≤ δ} := by
  rintro x ⟨hxv, hxw⟩
  exact ⟨tube_transverse hδ (norm_perp hv) (inner_perp v) hxv,
         tube_transverse hδ (norm_perp hw) (inner_perp w) hxw⟩

/-- **Two-tube overlap bound** (the geometric heart of K2). For unit directions `v, w` the
intersection of the two δ-tubes has area `≲ δ² / (s + δ)`, where `s := |v₀w₁ − v₁w₀| = |sin∠(v,w)|`
is the (lines-invariant) angular separation.

Using `s = |det[v,w]|` rather than the chord `‖v-w‖` is both *faithful* — it is invariant under
`v ↦ -v`/`w ↦ -w`, matching that a tube depends only on its line, whereas `‖v-w‖` wrongly reports
near-antipodal (≈ parallel) directions as far apart — and *natural*: `s` is exactly the Jacobian
`|det|` of the area computation. The constant `C` is not sharp; only the `1/(s+δ)` decay matters
downstream (it makes Córdoba's `L²` sum converge to `δ·log(1/δ)`).

Two regimes: near-parallel `s ≤ δ` is bounded by the single tube (`volume_tube_le`); transversal
`s > δ` by the parallelogram area `(2δ)²/s` (`inter_tube_subset_parallelogram` +
`addHaar_preimage_linearMap` with Jacobian `det[v,w] = v₀w₁−v₁w₀`). `C = 12` suffices for both. -/
theorem volume_inter_tube_le {a b v w : Plane} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    volume (tube a v δ ∩ tube b w δ)
      ≤ ENNReal.ofReal (12 * δ ^ 2 / (|v 0 * w 1 - v 1 * w 0| + δ)) := by
  sorry

end LeanFormalizations.Kakeya2D

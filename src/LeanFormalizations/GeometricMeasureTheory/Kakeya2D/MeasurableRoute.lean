/-
# The measurable-selection route — keystone measurability of the covered-length function

`Kakeya2D/CASE_B_ANALYSIS.md` pins the lone remaining obstruction (`kakeya_subresolution_content`,
the Case-B residual) to a single fact: the discrete `2ᴶ`-net machinery was built only to *avoid*
integrating over the continuum of directions, and Case B is the residue of that avoidance. The whole
proof closes the instant one may form `∫₀¹ ∑ⱼ ℓⱼ(θ) dθ ≥ 1` (each segment fully covered), pigeonhole
to a dominant scale `j*`, and run a single-scale Córdoba count at resolution `2⁻ʲ*`. The continuum is
"the scale-matched net at every resolution simultaneously", so it dissolves the net-scale circularity.

The *only* thing blocking that integral is the **measurability of the per-direction covered-length
function** `θ ↦ ℓ(θ) = vol{t∈[0,1] : a(θ)+t·v(θ) ∈ F}` — which in turn needs a **measurable base-point
selection** `θ ↦ a(θ)` (`IsKakeya` supplies only a `Classical.choice` selection; measurable selection
— Jankov–von Neumann / Kuratowski–Ryll-Nardzewski — is a genuine mathlib gap as of v4.29.1).

This file proves the keystone that the continuum route consumes and the discrete route dodged:

* `continuous_dir` / `measurable_dir` — the direction map `dir θ = (cos θ, sin θ)` is continuous;
* `measurable_coveredLength` — **given a measurable base-point map `a` and a measurable direction map
  `w`, the covered-length function `θ ↦ vol{t∈[0,1] : a θ + t•w θ ∈ F}` is measurable** for every
  measurable target `F` (via mathlib's Fubini `measurable_measure_prodMk_right`).

Once a measurable base-point selection is available (the one honest, true, citable axiom that would
replace `kakeya_subresolution_content`), this keystone + the already-proven `exists_dominant_scale`
pigeonhole + `one_le_tsum_volume_fiber_union` reduce the headline to a single-scale continuum Córdoba
count (`cordoba_continuum_count`, the remaining analytic brick). See `CASE_B_ANALYSIS.md` and
`ON-LINE-REQUEST.md` UPDATE 5. -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Directions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- The direction map `dir θ = (cos θ, sin θ)` is continuous. (`!₂[·,·] = WithLp.toLp 2 ![·,·]`,
and `WithLp.toLp 2` is continuous on the finite Pi type; the inner vector map is continuous
componentwise.) -/
theorem continuous_dir : Continuous dir := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin

/-- The direction map is measurable. -/
theorem measurable_dir : Measurable dir := continuous_dir.measurable

/-- **Keystone (the measurable-selection route).** For a measurable base-point map `a : ℝ → Plane`,
a measurable direction map `w : ℝ → Plane`, and a measurable target `F ⊆ Plane`, the **covered-length
function**

  `θ ↦ volume { t ∈ [0,1] : a θ + t • w θ ∈ F }`

is measurable. This is the one prerequisite the continuum dominant-scale argument needs and the
discrete `2ᴶ`-net machinery was invented to avoid (see `CASE_B_ANALYSIS.md`).

Proof: the joint map `Φ (t,θ) = a θ + t • w θ` is measurable, so the slab
`s = { (t,θ) : t ∈ [0,1] ∧ Φ(t,θ) ∈ F }` is measurable in `ℝ × ℝ`; Fubini
(`measurable_measure_prodMk_right`, valid as Lebesgue measure on `ℝ` is `SFinite`) makes
`θ ↦ volume {t : (t,θ) ∈ s}` measurable, and that fiber is exactly the covered set. -/
theorem measurable_coveredLength {a w : ℝ → Plane} (ha : Measurable a) (hw : Measurable w)
    {F : Set Plane} (hF : MeasurableSet F) :
    Measurable fun θ : ℝ => volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • w θ ∈ F} := by
  -- the joint map `(t,θ) ↦ a θ + t • w θ` is measurable
  have hΦ : Measurable (fun p : ℝ × ℝ => a p.2 + p.1 • w p.2) :=
    (ha.comp measurable_snd).add (measurable_fst.smul (hw.comp measurable_snd))
  -- the slab `{ (t,θ) : t ∈ [0,1] ∧ a θ + t • w θ ∈ F }` is measurable
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ a p.2 + p.1 • w p.2 ∈ F} := by
    rw [Set.setOf_and]
    exact (measurable_fst measurableSet_Icc).inter (hΦ hF)
  -- Fubini: the fiber measure is measurable in `θ`; the fiber is the covered set
  exact measurable_measure_prodMk_right hs

end LeanFormalizations.Kakeya2D

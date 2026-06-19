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
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.NetThinning
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

/-- **Continuum dominant-scale extraction — the cap-free heart of the measurable route.**

Given a **measurable** base-point selection `a : ℝ → Plane` for which, over a positive-measure arc of
directions (here `θ ∈ [0,1]`), the unit segment `t ↦ a θ + t·dir θ` is covered by the measurable
pieces `C n` (`hcov`), there is a dominant dyadic scale `j` (via the scale function `g`) carrying at
least its weight of the **integrated** covered length:

  `scaleWeight j ≤ ∫⁻ θ in [0,1], vol{ t∈[0,1] : a θ + t·dir θ ∈ ⋃_{g n = j} C n } dθ`.

This is the continuum analogue of `exists_dominant_shift` — but with **no resolution cap and no
Case B**: integrating over the continuum of directions is "the scale-matched net at every resolution
simultaneously", so the net-scale circularity that forces the discrete cap simply does not arise.
The proof: `measurable_coveredLength` makes each per-scale covered length measurable; per direction
`one_le_tsum_volume_fiber_union` gives `1 ≤ ∑ⱼ ℓⱼ(θ)`; integrating (Tonelli, `lintegral_tsum`) gives
`1 ≤ ∑ⱼ ∫ℓⱼ`; and `exists_dominant_scale` (the `scaleWeight` pigeonhole) selects `j`.

The only missing input to deploy this on a real Kakeya set is the **measurable selection** `a`
(`IsKakeya` gives only a `Classical.choice` selection — the genuine mathlib gap; see
`CASE_B_ANALYSIS.md`). Downstream, a single-scale continuum Córdoba count at resolution `2⁻ʲ` turns
this integrated covered length into the Hausdorff content bound, with no Case-B residual. -/
theorem exists_continuum_dominant_scale {a : ℝ → Plane} (ha : Measurable a)
    {C : ℕ → Set Plane} (hC : ∀ n, MeasurableSet (C n)) (g : ℕ → ℕ)
    (hcov : ∀ θ ∈ Set.Icc (0 : ℝ) 1, Set.Icc (0 : ℝ) 1 ⊆ {t | a θ + t • dir θ ∈ ⋃ n, C n}) :
    ∃ j : ℕ, scaleWeight j
      ≤ ∫⁻ θ in Set.Icc (0 : ℝ) 1,
          volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • dir θ ∈ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), C n} := by
  -- per-direction, per-piece pullback; `ℓ j θ` = covered length by scale-`j` pieces
  set T : ℕ → ℝ → Set ℝ := fun n θ => {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • dir θ ∈ C n} with hT
  set ℓ : ℕ → ℝ → ℝ≥0∞ := fun j θ => volume (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), T n θ) with hℓ
  -- the scale-`j` fiber union equals the "covered by `⋃_{g n=j} C n`" set
  have hfiberset : ∀ j θ, (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), T n θ)
      = {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • dir θ ∈ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), C n} := by
    intro j θ
    ext t
    simp only [hT, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨n, hn, ht, hmem⟩; exact ⟨ht, n, hn, hmem⟩
    · rintro ⟨ht, n, hn, hmem⟩; exact ⟨n, hn, ht, hmem⟩
  -- each `ℓ j` is measurable in `θ` (via the keystone)
  have hℓmeas : ∀ j, Measurable (ℓ j) := by
    intro j
    have hFj : MeasurableSet (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), C n) :=
      MeasurableSet.biUnion (Set.to_countable _) (fun n _ => hC n)
    have hkey := measurable_coveredLength ha measurable_dir hFj
    have heq : ℓ j = fun θ => volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1
        ∧ a θ + t • dir θ ∈ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), C n} := by
      funext θ
      change volume (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), T n θ) = _
      rw [hfiberset j θ]
    rw [heq]; exact hkey
  -- per direction: total covered length over scales is `≥ 1`
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) 1, 1 ≤ ∑' j, ℓ j θ := by
    intro θ hθ
    refine one_le_tsum_volume_fiber_union g ?_
    have hsub : Set.Icc (0 : ℝ) 1 ⊆ ⋃ n, T n θ := by
      intro t ht
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov θ hθ ht)
      exact Set.mem_iUnion.mpr ⟨n, ht, hn⟩
    calc (1 : ℝ≥0∞) = volume (Set.Icc (0 : ℝ) 1) := by
            rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
      _ ≤ volume (⋃ n, T n θ) := measure_mono hsub
  -- integrate the per-direction bound, swap sum/integral (Tonelli)
  have hone : (1 : ℝ≥0∞) ≤ ∑' j, ∫⁻ θ in Set.Icc (0 : ℝ) 1, ℓ j θ := by
    have hμ : volume (Set.Icc (0 : ℝ) 1) = 1 := by
      rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
    calc (1 : ℝ≥0∞)
        = ∫⁻ _θ in Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, hμ, mul_one]
      _ ≤ ∫⁻ θ in Set.Icc (0 : ℝ) 1, ∑' j, ℓ j θ :=
          setLIntegral_mono_ae (by fun_prop)
            (Filter.Eventually.of_forall (fun θ hθ => hpt θ hθ))
      _ = ∑' j, ∫⁻ θ in Set.Icc (0 : ℝ) 1, ℓ j θ :=
          lintegral_tsum (fun j => (hℓmeas j).aemeasurable)
  -- the `scaleWeight` pigeonhole over scales (direct index form — no subtype)
  obtain ⟨j, hj⟩ := exists_index_ge_of_tsum_lt hone tsum_scaleWeight_lt_one
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  refine lintegral_congr (fun θ => ?_)
  change volume (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), T n θ) = _
  rw [hfiberset j θ]

end LeanFormalizations.Kakeya2D

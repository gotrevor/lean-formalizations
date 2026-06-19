/-
# The Córdoba `L²` integral identities (ladder K4, bridge to Cauchy–Schwarz)

The Córdoba estimate lower-bounds `vol(Sδ)` by Cauchy–Schwarz applied to the tube-counting
function `f = ∑ₖ 1_{Tₖ}`. This file proves the two identities that turn the *integrals* of `f`
and `f²` into the *geometric sums* already bounded in `Cordoba.lean`:

* `lintegral_sum_indicator`    — `∫ f  = ∑ₖ vol(Tₖ)`            (numerator, bounded below by `sum_tube_ge`);
* `lintegral_sq_sum_indicator` — `∫ f² = ∑_{j,k} vol(Tⱼ ∩ Tₖ)`  (denominator, bounded above by `sum_overlap_le`).

The remaining Cauchy–Schwarz step `(∫ f)² ≤ vol(Sδ) · ∫ f²` (Hölder `p = q = 2` against `1_{Sδ}`,
since `f` is supported in `Sδ`) then yields `vol(Sδ) ≳ 1/log(1/δ)`. See `PLAN.md` (K4).

Reference: A. Córdoba (1977). -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Cordoba
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.TubeFractional

open Finset MeasureTheory
open scoped ENNReal Real

namespace LeanFormalizations.Kakeya2D

/-- **Numerator integral.** `∫ (∑ₖ 1_{Tₖ}) = ∑ₖ vol(Tₖ)` — integrate the finite sum of indicators
termwise (`lintegral_finset_sum`, `lintegral_indicator_one`). -/
theorem lintegral_sum_indicator (T : ℕ → Set Plane) (hT : ∀ k, MeasurableSet (T k)) (N : ℕ) :
    ∫⁻ x, ∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x ∂volume
      = ∑ k ∈ range N, volume (T k) := by
  rw [lintegral_finset_sum _ (fun k _ => measurable_one.indicator (hT k))]
  exact sum_congr rfl (fun k _ => lintegral_indicator_one (hT k))

/-- **Denominator integral.** `∫ (∑ₖ 1_{Tₖ})² = ∑_{j,k} vol(Tⱼ ∩ Tₖ)` — expand the square as a
double sum (`sum_mul_sum`), turn each product of indicators into the indicator of the intersection
(`Set.inter_indicator_one`), and integrate termwise. -/
theorem lintegral_sq_sum_indicator (T : ℕ → Set Plane) (hT : ∀ k, MeasurableSet (T k)) (N : ℕ) :
    ∫⁻ x, (∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x) ^ 2 ∂volume
      = ∑ j ∈ range N, ∑ k ∈ range N, volume (T j ∩ T k) := by
  have hpt : ∀ x, (∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x) ^ 2
      = ∑ j ∈ range N, ∑ k ∈ range N, (T j ∩ T k).indicator (1 : Plane → ℝ≥0∞) x := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    refine sum_congr rfl (fun j _ => sum_congr rfl (fun k _ => ?_))
    rw [Set.inter_indicator_one, Pi.mul_apply]
  rw [lintegral_congr hpt,
    lintegral_finset_sum _ (fun j _ =>
      Finset.measurable_sum _ (fun k _ => measurable_one.indicator ((hT j).inter (hT k))))]
  refine sum_congr rfl (fun j _ => ?_)
  rw [lintegral_finset_sum _ (fun k _ => measurable_one.indicator ((hT j).inter (hT k)))]
  exact sum_congr rfl (fun k _ => lintegral_indicator_one ((hT j).inter (hT k)))

/-- **Cauchy–Schwarz against the support.** For a measurable `f ≥ 0` supported in a measurable set
`E`, `(∫ f)² ≤ vol(E) · ∫ f²`. This is Hölder with `p = q = 2` applied to `f = f · 1_E`
(`lintegral_mul_le_Lp_mul_Lq`, `Real.HolderConjugate.two_two`), then squared. -/
theorem lintegral_sq_le_measure_mul {f : Plane → ℝ≥0∞} (hf : Measurable f)
    {E : Set Plane} (hE : MeasurableSet E) (hsupp : ∀ x, x ∉ E → f x = 0) :
    (∫⁻ x, f x ∂volume) ^ 2 ≤ volume E * ∫⁻ x, (f x) ^ 2 ∂volume := by
  set g : Plane → ℝ≥0∞ := E.indicator 1 with hg_def
  have hg : Measurable g := measurable_one.indicator hE
  have hfg : ∀ x, f x = (f * g) x := by
    intro x
    by_cases hx : x ∈ E
    · simp [hg_def, Set.indicator_of_mem hx]
    · simp [hsupp x hx]
  have h1 : ∫⁻ x, f x ∂volume = ∫⁻ x, (f * g) x ∂volume := lintegral_congr hfg
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  have hg2 : ∫⁻ x, (g x) ^ (2 : ℝ) ∂volume = volume E := by
    rw [show (fun x => (g x) ^ (2 : ℝ)) = g by
      funext x; rw [ENNReal.rpow_two]; by_cases hx : x ∈ E <;>
        simp [hg_def, Set.indicator_of_mem, Set.indicator_of_notMem, hx], hg_def,
      lintegral_indicator_one hE]
  rw [h1]
  calc (∫⁻ x, (f * g) x ∂volume) ^ 2
      ≤ ((∫⁻ x, f x ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)
          * (∫⁻ x, g x ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, f x ^ (2 : ℝ) ∂volume) * (∫⁻ x, g x ^ (2 : ℝ) ∂volume) := by
        rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        simp only [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    _ = volume E * ∫⁻ x, (f x) ^ 2 ∂volume := by
        have hr : ∫⁻ x, f x ^ (2 : ℝ) ∂volume = ∫⁻ x, (f x) ^ 2 ∂volume :=
          lintegral_congr (fun x => ENNReal.rpow_two (f x))
        rw [hg2, hr, mul_comm]

/-- **K4 — the Córdoba `L²` lower bound on the δ-neighbourhood (division-free form).** For a Kakeya
set `S`, a δ-net of `N` directions (with `N δ ≤ 1`) gives `N` δ-tubes inside `Sδ`, and

  `(N · 2δ)²  ≤  vol(Sδ) · (6π δ · 2N(1 + log N))`.

This is the cross-multiplied `(∫ f)² ≤ vol(Sδ) · ∫ f²` of Córdoba's Cauchy–Schwarz estimate, with
numerator `∫ f = ∑ vol(Tₖ) ≥ N·2δ` (`sum_tube_ge`) and denominator `∫ f² = ∑ vol(Tⱼ∩Tₖ) ≤
6π δ·2N(1+log N)` (`sum_overlap_le`). Choosing `N ≈ δ⁻¹` and dividing yields
`vol(Sδ) ≳ 1/log(1/δ)` — the Minkowski-content lower bound that K5 lifts to Hausdorff
positivity. -/
theorem volume_thickening_tubes_ge {E : Set Plane} (hE : MeasurableSet E) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : (N : ℝ) * δ ≤ 1)
    (b : ℕ → Plane) (hsub : ∀ k, tube (b k) (dir ((k : ℝ) * δ)) δ ⊆ E) :
    ((N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)) ^ 2
      ≤ volume E * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
  set T : ℕ → Set Plane := fun k => tube (b k) (dir ((k : ℝ) * δ)) δ with hT_def
  have hTmeas : ∀ k, MeasurableSet (T k) := fun k => measurableSet_tube _ _ _
  have hTsub : ∀ k, T k ⊆ E := hsub
  set f : Plane → ℝ≥0∞ := fun x => ∑ k ∈ range N, (T k).indicator 1 x with hf_def
  have hfval : ∀ x, f x = ∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x := fun x => by
    rw [hf_def]
  have hfmeas : Measurable f := by
    rw [hf_def]
    exact Finset.measurable_sum _ (fun k _ => measurable_one.indicator (hTmeas k))
  have hsupp : ∀ x, x ∉ E → f x = 0 := by
    intro x hx
    rw [hfval]
    exact Finset.sum_eq_zero (fun k _ => Set.indicator_of_notMem (fun hxk => hx (hTsub k hxk)) _)
  have hint1 : ∫⁻ x, f x ∂volume = ∑ k ∈ range N, volume (T k) := by
    rw [lintegral_congr hfval]; exact lintegral_sum_indicator T hTmeas N
  have hint2 : ∫⁻ x, (f x) ^ 2 ∂volume = ∑ j ∈ range N, ∑ k ∈ range N, volume (T j ∩ T k) := by
    rw [lintegral_congr (fun x => by rw [hfval])]; exact lintegral_sq_sum_indicator T hTmeas N
  have hnum : (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ) ≤ ∫⁻ x, f x ∂volume := by
    rw [hint1]; exact sum_tube_ge b N
  have hden : ∫⁻ x, (f x) ^ 2 ∂volume
      ≤ ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
    rw [hint2]; exact sum_overlap_le hδ hδ1 hN b
  calc ((N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)) ^ 2
      ≤ (∫⁻ x, f x ∂volume) ^ 2 := by gcongr
    _ ≤ volume E * ∫⁻ x, (f x) ^ 2 ∂volume :=
        lintegral_sq_le_measure_mul hfmeas hE hsupp
    _ ≤ volume E * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
        gcongr

/-- **Localized Córdoba `L²` bound, general per-direction sets — sub-brick (c) core.** The
dominant-scale upgrade of `volume_thickening_tubes_ge`: instead of full unit tubes, each direction `k`
contributes an arbitrary measurable set `R k` lying inside both the full δ-tube `Tₖ` (direction
`dir(kδ)`) and a container `E` (the thickened dominant-scale cover pieces). Then

  `(∑ₖ vol(R k))²  ≤  vol(E) · (6π δ · 2N(1 + log N))`.

The **denominator** is unchanged — `vol(Rⱼ ∩ Rₖ) ≤ vol(Tⱼ ∩ Tₖ)` since `R · ⊆ T ·`, so the full-tube
overlap estimate `sum_overlap_le` transfers verbatim. The `L²`/Cauchy–Schwarz chain is identical to
the full-tube case; only the numerator (`∫ f = ∑ vol(R k)`) is left to the caller. The intended `R k`
is the δ-thickening of the *covered set* `φₖ(Aₖ)` of direction `k` at the dominant scale — a general
measurable set, not a single sub-segment — whose mass `vol(R k) ≥ 2δ·vol(Aₖ)` is the covered length. -/
theorem volume_thickening_sets_ge {E : Set Plane} (hE : MeasurableSet E) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : (N : ℝ) * δ ≤ 1)
    (b : ℕ → Plane) (R : ℕ → Set Plane) (hRmeas : ∀ k, MeasurableSet (R k))
    (hRfull : ∀ k, R k ⊆ tube (b k) (dir ((k : ℝ) * δ)) δ) (hRE : ∀ k, R k ⊆ E) :
    (∑ k ∈ range N, volume (R k)) ^ 2
      ≤ volume E * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
  set Tfull : ℕ → Set Plane := fun k => tube (b k) (dir ((k : ℝ) * δ)) δ with hTfull_def
  set f : Plane → ℝ≥0∞ := fun x => ∑ k ∈ range N, (R k).indicator 1 x with hf_def
  have hfval : ∀ x, f x = ∑ k ∈ range N, (R k).indicator (1 : Plane → ℝ≥0∞) x := fun x => by
    rw [hf_def]
  have hfmeas : Measurable f := by
    rw [hf_def]
    exact Finset.measurable_sum _ (fun k _ => measurable_one.indicator (hRmeas k))
  have hsupp : ∀ x, x ∉ E → f x = 0 := by
    intro x hx
    rw [hfval]
    exact Finset.sum_eq_zero (fun k _ => Set.indicator_of_notMem (fun hxk => hx (hRE k hxk)) _)
  have hint1 : ∫⁻ x, f x ∂volume = ∑ k ∈ range N, volume (R k) := by
    rw [lintegral_congr hfval]; exact lintegral_sum_indicator R hRmeas N
  have hint2 : ∫⁻ x, (f x) ^ 2 ∂volume = ∑ j ∈ range N, ∑ k ∈ range N, volume (R j ∩ R k) := by
    rw [lintegral_congr (fun x => by rw [hfval])]; exact lintegral_sq_sum_indicator R hRmeas N
  -- denominator: overlaps bounded by full-tube overlaps, then `sum_overlap_le`
  have hden : ∫⁻ x, (f x) ^ 2 ∂volume
      ≤ ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
    rw [hint2]
    calc ∑ j ∈ range N, ∑ k ∈ range N, volume (R j ∩ R k)
        ≤ ∑ j ∈ range N, ∑ k ∈ range N, volume (Tfull j ∩ Tfull k) := by
          apply Finset.sum_le_sum; intro j _; apply Finset.sum_le_sum; intro k _
          have hss : R j ∩ R k ⊆ Tfull j ∩ Tfull k :=
            Set.inter_subset_inter (hRfull j) (hRfull k)
          exact measure_mono hss
      _ ≤ ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := sum_overlap_le hδ hδ1 hN b
  calc (∑ k ∈ range N, volume (R k)) ^ 2
      = (∫⁻ x, f x ∂volume) ^ 2 := by rw [hint1]
    _ ≤ volume E * ∫⁻ x, (f x) ^ 2 ∂volume := lintegral_sq_le_measure_mul hfmeas hE hsupp
    _ ≤ volume E * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by gcongr

/-- **Localized fractional Córdoba `L²` bound.** The `volume_thickening_sets_ge` instance with
`R k = tube (b k) (wₖ•dir(kδ)) δ` the *fractional* tube of length `wₖ ≤ 1`: it lies in the full tube
(`tube_smul_subset`) and in `E` (`hsub`), and `vol(R k) ≥ 2δ·wₖ` (`volume_tube_ge_frac`), so

  `(∑ₖ 2δ·wₖ)²  ≤  vol(E) · (6π δ · 2N(1 + log N))`. -/
theorem volume_thickening_fracTubes_ge {E : Set Plane} (hE : MeasurableSet E) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : (N : ℝ) * δ ≤ 1)
    (b : ℕ → Plane) (w : ℕ → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∀ k, w k ≤ 1)
    (hsub : ∀ k, tube (b k) (w k • dir ((k : ℝ) * δ)) δ ⊆ E) :
    (∑ k ∈ range N, ENNReal.ofReal (2 * δ * w k)) ^ 2
      ≤ volume E * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
  have hnumk : ∀ k, ENNReal.ofReal (2 * δ * w k)
      ≤ volume (tube (b k) (w k • dir ((k : ℝ) * δ)) δ) := by
    intro k
    rcases eq_or_lt_of_le (hw0 k) with hk0 | hk0
    · rw [← hk0, mul_zero, ENNReal.ofReal_zero]; exact zero_le _
    · have hdir : dir ((k : ℝ) * δ) ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_dir]; norm_num)
      have hv : w k • dir ((k : ℝ) * δ) ≠ 0 := smul_ne_zero (ne_of_gt hk0) hdir
      have hnorm : ‖w k • dir ((k : ℝ) * δ)‖ = w k := by
        rw [norm_smul, norm_dir, mul_one, Real.norm_eq_abs, abs_of_nonneg (hw0 k)]
      have hfr := volume_tube_ge_frac (a := b k) (δ := δ) hv
      rw [hnorm] at hfr
      exact hfr
  calc (∑ k ∈ range N, ENNReal.ofReal (2 * δ * w k)) ^ 2
      ≤ (∑ k ∈ range N, volume (tube (b k) (w k • dir ((k : ℝ) * δ)) δ)) ^ 2 := by
        gcongr with k _; exact hnumk k
    _ ≤ volume E * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) :=
        volume_thickening_sets_ge hE hδ hδ1 hN b _ (fun k => measurableSet_tube _ _ _)
          (fun k => tube_smul_subset (hw0 k) (hw1 k)) hsub

/-- **Localized Córdoba count, in cover-piece form — sub-brick (c) assembled (per scale).** The full
single-scale assembly, parameterised by the covered data so it stays independent of the cross-scale
combinatorics. Inputs at scale `δ` (separation = tube width): net base points `a k`, per-direction
*covered sets* `A k ⊆ [0,1]` (measurable), and a measurable container `P` (the union of the
dominant-scale cover pieces) with each covered segment `φₖ(A k) ⊆ P`. Then

  `(∑ₖ 2δ·vol(A k))²  ≤  vol(Pδ) · (6π δ · 2N(1 + log N))`.

`Pδ = cthickening δ P` is bounded above by `M·C·δ²` (`volume_thickening_le_of_ediam_le`, `M` = number
of pieces), so when the covered lengths `vol(A k)` are bounded below across a net of `N ≈ 1/δ`
directions, this forces `M ≳ 1/(δ²·log)` pieces at the dominant scale — the final Hausdorff content
bound. Proof: take `R k = cthickening δ (φₖ(A k))` in `volume_thickening_sets_ge`; `R k ⊆ Pδ`
(`cthickening` monotone), `R k ⊆` full tube (`φₖ(A k) ⊆` segment since `A k ⊆ [0,1]`), and the
numerator `vol(R k) ≥ 2δ·vol(A k)` is `volume_thickening_covered_ge`. -/
theorem cordoba_cover_count {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : (N : ℝ) * δ ≤ 1)
    (a : ℕ → Plane) (A : ℕ → Set ℝ) (hAmeas : ∀ k, MeasurableSet (A k))
    (hA01 : ∀ k, A k ⊆ Set.Icc (0 : ℝ) 1)
    (P : Set Plane) (hcov : ∀ k, (fun t => a k + t • dir ((k : ℝ) * δ)) '' (A k) ⊆ P) :
    (∑ k ∈ range N, ENNReal.ofReal (2 * δ) * volume (A k)) ^ 2
      ≤ volume (Metric.cthickening δ P)
        * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
  set φ : ℕ → ℝ → Plane := fun k t => a k + t • dir ((k : ℝ) * δ) with hφ
  set R : ℕ → Set Plane := fun k => Metric.cthickening δ (φ k '' (A k)) with hR
  -- R k ⊆ full δ-tube about direction k (covered segment ⊆ unit segment)
  have hRfull : ∀ k, R k ⊆ tube (a k) (dir ((k : ℝ) * δ)) δ := by
    intro k
    have hseg : φ k '' (A k) ⊆ affineSegment ℝ (a k) (a k + dir ((k : ℝ) * δ)) := by
      rintro y ⟨t, htA, rfl⟩
      rw [affineSegment_eq]; exact ⟨t, hA01 k htA, rfl⟩
    rw [hR, tube_def]
    exact Metric.cthickening_subset_of_subset δ hseg
  -- R k ⊆ container thickening
  have hRE : ∀ k, R k ⊆ Metric.cthickening δ P := fun k =>
    Metric.cthickening_subset_of_subset δ (hcov k)
  -- numerator: vol(R k) ≥ 2δ·vol(A k)
  have hnumk : ∀ k, ENNReal.ofReal (2 * δ) * volume (A k) ≤ volume (R k) := fun k =>
    volume_thickening_covered_ge (norm_dir _) (hAmeas k)
  calc (∑ k ∈ range N, ENNReal.ofReal (2 * δ) * volume (A k)) ^ 2
      ≤ (∑ k ∈ range N, volume (R k)) ^ 2 := by gcongr with k _; exact hnumk k
    _ ≤ volume (Metric.cthickening δ P)
          * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) :=
        volume_thickening_sets_ge Metric.isClosed_cthickening.measurableSet hδ hδ1 hN a R
          (fun k => Metric.isClosed_cthickening.measurableSet) hRfull hRE

/-- The Kakeya specialization of `volume_thickening_tubes_ge`: the `N` net-direction δ-tubes
furnished by `exists_tube_family` all lie in `Sδ`, so `E := thickening S δ`. -/
theorem volume_thickening_mul_ge {S : Set Plane} (h : IsKakeya S) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : (N : ℝ) * δ ≤ 1) :
    ((N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)) ^ 2
      ≤ volume (thickening S δ) * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
  obtain ⟨a, ha⟩ := exists_tube_family h δ
  exact volume_thickening_tubes_ge (measurableSet_thickening S δ) hδ hδ1 hN
    (fun k => a ((k : ℝ) * δ)) (fun k => ha ((k : ℝ) * δ))

/-- **K4 — the Minkowski-content lower bound `vol(Sδ) ≳ 1/log(1/δ)`.** Specialising
`volume_thickening_mul_ge` to the maximal net `N = ⌊1/δ⌋` (so the numerator `N·2δ ≥ 1` and the
denominator `6π δ·2N(1+log N) ≤ 12π(1+log(1/δ))`), the δ-neighbourhood of a planar Kakeya set
satisfies

  `1 ≤ vol(Sδ) · 12π(1 + log(1/δ))`,

i.e. `vol(Sδ) ≥ 1 / (12π(1 + log(1/δ)))`. This is the uniform-content input that K5 lifts (via a
mass-distribution / Frostman argument across scales) to `μH[d] S ≠ 0` for every `d < 2`. -/
theorem volume_thickening_log_ge {S : Set Plane} (h : IsKakeya S) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    1 ≤ volume (thickening S δ) * ENNReal.ofReal (12 * π * (1 + Real.log (1 / δ))) := by
  set N : ℕ := ⌊1 / δ⌋₊ with hN_def
  have hr2 : (2 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hr2)
  have hNpos : 0 < N := by omega
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNle : (N : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hNδ : (N : ℝ) * δ ≤ 1 := (le_div_iff₀ hδ).mp hNle
  -- numerator ≥ 1
  have hNlow : 1 / δ - 1 < (N : ℝ) := by linarith [Nat.lt_floor_add_one (1 / δ : ℝ)]
  have hδNlow : 1 - δ < (N : ℝ) * δ := by
    have h1 : (1 / δ - 1) * δ < (N : ℝ) * δ := by
      apply mul_lt_mul_of_pos_right hNlow hδ
    have h2 : (1 / δ - 1) * δ = 1 - δ := by field_simp
    linarith
  have h2δN : (1 : ℝ) ≤ (N : ℝ) * (2 * δ) := by nlinarith [hδNlow, hδ2]
  have hnum1 : (1 : ℝ≥0∞) ≤ ((N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)) ^ 2 := by
    have heq : ENNReal.ofReal ((N : ℝ) * (2 * δ)) = (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    rw [← heq, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [h2δN])
  -- denominator ≤ 12π(1+log(1/δ))
  have hlogN : Real.log N ≤ Real.log (1 / δ) := Real.log_le_log hNposR hNle
  have h1logN : (0 : ℝ) ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN1R]
  have hden_le : ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N)))
      ≤ ENNReal.ofReal (12 * π * (1 + Real.log (1 / δ))) := by
    apply ENNReal.ofReal_le_ofReal
    have hprod : δ * N * (1 + Real.log N) ≤ 1 * (1 + Real.log (1 / δ)) :=
      mul_le_mul (by rw [mul_comm]; exact hNδ) (by linarith [hlogN]) h1logN zero_le_one
    nlinarith [hprod, Real.pi_pos, h1logN]
  calc (1 : ℝ≥0∞)
      ≤ ((N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)) ^ 2 := hnum1
    _ ≤ volume (thickening S δ) * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) :=
        volume_thickening_mul_ge h hδ (by linarith) hNδ
    _ ≤ volume (thickening S δ) * ENNReal.ofReal (12 * π * (1 + Real.log (1 / δ))) := by
        gcongr

end LeanFormalizations.Kakeya2D

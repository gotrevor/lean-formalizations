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
theorem volume_thickening_mul_ge {S : Set Plane} (h : IsKakeya S) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : (N : ℝ) * δ ≤ 1) :
    ((N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)) ^ 2
      ≤ volume (thickening S δ) * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
  obtain ⟨a, ha⟩ := exists_tube_family h δ
  set b : ℕ → Plane := fun k => a ((k : ℝ) * δ) with hb_def
  set T : ℕ → Set Plane := fun k => tube (b k) (dir ((k : ℝ) * δ)) δ with hT_def
  have hTmeas : ∀ k, MeasurableSet (T k) := fun k => measurableSet_tube _ _ _
  have hTsub : ∀ k, T k ⊆ thickening S δ := fun k => ha ((k : ℝ) * δ)
  set f : Plane → ℝ≥0∞ := fun x => ∑ k ∈ range N, (T k).indicator 1 x with hf_def
  have hfval : ∀ x, f x = ∑ k ∈ range N, (T k).indicator (1 : Plane → ℝ≥0∞) x := fun x => by
    rw [hf_def]
  have hfmeas : Measurable f := by
    rw [hf_def]
    exact Finset.measurable_sum _ (fun k _ => measurable_one.indicator (hTmeas k))
  have hsupp : ∀ x, x ∉ thickening S δ → f x = 0 := by
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
    _ ≤ volume (thickening S δ) * ∫⁻ x, (f x) ^ 2 ∂volume :=
        lintegral_sq_le_measure_mul hfmeas (measurableSet_thickening S δ) hsupp
    _ ≤ volume (thickening S δ) * ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
        gcongr

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

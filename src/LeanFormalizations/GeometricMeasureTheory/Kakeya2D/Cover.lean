/-
# The Hausdorff content lower bound (ladder K5, the honest cover route)

The Córdoba content bound (K4, `volume_thickening_log_ge`) gives `vol(Sδ) ≳ 1/log(1/δ)` at every
scale — a *Minkowski-content* statement, which by itself does **not** pin the Hausdorff dimension
(box dimension ≥ Hausdorff dimension always). The previous brick (`Frostman.lean`) packaged the
mass-distribution principle, reducing the crux to *constructing a measure* — which forces a weak-*
limit of normalised tube masses, a heavy piece of measure theory.

This file takes the **dual, measure-free route**: it reduces `μH[d] S ≠ 0` directly to a uniform
**Hausdorff content lower bound** —

  `∃ r > 0, ∃ c ≠ 0, ∀ countable cover `S ⊆ ⋃ tₙ` with `ediam(tₙ) ≤ r`, `∑ₙ ediam(tₙ)^d ≥ c`.

via mathlib's covering formula `hausdorffMeasure_apply`. This is the most faithful form of Córdoba's
argument: there is no measure to build; the entire remaining content is a covering/pigeonhole
estimate fed by the K4 single-scale bound. The deep multi-scale combinatorics (a dyadic pigeonhole
reducing an arbitrary cover to a dominant scale, then the single-scale tube count) is what remains.

Reference: Mattila, *Geometry of Sets and Measures*, §4–5 (Hausdorff content, net measures);
A. Córdoba (1977). -/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.CordobaL2
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

open Set MeasureTheory Metric
open scoped ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **Hausdorff content lower bound ⟹ positive Hausdorff measure (raw form).** If there is a scale
`r > 0` and a positive constant `c` such that *every* countable cover of `S` by sets of diameter
`≤ r` has `∑ₙ ⨆_{tₙ ≠ ∅} ediam(tₙ)^d ≥ c`, then `μH[d] S ≠ 0`.

This is the exact shape of mathlib's covering formula `hausdorffMeasure_apply`: the supremum over `r`
of the infimum over covers is `≥ c > 0`. -/
theorem hausdorffMeasure_ne_zero_of_content_bound {S : Set Plane} {d : ℝ}
    {r : ℝ≥0∞} (hr : 0 < r) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hbound : ∀ t : ℕ → Set Plane, S ⊆ ⋃ n, t n → (∀ n, Metric.ediam (t n) ≤ r) →
        c ≤ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) :
    μH[d] S ≠ 0 := by
  have hge : c ≤ μH[d] S := by
    rw [Measure.hausdorffMeasure_apply]
    refine le_trans ?_
      (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
        ⨅ (t : ℕ → Set Plane) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) r hr)
    exact le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => hbound t hcov hdiam
  exact fun hzero => hc (le_antisymm (hzero ▸ hge) (zero_le c))

/-- **Hausdorff content lower bound ⟹ positive Hausdorff measure (diameter form, `d > 0`).** The
convenient downstream form: the cover hypothesis is stated with the *bare* sum `∑ₙ ediam(tₙ)^d`
(no `Nonempty` guard). For `d > 0` the guard is free — an empty piece has `ediam = 0` and
`0^d = 0` — so the two sums agree termwise. -/
theorem hausdorffMeasure_ne_zero_of_diam_content {S : Set Plane} {d : ℝ} (hd : 0 < d)
    {r : ℝ≥0∞} (hr : 0 < r) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hbound : ∀ t : ℕ → Set Plane, S ⊆ ⋃ n, t n → (∀ n, Metric.ediam (t n) ≤ r) →
        c ≤ ∑' n, Metric.ediam (t n) ^ d) :
    μH[d] S ≠ 0 := by
  refine hausdorffMeasure_ne_zero_of_content_bound hr hc (fun t hcov hdiam => ?_)
  refine le_trans (hbound t hcov hdiam) (ENNReal.tsum_le_tsum (fun n => ?_))
  by_cases hne : (t n).Nonempty
  · exact le_iSup (fun _ : (t n).Nonempty => Metric.ediam (t n) ^ d) hne
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hd]
    exact zero_le _

/-- **The remaining deep obligation (K5 core), as a `Prop`.** A *Hausdorff content lower bound* of
exponent `d` for `S`: a scale `r > 0` and a positive constant `c` such that every countable cover of
`S` by sets of diameter `≤ r` has `∑ₙ ediam(tₙ)^d ≥ c`. For a planar Kakeya set this holds for every
`d < 2` (Córdoba / Davies); `hausdorffMeasure_ne_zero_of_diam_content` turns it into `μH[d] S ≠ 0`. -/
def HausdorffContentBound (S : Set Plane) (d : ℝ) : Prop :=
  ∃ r : ℝ≥0∞, 0 < r ∧ ∃ c : ℝ≥0∞, c ≠ 0 ∧
    ∀ t : ℕ → Set Plane, S ⊆ ⋃ n, t n → (∀ n, Metric.ediam (t n) ≤ r) →
      c ≤ ∑' n, Metric.ediam (t n) ^ d

/-- The K5 reduction, packaged: a Hausdorff content lower bound of exponent `d > 0` ⟹
`μH[d] S ≠ 0`. -/
theorem hausdorffMeasure_ne_zero_of_contentBound {S : Set Plane} {d : ℝ} (hd : 0 < d)
    (h : HausdorffContentBound S d) : μH[d] S ≠ 0 := by
  obtain ⟨r, hr, c, hc, hbound⟩ := h
  exact hausdorffMeasure_ne_zero_of_diam_content hd hr hc hbound

/-! ### Covering geometry: a cover of `S` thickens to a cover of `Sδ`

The bridge from the K4 single-scale content `vol(Sδ) ≳ 1/log(1/δ)` to a Hausdorff content lower
bound. A countable cover `S ⊆ ⋃ Uₙ` thickens to a cover `Sδ ⊆ ⋃ (Uₙ)δ'` of the δ-neighbourhood,
*provided one opens up the radius* `δ < δ'`. The strict gap is essential for the **closed**
thickening: `infEdist x S ≤ ofReal δ` forces the infimum `⨅ₙ infEdist x Uₙ ≤ ofReal δ` to be `<`
than `ofReal δ'`, which (unlike `≤`) is attained by *some* single `n` (`iInf_lt_iff`). With equal
radii an infinite cover can keep the inf an unattained limit — exactly the boundary subtlety flagged
in the K5 plan, dissolved by the slack. -/

/-- **Cover thickening (closed, with slack).** If `S ⊆ ⋃ₙ Uₙ` and `0 ≤ δ < δ'`, then the closed
δ-neighbourhood of `S` is covered by the closed δ'-neighbourhoods of the `Uₙ`. -/
theorem thickening_subset_iUnion_thickening {S : Set Plane} {U : ℕ → Set Plane}
    (hcov : S ⊆ ⋃ n, U n) {δ δ' : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < δ') :
    thickening S δ ⊆ ⋃ n, thickening (U n) δ' := by
  intro x hx
  rw [thickening_def, mem_cthickening_iff] at hx
  have h1 : (⨅ n, infEDist x (U n)) ≤ ENNReal.ofReal δ := by
    rw [← infEDist_iUnion]; exact le_trans (infEDist_anti hcov) hx
  have hlt : (⨅ n, infEDist x (U n)) < ENNReal.ofReal δ' :=
    lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hδ0 hδ)).mpr hδ)
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hlt
  exact mem_iUnion.mpr ⟨n, by rw [thickening_def, mem_cthickening_iff]; exact hn.le⟩

/-- **Subadditive covering-volume bound.** If `S ⊆ ⋃ₙ Uₙ` and `0 ≤ δ < δ'`, then
`vol(Sδ) ≤ ∑ₙ vol((Uₙ)δ')`. This is the upper bound on the δ-neighbourhood volume of `S` in terms of
the cover, which — paired with the K4 lower bound `volume_thickening_log_ge` — drives the
single-scale Hausdorff content estimate. -/
theorem volume_thickening_le_tsum {S : Set Plane} {U : ℕ → Set Plane}
    (hcov : S ⊆ ⋃ n, U n) {δ δ' : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < δ') :
    volume (thickening S δ) ≤ ∑' n, volume (thickening (U n) δ') :=
  le_trans (measure_mono (thickening_subset_iUnion_thickening hcov hδ0 hδ)) (measure_iUnion_le _)

/-- **Diameter ⟹ thickened-volume bound.** A cover piece `U` of diameter `≤ ρ`, thickened by `δ'`,
sits inside a disc of radius `ρ + δ'`, so its area is `≤ π·(ρ+δ')²` (with `π = vol(unit disc)`). In
the plane `vol(closedBall 0 1) = π`. This is the per-piece estimate that, summed against
`volume_thickening_le_tsum`, turns the K4 lower bound `vol(Sδ) ≳ 1/log` into a lower bound on the
number/size of cover pieces — the engine of the single-scale Hausdorff content estimate. -/
theorem volume_thickening_le_of_ediam_le {U : Set Plane} {ρ δ' : ℝ}
    (hρ : 0 ≤ ρ) (hδ' : 0 ≤ δ') (hdiam : Metric.ediam U ≤ ENNReal.ofReal ρ) :
    volume (thickening U δ') ≤ ENNReal.ofReal ((ρ + δ') ^ 2) * volume (closedBall (0 : Plane) 1) := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rw [thickening_def, cthickening_empty, measure_empty]; exact zero_le _
  · have hsub : U ⊆ closedBall x₀ ρ := by
      intro y hy
      rw [Metric.mem_closedBall, dist_comm]
      have he : edist x₀ y ≤ ENNReal.ofReal ρ :=
        le_trans (Metric.edist_le_ediam_of_mem hx₀ hy) hdiam
      rw [edist_dist] at he
      exact (ENNReal.ofReal_le_ofReal_iff hρ).1 he
    have hsubball : thickening U δ' ⊆ closedBall x₀ (δ' + ρ) := by
      rw [thickening_def]
      calc cthickening δ' U ⊆ cthickening δ' (closedBall x₀ ρ) := cthickening_subset_of_subset δ' hsub
        _ = closedBall x₀ (δ' + ρ) := cthickening_closedBall hδ' hρ x₀
    have hfr : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
    calc volume (thickening U δ')
        ≤ volume (closedBall x₀ (δ' + ρ)) := measure_mono hsubball
      _ = ENNReal.ofReal ((δ' + ρ) ^ Module.finrank ℝ Plane) * volume (closedBall (0 : Plane) 1) :=
          Measure.addHaar_closedBall' volume x₀ (add_nonneg hδ' hρ)
      _ = ENNReal.ofReal ((ρ + δ') ^ 2) * volume (closedBall (0 : Plane) 1) := by
          rw [hfr, add_comm δ' ρ]

end LeanFormalizations.Kakeya2D

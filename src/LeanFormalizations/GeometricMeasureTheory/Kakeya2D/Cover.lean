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

/-- **Weighted pigeonhole (`ℝ≥0∞`).** If the total `∑ₙ aₙ` reaches `c` while the weights total
`∑ₙ wₙ < c`, then some index carries at least its weight: `wₙ ≤ aₙ`. This is the engine of the two
pigeonholes (first over dyadic scales, then over net directions) in the remaining multi-scale
Hausdorff content estimate: with weights `wⱼ = 6/(π²(j+1)²)` summing to `< 1 ≤ ∑ⱼ Lⱼ`, it extracts a
dominant scale carrying a definite fraction of the covering. -/
theorem exists_index_ge_of_tsum_lt {a w : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hsum : c ≤ ∑' n, a n) (hw : ∑' n, w n < c) : ∃ n, w n ≤ a n := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hle : ∑' n, a n ≤ ∑' n, w n := ENNReal.tsum_le_tsum (fun n => (h n).le)
  exact absurd (lt_of_le_of_lt (le_trans hsum hle) hw) (lt_irrefl c)

/-! ### Dyadic scale pigeonhole: extracting a dominant scale from a covered total

The multi-scale upgrade (Minkowski ⟹ Hausdorff) hinges on reducing an arbitrary cover to a single
*dominant scale*. The mechanism: given a total `1 ≤ ∑ₙ fₙ` spread over the cover pieces, partition the
pieces by a dyadic scale function `g : ℕ → ℕ` (`g n` = the dyadic scale of `ediam(Uₙ)`), regroup the
sum scale-by-scale (`ENNReal.tsum_fiberwise`), and pigeonhole against weights `wⱼ` summing to `< 1`.

The weights **must decay only polynomially** (`wⱼ ≳ 1/j²`): the dominant scale's share `Lⱼ ≥ wⱼ` then
beats the geometric shrinkage `δ = 2⁻ʲ`, which is exactly what the localized-Córdoba assembly needs
(`δ^{-(2-d)}` must dominate `poly(log 1/δ)`). Geometric weights `2⁻ʲ` would give `Lⱼ ≳ δ`, killing the
gain. The telescoping family `wⱼ = 1/(2(j+1)(j+2))` (sum `= 1/2 < 1`) supplies this cleanly. -/

/-- The telescoping series `∑ₙ 1/((n+1)(n+2)) = 1` (partial sums `1 - 1/(n+1)`). -/
theorem hasSum_one_div_succ_mul_succ_succ :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1) * (n + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  have hpartial : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 : ℝ) / ((i + 1) * (i + 2)) = 1 - 1 / (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  simp_rw [hpartial]
  have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub (1 : ℝ)
  simpa using h0

/-- The dyadic-scale weights `wⱼ = 1/(2(j+1)(j+2))` (as `ℝ≥0∞`), summing to `1/2`. Polynomial decay
`≳ 1/j²` is essential — see the section header. -/
noncomputable def scaleWeight (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * (j + 1) * (j + 2)))

/-- The scale weights total `< 1`, the slack the pigeonhole `exists_index_ge_of_tsum_lt` needs. -/
theorem tsum_scaleWeight_lt_one : ∑' j : ℕ, scaleWeight j < 1 := by
  have hhalf : HasSum (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2))) (1 / 2) := by
    have h := hasSum_one_div_succ_mul_succ_succ.mul_left (1 / 2)
    have he : (fun n : ℕ => (1 / 2) * ((1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2))))
        = fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      funext n
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
    rw [he] at h
    simpa using h
  have hnonneg : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := fun n => by positivity
  have hsum : ∑' j : ℕ, scaleWeight j = ENNReal.ofReal (1 / 2) := by
    unfold scaleWeight
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hhalf.summable, hhalf.tsum_eq]
  rw [hsum]
  exact ENNReal.ofReal_lt_one.mpr (by norm_num)

/-- **Dominant-scale extraction.** Given a total `1 ≤ ∑ₙ fₙ` over cover pieces and any dyadic scale
function `g : ℕ → ℕ`, some scale `j` carries at least its weight: `scaleWeight j ≤ ∑_{n : g n = j} fₙ`.
Proof: regroup the sum by scale (`ENNReal.tsum_fiberwise`), then the weighted pigeonhole against the
`< 1` weights. This is the first of the two pigeonholes (scales, then directions) of the multi-scale
Córdoba Hausdorff content estimate. -/
theorem exists_dominant_scale {f : ℕ → ℝ≥0∞} (g : ℕ → ℕ) (h : 1 ≤ ∑' n, f n) :
    ∃ j : ℕ, scaleWeight j ≤ ∑' n : (g ⁻¹' {j} : Set ℕ), f n := by
  have hfib : ∑' j : ℕ, (∑' n : (g ⁻¹' {j} : Set ℕ), f n) = ∑' n, f n :=
    ENNReal.tsum_fiberwise f g
  exact exists_index_ge_of_tsum_lt (hfib ▸ h) tsum_scaleWeight_lt_one

/-- **Global dominant scale across a direction net (sub-brick (b)).** Given a finite nonempty set `s`
of directions and, for each `k ∈ s`, a per-scale covered-length profile `L k · : ℕ → ℝ≥0∞` with total
`1 ≤ ∑ⱼ L k j` (the per-direction covered unit segment), there is a single scale `j` whose pieces
cover a definite fraction of the *aggregate* length:

  `s.card · scaleWeight j ≤ ∑_{k ∈ s} L k j`,   i.e. total covered length at scale `j ≳ |s|/(j+1)²`.

This is the second pigeonhole: sum the per-direction totals to `≥ |s|`, swap finite-sum with the
scale `tsum`, and pigeonhole the aggregate against the weights `|s|·scaleWeight` (total `< |s|`). The
output is the input to the localized Córdoba count (sub-brick (c)): `|s|/poly` directions worth of
covered length concentrated at one scale `δ = 2⁻ʲ`. -/
theorem exists_global_dominant_scale {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (L : ι → ℕ → ℝ≥0∞) (hL : ∀ k ∈ s, 1 ≤ ∑' j, L k j) :
    ∃ j : ℕ, (s.card : ℝ≥0∞) * scaleWeight j ≤ ∑ k ∈ s, L k j := by
  have hcard0 : (s.card : ℝ≥0∞) ≠ 0 :=
    (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)).ne'
  have hcardtop : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : (s.card : ℝ≥0∞) ≤ ∑' j, ∑ k ∈ s, L k j := by
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have hcard : (s.card : ℝ≥0∞) = ∑ _k ∈ s, (1 : ℝ≥0∞) := by simp
    rw [hcard]
    exact Finset.sum_le_sum (fun k hk => hL k hk)
  have hw : ∑' j, ((s.card : ℝ≥0∞) * scaleWeight j) < (s.card : ℝ≥0∞) := by
    rw [ENNReal.tsum_mul_left, mul_comm (s.card : ℝ≥0∞)]
    calc (∑' j, scaleWeight j) * (s.card : ℝ≥0∞)
        < 1 * (s.card : ℝ≥0∞) := ENNReal.mul_lt_mul_left hcard0 hcardtop tsum_scaleWeight_lt_one
      _ = (s.card : ℝ≥0∞) := one_mul _
  exact exists_index_ge_of_tsum_lt hsum hw

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

/-- **Finite-union thickening subadditivity.** For a *finite* index set, the δ-thickening of a union
of cover pieces has area at most the sum of the per-piece thickened areas:
`vol(thickening (⋃_{n∈s} Uₙ) δ) ≤ ∑_{n∈s} vol(thickening (Uₙ) δ)`. (The closed thickening distributes
over *finite* unions — `cthickening_union` — unlike the infinite case that needed the `δ<δ'` slack.)
Combined with `volume_thickening_le_of_ediam_le`, this bounds the container `vol(Pδ) ≤ M·C·(ρ+δ)²` for
the union `P` of the `M` dominant-scale cover pieces in the localized Córdoba count. -/
theorem volume_thickening_biUnion_le (s : Finset ℕ) (U : ℕ → Set Plane) (δ : ℝ) :
    volume (thickening (⋃ n ∈ s, U n) δ) ≤ ∑ n ∈ s, volume (thickening (U n) δ) := by
  classical
  induction s using Finset.induction with
  | empty => simp [thickening]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    have hun : thickening (U a ∪ ⋃ n ∈ s, U n) δ
        = thickening (U a) δ ∪ thickening (⋃ n ∈ s, U n) δ := by
      simp only [thickening_def]; exact cthickening_union δ _ _
    rw [hun]
    calc volume (thickening (U a) δ ∪ thickening (⋃ n ∈ s, U n) δ)
        ≤ volume (thickening (U a) δ) + volume (thickening (⋃ n ∈ s, U n) δ) := measure_union_le _ _
      _ ≤ volume (thickening (U a) δ) + ∑ n ∈ s, volume (thickening (U n) δ) := by gcongr

/-- The planar unit-disc area constant `vol(closedBall 0 1)` is positive — the Frostman constant `C`
in the eventual content bound is built from it, so it must be `≠ 0`. -/
theorem volume_closedBall_one_pos : 0 < volume (closedBall (0 : Plane) 1) :=
  measure_closedBall_pos volume 0 one_pos

/-- The planar unit-disc area constant is finite (a bounded set in finite dimension) — so the
Frostman constant `C` built from it is `≠ ⊤`. -/
theorem volume_closedBall_one_ne_top : volume (closedBall (0 : Plane) 1) ≠ ⊤ :=
  measure_closedBall_lt_top.ne

/-- **Single-scale cover-piece count — sub-brick (c), fully assembled in piece-count form.** Combines
the localized Córdoba count `cordoba_cover_count` with the container bound
(`volume_thickening_biUnion_le` + `volume_thickening_le_of_ediam_le`). At scale `δ`, for a net of `N`
directions with covered sets `A k ⊆ [0,1]` whose covered segments lie in the union of a *finite* set
`s` of cover pieces each of diameter `≤ ρ`:

  `(∑ₖ 2δ·vol(A k))²  ≤  |s| · (ρ+δ)² · vol(unit disc) · (6π δ · 2N(1 + log N))`.

Reading off `M = |s|`: the number of dominant-scale pieces is `M ≳ (∑ₖ vol(A k))² / ((ρ+δ)²·log N)`.
With `ρ ≈ δ` (dominant scale), `N ≈ 1/δ`, and `∑ₖ vol(A k) ≳ N/poly` (the two pigeonholes), this is
`M ≳ δ^{-2}/poly`, hence `∑_{scale} ediam^d ≥ M·δ^d ≳ δ^{-(2-d)}/poly`. The only remaining gap to
`kakeya_hausdorffContentBound` is the cross-scale orchestration furnishing `∑ₖ vol(A k) ≳ N/poly`
(the net-scale thinning; see `ON-LINE-REQUEST.md`). -/
theorem cover_count_lower {δ ρ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ)
    {N : ℕ} (hN : (N : ℝ) * δ ≤ 1)
    (a : ℕ → Plane) (A : ℕ → Set ℝ) (hAmeas : ∀ k, MeasurableSet (A k))
    (hA01 : ∀ k, A k ⊆ Icc (0 : ℝ) 1)
    (s : Finset ℕ) (U : ℕ → Set Plane) (hediam : ∀ n ∈ s, Metric.ediam (U n) ≤ ENNReal.ofReal ρ)
    (hcov : ∀ k, (fun t => a k + t • dir ((k : ℝ) * δ)) '' (A k) ⊆ ⋃ n ∈ s, U n) :
    (∑ k ∈ Finset.range N, ENNReal.ofReal (2 * δ) * volume (A k)) ^ 2
      ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal ((ρ + δ) ^ 2) * volume (closedBall (0 : Plane) 1)
        * ENNReal.ofReal (6 * Real.pi * δ * (2 * N * (1 + Real.log N))) := by
  have hPbound : volume (Metric.cthickening δ (⋃ n ∈ s, U n))
      ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal ((ρ + δ) ^ 2) * volume (closedBall (0 : Plane) 1) := by
    have h2 : ∑ n ∈ s, volume (thickening (U n) δ)
        ≤ ∑ _n ∈ s, ENNReal.ofReal ((ρ + δ) ^ 2) * volume (closedBall (0 : Plane) 1) :=
      Finset.sum_le_sum (fun n hn => volume_thickening_le_of_ediam_le hρ hδ.le (hediam n hn))
    have h3 : ∑ _n ∈ s, ENNReal.ofReal ((ρ + δ) ^ 2) * volume (closedBall (0 : Plane) 1)
        = (s.card : ℝ≥0∞) * ENNReal.ofReal ((ρ + δ) ^ 2) * volume (closedBall (0 : Plane) 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    rw [show Metric.cthickening δ (⋃ n ∈ s, U n) = thickening (⋃ n ∈ s, U n) δ from rfl, ← h3]
    exact le_trans (volume_thickening_biUnion_le s U δ) h2
  calc (∑ k ∈ Finset.range N, ENNReal.ofReal (2 * δ) * volume (A k)) ^ 2
      ≤ volume (Metric.cthickening δ (⋃ n ∈ s, U n))
          * ENNReal.ofReal (6 * Real.pi * δ * (2 * N * (1 + Real.log N))) :=
        cordoba_cover_count hδ hδ1 hN a A hAmeas hA01 (⋃ n ∈ s, U n) hcov
    _ ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal ((ρ + δ) ^ 2) * volume (closedBall (0 : Plane) 1)
          * ENNReal.ofReal (6 * Real.pi * δ * (2 * N * (1 + Real.log N))) := by gcongr

/-! ### Per-direction length bound: a covered unit segment forces `∑ₙ ediam(Uₙ) ≥ 1`

The foundation of the dyadic pigeonhole. Pull the cover `ℓ ⊆ ⋃Uₙ` of a *unit* segment back along the
unit-speed parametrisation `φ : t ↦ a + t•v` (an isometry on the line, `‖v‖=1`): the pieces
`Tₙ = {t∈[0,1] | φ t ∈ Uₙ}` cover `[0,1]`, and each has 1-D length `≤ ediam(Tₙ) ≤ ediam(Uₙ)` (since
`φ` is an isometry and `Tₙ`'s image lies in `Uₙ`). Countable subadditivity then gives
`1 = vol[0,1] ≤ ∑ vol(Tₙ) ≤ ∑ ediam(Uₙ)`. (Works for arbitrary — non-measurable — `Uₙ`, since
`volume` is an outer measure: `Real.volume_le_diam` and `measure_iUnion_le` need no measurability.)
This is the `d = 1` Hausdorff content bound from a *single* direction; the `d>1` bound needs the
many-direction Córdoba pigeonhole on top of this.

The refined form `exists_pullback_cover` exposes the intermediate `1 ≤ ∑ₙ volume(Tₙ)` *before*
collapsing each `volume(Tₙ)` to `ediam(Uₙ)`, together with the pullback pieces `Tₙ ⊆ [0,1]`. Keeping
the covered *length* `volume(Tₙ)` (not just `ediam(Uₙ)`) is what the dyadic scale pigeonhole consumes:
the per-direction total `1` is regrouped by scale, and the dominant scale's covered length feeds the
localized-Córdoba count. -/

/-- **Covered unit segment ⟹ pullback pieces of total length `≥ 1` (refined length bound, sub-brick
(a′)).** Returns the unit-speed pullback `Tₙ = {t∈[0,1] | a+t•v ∈ Uₙ}`: each `Tₙ ⊆ [0,1]`, has length
`volume(Tₙ) ≤ ediam(Uₙ)`, and the lengths total `≥ 1`. The exposed `volume(Tₙ)` (the covered length,
not yet collapsed to `ediam`) is the input to the dyadic scale pigeonhole `exists_dominant_scale`. -/
theorem exists_pullback_cover {a v : Plane} (hv : ‖v‖ = 1) {U : ℕ → Set Plane}
    (hcov : affineSegment ℝ a (a + v) ⊆ ⋃ n, U n) :
    ∃ T : ℕ → Set ℝ, (∀ n, T n ⊆ Icc (0 : ℝ) 1) ∧
      (∀ n, volume (T n) ≤ Metric.ediam (U n)) ∧ 1 ≤ ∑' n, volume (T n) := by
  set φ : ℝ → Plane := fun t => a + t • v with hφ
  set T : ℕ → Set ℝ := fun n => Icc (0 : ℝ) 1 ∩ φ ⁻¹' (U n) with hT
  -- the pullback pieces cover `[0,1]`
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ n, T n := by
    intro t ht
    have hmem : φ t ∈ affineSegment ℝ a (a + v) := by
      rw [affineSegment_eq]; exact ⟨t, ht, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcov hmem)
    exact mem_iUnion.mpr ⟨n, ht, hn⟩
  -- `φ` is a unit-speed isometry on the line
  have hiso : ∀ s t : ℝ, edist s t = edist (φ s) (φ t) := by
    intro s t
    have hsub : φ s - φ t = (s - t) • v := by simp only [hφ, sub_smul]; abel
    have hd : dist (φ s) (φ t) = dist s t := by
      rw [dist_eq_norm, hsub, norm_smul, hv, mul_one, Real.norm_eq_abs, Real.dist_eq]
    rw [edist_dist, edist_dist, hd]
  -- per piece: `Tₙ ⊆ [0,1]` and `vol(Tₙ) ≤ ediam(Tₙ) ≤ ediam(Uₙ)`
  have h01 : ∀ n, T n ⊆ Icc (0 : ℝ) 1 := fun n => inter_subset_left
  have h3 : ∀ n, volume (T n) ≤ Metric.ediam (U n) := by
    intro n
    refine le_trans (Real.volume_le_diam (T n)) ?_
    rw [Metric.ediam_le_iff]
    intro s hs t ht
    rw [hiso s t]
    exact Metric.edist_le_ediam_of_mem hs.2 ht.2
  -- assemble: `1 = vol[0,1] ≤ vol(⋃Tₙ) ≤ ∑ vol(Tₙ)`
  have hvol1 : volume (Icc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  refine ⟨T, h01, h3, ?_⟩
  calc (1 : ℝ≥0∞) = volume (Icc (0 : ℝ) 1) := hvol1.symm
    _ ≤ volume (⋃ n, T n) := measure_mono hcover
    _ ≤ ∑' n, volume (T n) := measure_iUnion_le _

theorem one_le_tsum_ediam_of_covers {a v : Plane} (hv : ‖v‖ = 1) {U : ℕ → Set Plane}
    (hcov : affineSegment ℝ a (a + v) ⊆ ⋃ n, U n) :
    1 ≤ ∑' n, Metric.ediam (U n) := by
  obtain ⟨T, _, h3, h1⟩ := exists_pullback_cover hv hcov
  exact le_trans h1 (ENNReal.tsum_le_tsum h3)

/-- **Per-direction dominant scale (sub-brick (a′), assembled).** For a Kakeya direction's covered
unit segment and any dyadic scale function `g : ℕ → ℕ` on the cover pieces, there is a dominant scale
`j` whose pieces cover a length `≥ scaleWeight j ≳ 1/(j+1)²` of the segment. Combines the refined
length bound `exists_pullback_cover` with the scale pigeonhole `exists_dominant_scale`. The next step
(sub-brick (b)) pigeonholes this dominant scale across the direction net to a single global `j*`. -/
theorem exists_dominant_scale_of_covers {a v : Plane} (hv : ‖v‖ = 1) {U : ℕ → Set Plane}
    (hcov : affineSegment ℝ a (a + v) ⊆ ⋃ n, U n) (g : ℕ → ℕ) :
    ∃ T : ℕ → Set ℝ, (∀ n, T n ⊆ Icc (0 : ℝ) 1) ∧ (∀ n, volume (T n) ≤ Metric.ediam (U n)) ∧
      ∃ j : ℕ, scaleWeight j ≤ ∑' n : (g ⁻¹' {j} : Set ℕ), volume (T n) := by
  obtain ⟨T, h01, h3, h1⟩ := exists_pullback_cover hv hcov
  exact ⟨T, h01, h3, exists_dominant_scale g h1⟩

/-! ### End-to-end at `d = 1`: the pipeline composes axiom-clean

`one_le_tsum_ediam_of_covers` already gives the `d = 1` content bound from a single Kakeya direction,
with no Córdoba pigeonhole needed (it is the geometrically trivial `dimH ≥ 1`). Wiring it through the
reduction proves `μH[1] S ≠ 0` with **zero** `sorry` — an anti-vacuity anchor that the whole
reduction/geometry stack actually composes to a genuine positive-Hausdorff-measure statement. The
`d > 1` upgrade (the real content) is what the multi-scale pigeonhole supplies on top. -/

/-- A planar Kakeya set has a `d = 1` Hausdorff content lower bound — directly from the covered unit
segment it contains, with constant `c = 1`. Axiom-clean (no `sorry`). -/
theorem kakeya_hausdorffContentBound_one {S : Set Plane} (h : IsKakeya S) :
    HausdorffContentBound S 1 := by
  refine ⟨1, one_pos, 1, one_ne_zero, fun t hcov _ => ?_⟩
  have hv : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single, norm_one]
  obtain ⟨a, ha⟩ := h _ hv
  have hb := one_le_tsum_ediam_of_covers hv (ha.trans hcov)
  simpa only [ENNReal.rpow_one] using hb

/-- **A planar Kakeya set has positive 1-dimensional Hausdorff measure.** End-to-end, axiom-clean
(`#print axioms`-clean, no `sorry`): the covered-segment length bound `one_le_tsum_ediam_of_covers`
fed through the cover-content reduction `hausdorffMeasure_ne_zero_of_contentBound`. Mathematically the
weak `dimH ≥ 1` (a segment already has dimension 1), but it exercises the full K5 reduction stack and
certifies it composes. -/
theorem hausdorffMeasure_one_ne_zero {S : Set Plane} (h : IsKakeya S) : μH[(1 : ℝ)] S ≠ 0 :=
  hausdorffMeasure_ne_zero_of_contentBound one_pos (kakeya_hausdorffContentBound_one h)

end LeanFormalizations.Kakeya2D

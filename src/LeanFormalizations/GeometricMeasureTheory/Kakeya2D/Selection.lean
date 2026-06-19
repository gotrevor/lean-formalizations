/-
# Narrowing the measurable-selection crux to a standard Jankov–von Neumann statement

The headline `davies_kakeya_2d` rests (after the rewire in `Wiring.lean`) on the lone axiom
`kakeya_measurable_selection`: a **measurable** base-point selection `a : ℝ → Plane` whose unit
segment over each direction `θ ∈ [0,1]` lies *pointwise* in a measurable cover `⋃ C n` of the Kakeya
set. That pointwise form is logically **coanalytic-uniformization (Kondô) strength**: the graph
`G = {(θ,p) : ∀t∈[0,1], p+t·dirθ ∈ ⋃ C n}` is the co-projection of a Borel set along the compact fibre
`[0,1]`, hence Π¹₁, and selecting from it needs Π¹₁-uniformization.

**This file narrows that crux.** The key observation is that the continuum route's downstream consumer
(`MeasurableRoute.exists_continuum_dominant_scale`) only ever uses the **a.e.** statement
`1 ≤ vol{t∈[0,1] : aθ + t·dirθ ∈ ⋃ C n}` (covered length `= 1`), *not* pointwise membership: it passes
`hcov` through a single `measure_mono`/`one_le_tsum_volume_fiber_union` step. With only a.e. coverage
required, the selection graph becomes

  `G_ae = {(θ,p) : 1 ≤ vol{t∈[0,1] : p + t·dirθ ∈ ⋃ C n}}`,

which is **Borel** (the covered length is jointly measurable in `(θ,p)`), so the selection is plain
**Jankov–von Neumann / von Neumann** strength — a Borel set with non-empty sections admits a
universally-measurable (a.e.-measurable) selector. That is the standard, citable "measurable selection
theorem", strictly weaker than Π¹₁-uniformization.

What is **proven here** (no new axioms; JvN enters as an explicit hypothesis, mirroring `Wiring`'s
`hsel` pattern):

* `measurable_coveredLength_prod` — the covered length `φ(θ,p) = vol{t∈[0,1] : p+t·dirθ ∈ F}` is
  **jointly measurable** in `(θ,p)` (Fubini), so `G_ae` is Borel;
* `isKakeya_exists_aeCover` — `IsKakeya S` gives, for every direction `θ`, a base point with the *full*
  unit segment in `F ⊇ S`, hence covered length `= 1` (so `G_ae`'s section over each `θ` is non-empty);
* `kakeya_aeMeasurable_selection_of_jvn` — **the reduction**: from an abstract Borel-graph JvN selector
  (hypothesis `jvn`), the Kakeya a.e.-measurable selection follows. All Kakeya-specific geometry and
  measurability is discharged; the only remaining content is the Kakeya-agnostic `jvn`.

**Remaining to fully discharge (next laps):** (i) the abstract `jvn` itself — Jankov–von Neumann
uniformization of a Borel set, i.e. mathlib's missing measurable-selection theorem (it has `AnalyticSet`
+ its closure/projection API in `MeasureTheory/Constructions/Polish/Basic.lean`, but neither
universal measurability of analytic sets nor the Souslin-scheme selector); (ii) upgrading the
`MeasurableRoute`/`Wiring` spine from `Measurable a` + pointwise coverage to `AEMeasurable a` + a.e.
coverage (mechanical: `exists_continuum_dominant_scale` already only consumes the measure bound). See
`ON-LINE-REQUEST.md` and `CASE_B_ANALYSIS.md`.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.MeasurableRoute
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Wiring
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **Joint measurability of the covered length.** For a measurable target `F ⊆ Plane`, the covered
length `φ(θ,p) = vol{t∈[0,1] : p + t·dirθ ∈ F}` is measurable in the pair `(θ,p) ∈ ℝ × Plane`. This is
the two-variable companion of `measurable_coveredLength` (which fixes a base map `a`); it is what makes
the a.e.-coverage selection graph Borel. Proof: the joint map `(t,θ,p) ↦ p + t·dirθ` is measurable, so
the slab `{(t,(θ,p)) : t∈[0,1] ∧ p+t·dirθ ∈ F}` is measurable, and Fubini
(`measurable_measure_prodMk_right`, Lebesgue measure on the `t`-axis is `SFinite`) integrates out `t`. -/
theorem measurable_coveredLength_prod {F : Set Plane} (hF : MeasurableSet F) :
    Measurable fun q : ℝ × Plane =>
      volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 + t • dir q.1 ∈ F} := by
  -- joint map `(t,(θ,p)) ↦ p + t • dir θ`
  have hΦ : Measurable (fun r : ℝ × (ℝ × Plane) => r.2.2 + r.1 • dir r.2.1) :=
    measurable_snd.snd.add (measurable_fst.smul (measurable_dir.comp measurable_snd.fst))
  -- the slab is measurable in `ℝ × (ℝ × Plane)`
  have hs : MeasurableSet
      {r : ℝ × (ℝ × Plane) | r.1 ∈ Set.Icc (0 : ℝ) 1 ∧ r.2.2 + r.1 • dir r.2.1 ∈ F} := by
    rw [Set.setOf_and]
    exact (measurable_fst measurableSet_Icc).inter (hΦ hF)
  exact measurable_measure_prodMk_right hs

/-- **`IsKakeya` gives full (hence a.e.) coverage along every direction.** For a Kakeya set `S ⊆ F`,
every direction `θ` has a base point `p` whose entire unit segment `t ↦ p + t·dirθ` (`t∈[0,1]`) lies in
`F`, so the covered length is the full `vol[0,1] = 1`. This is the geometric content that makes each
section of the a.e.-coverage selection graph non-empty. -/
theorem isKakeya_exists_aeCover {S : Set Plane} (h : IsKakeya S) {F : Set Plane} (hSF : S ⊆ F)
    (θ : ℝ) :
    ∃ p : Plane, volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ p + t • dir θ ∈ F} = 1 := by
  obtain ⟨p, hp⟩ := h (dir θ) (norm_dir θ)
  refine ⟨p, ?_⟩
  -- the whole segment lies in `F`
  have hfull : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t • dir θ ∈ F := by
    intro t ht
    have hmem : p + t • dir θ ∈ affineSegment ℝ p (p + dir θ) := by
      rw [affineSegment]
      refine ⟨t, ht, ?_⟩
      rw [AffineMap.lineMap_apply_module', show (p + dir θ) - p = dir θ from by abel]
      abel
    exact hSF (hp hmem)
  -- so the covered set is all of `[0,1]`
  have hset : {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ p + t • dir θ ∈ F} = Set.Icc (0 : ℝ) 1 := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    exact ⟨fun hh => hh.1, fun ht => ⟨ht, hfull t ⟨ht.1, ht.2⟩⟩⟩
  rw [hset, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- **The reduction: Kakeya a.e.-measurable selection from an abstract JvN selector.**

Given an abstract Borel-graph measurable selector `jvn` — for any *measurable* `G ⊆ ℝ × Plane` whose
section over each `θ ∈ [0,1]` is non-empty, an a.e.-measurable `a : ℝ → Plane` with `(θ, a θ) ∈ G` for
all `θ ∈ [0,1]` — the **Kakeya a.e.-measurable base-point selection** follows: a measurable cover `C` of
a Kakeya set `S` admits an a.e.-measurable `a` whose unit segment over each `θ ∈ [0,1]` covers length
`≥ 1` in `⋃ C n`.

All Kakeya-specific work is discharged here: the selection graph `G_ae` is Borel
(`measurable_coveredLength_prod`) with non-empty sections (`isKakeya_exists_aeCover`). The only
remaining input, `jvn`, is the standard Jankov–von Neumann / von Neumann measurable-selection theorem —
Kakeya-agnostic and citable, and strictly weaker than the Π¹₁-uniformization that the *pointwise*
selection `kakeya_measurable_selection` would need. -/
theorem kakeya_aeMeasurable_selection_of_jvn
    (jvn : ∀ G : Set (ℝ × Plane), MeasurableSet G →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∃ p : Plane, (θ, p) ∈ G) →
        ∃ a : ℝ → Plane, AEMeasurable a ∧ ∀ θ ∈ Set.Icc (0 : ℝ) 1, (θ, a θ) ∈ G)
    {S : Set Plane} (h : IsKakeya S) (C : ℕ → Set Plane) (hC : ∀ n, MeasurableSet (C n))
    (hcov : S ⊆ ⋃ n, C n) :
    ∃ a : ℝ → Plane, AEMeasurable a ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        1 ≤ volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • dir θ ∈ ⋃ n, C n} := by
  set F : Set Plane := ⋃ n, C n with hFdef
  have hF : MeasurableSet F := MeasurableSet.iUnion hC
  -- the a.e.-coverage selection graph, Borel by joint measurability
  set G : Set (ℝ × Plane) :=
    {q : ℝ × Plane | 1 ≤ volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 + t • dir q.1 ∈ F}} with hGdef
  have hG : MeasurableSet G :=
    measurableSet_le measurable_const (measurable_coveredLength_prod hF)
  -- non-empty sections from the Kakeya structure
  have hsec : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∃ p : Plane, (θ, p) ∈ G := by
    intro θ _
    obtain ⟨p, hp⟩ := isKakeya_exists_aeCover h hcov θ
    exact ⟨p, by rw [hGdef, Set.mem_setOf_eq, hp]⟩
  obtain ⟨a, ha, hsel⟩ := jvn G hG hsec
  exact ⟨a, ha, fun θ hθ => hsel θ hθ⟩

/-! ### First step toward discharging `kakeya_borel_selection` (the von Neumann route) -/

/-- **The projection of the Borel selection graph is analytic, and `[0,1]` lies inside it.** This is
the opening move of the von Neumann / Jankov–von Neumann selection proof for `kakeya_borel_selection`:
the parameter set actually covered by the graph is `Prod.fst '' G`, which is **analytic** (the image of
a measurable/Borel set under the continuous projection `fst`, via `MeasurableSet.analyticSet_image`),
and the non-empty-sections hypothesis puts the whole direction arc `[0,1]` inside it. What remains for
the full selector is the Souslin-scheme / "von Neumann derivative" construction on `G` (needing
analytic-set universal measurability — the genuine mathlib gap; see the file header and
`ON-LINE-REQUEST.md` UPDATE 6). Proven here as an axiom-clean down payment. -/
theorem analyticSet_proj_and_Icc_subset
    (G : Set (ℝ × Plane)) (hG : MeasurableSet G)
    (hsec : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∃ p : Plane, (θ, p) ∈ G) :
    AnalyticSet (Prod.fst '' G) ∧ Set.Icc (0 : ℝ) 1 ⊆ Prod.fst '' G := by
  refine ⟨hG.analyticSet_image measurable_fst, fun θ hθ => ?_⟩
  obtain ⟨p, hp⟩ := hsec θ hθ
  exact ⟨(θ, p), hp, rfl⟩

/-! ### The elementary discharge: measurable selection against an OPEN cover (no DST) -/

open scoped Classical in
/-- **Elementary measurable base-point selection against an OPEN cover (von Neumann–free).**

For a Kakeya set `S` contained in an **open** set `F ⊆ Plane`, there is a genuinely **measurable**
base-point selection `a : ℝ → Plane` whose unit segment over *every* direction `θ` covers the full
length `1` inside `F`:  `1 ≤ vol{t∈[0,1] : a θ + t·dir θ ∈ F}`.

This **discharges the selection crux elementarily for open targets** — no descriptive set theory, no
Jankov–von Neumann, no analytic-set universal measurability. The decisive use of openness: for each
direction `θ`, `IsKakeya` supplies a base point `p` whose entire unit segment (a **compact** set) lies
in `F`, so a whole tube around it lies in `F` (`IsCompact.exists_thickening_subset_open`); hence *any*
base point within that tube — in particular one taken from a fixed countable dense sequence
`q = denseSeq` — has its full segment in `F`, giving covered length `= 1`. The selector
`a θ := q (Nat.find …)` picks the first dense point that works; it is measurable because each section
`{θ : 1 ≤ vol{t : q n + t·dir θ ∈ F}}` is measurable (`measurable_coveredLength`) and `measurable_find`
assembles the first-hit index over the (total) `∀ θ, ∃ n` witness. The downstream Hausdorff content
bound only ever consumes this measure form, so this fully replaces the abstract selection axiom once the
cover is fattened to an open superset (`Wiring`). -/
theorem exists_measurable_selection_of_isOpen
    {S : Set Plane} (h : IsKakeya S) {F : Set Plane} (hFo : IsOpen F) (hSF : S ⊆ F) :
    ∃ a : ℝ → Plane, Measurable a ∧
      ∀ θ : ℝ, 1 ≤ volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • dir θ ∈ F} := by
  classical
  have hFm : MeasurableSet F := hFo.measurableSet
  set q : ℕ → Plane := TopologicalSpace.denseSeq Plane with hqdef
  set P : ℝ → ℕ → Prop := fun θ n =>
    1 ≤ volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ q n + t • dir θ ∈ F} with hPdef
  -- (1) every direction has a "good" dense base point: compact segment ⊆ open F ⟹ a tube ⊆ F.
  have hex : ∀ θ : ℝ, ∃ n, P θ n := by
    intro θ
    obtain ⟨p, hp⟩ := h (dir θ) (norm_dir θ)
    set seg : Set Plane := (fun t : ℝ => p + t • dir θ) '' Set.Icc (0 : ℝ) 1 with hsegdef
    have hcont : Continuous (fun t : ℝ => p + t • dir θ) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hsegc : IsCompact seg := isCompact_Icc.image hcont
    have hsegF : seg ⊆ F := by
      rintro x ⟨t, ht, rfl⟩
      refine hSF (hp ?_)
      rw [affineSegment]
      refine ⟨t, ht, ?_⟩
      rw [AffineMap.lineMap_apply_module', show (p + dir θ) - p = dir θ from by abel]
      abel
    obtain ⟨δ, hδ, hthick⟩ := hsegc.exists_thickening_subset_open hFo hsegF
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq Plane) p δ hδ
    refine ⟨n, ?_⟩
    have hfull : {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ q n + t • dir θ ∈ F} = Set.Icc (0 : ℝ) 1 := by
      ext t
      constructor
      · rintro ⟨ht, _⟩; exact ht
      · intro ht
        refine ⟨ht, hthick ?_⟩
        rw [Metric.mem_thickening_iff]
        refine ⟨p + t • dir θ, ⟨t, ht, rfl⟩, ?_⟩
        calc dist (q n + t • dir θ) (p + t • dir θ)
            = dist (q n) p := by rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
          _ = dist p (q n) := dist_comm _ _
          _ < δ := hn
    show 1 ≤ volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ q n + t • dir θ ∈ F}
    rw [hfull, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  -- (2) the first-hit selector is measurable.
  have hPset : ∀ n, MeasurableSet {θ : ℝ | P θ n} := fun n =>
    measurableSet_le measurable_const
      (measurable_coveredLength measurable_const measurable_dir hFm)
  refine ⟨fun θ => q (Nat.find (hex θ)),
    measurable_from_nat.comp (measurable_find hex hPset), fun θ => ?_⟩
  exact Nat.find_spec (hex θ)

/-- **Per-piece open fattening with controlled `ediam^d` overshoot.** A set of diameter `x ≤ 1/2`
can be thickened by a positive radius `δ` so the result still has diameter `≤ 1` and its `d`-th power
overshoots by less than any prescribed `η > 0`: `(x + 2δ)^d ≤ x^d + η`. This is the analytic content
that lets the open-cover route pay only a vanishing price over the original closed cover. Proof: the
map `δ ↦ (x + ofReal(2δ))^d` is continuous at `0` with value `x^d`, so it is `< x^d + η` on a
neighbourhood; pick `δ` there, capped at `1/4` for the `≤ 1` bound. -/
theorem exists_thickening_radius_rpow_le {x : ℝ≥0∞} (hx : x ≤ 1 / 2) {d : ℝ} (hd0 : 0 < d)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ x + ENNReal.ofReal (2 * δ) ≤ 1 ∧
      (x + ENNReal.ofReal (2 * δ)) ^ d ≤ x ^ d + η := by
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hx
  have hxdtop : x ^ d ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hd0.le hxtop
  have hlt : x ^ d < x ^ d + η := ENNReal.lt_add_right hxdtop hη.ne'
  -- continuity of `δ ↦ (x + ofReal(2δ))^d` at `0`
  have hca : ContinuousAt (fun δ : ℝ => (x + ENNReal.ofReal (2 * δ)) ^ d) 0 :=
    (ENNReal.continuous_rpow_const.continuousAt).comp
      ((continuous_const.add
        (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id))).continuousAt)
  have h0 : (fun δ : ℝ => (x + ENNReal.ofReal (2 * δ)) ^ d) 0 = x ^ d := by
    simp
  have hev : ∀ᶠ δ : ℝ in nhds 0, (x + ENNReal.ofReal (2 * δ)) ^ d < x ^ d + η := by
    have htends : Filter.Tendsto (fun δ : ℝ => (x + ENNReal.ofReal (2 * δ)) ^ d)
        (nhds 0) (nhds (x ^ d)) := by simpa using hca.tendsto
    exact htends.eventually (Iio_mem_nhds hlt)
  obtain ⟨ε, hεpos, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 4) (1 / 4), lt_min (by positivity) (by norm_num), ?_, ?_⟩
  · -- `x + 2δ ≤ 1/2 + 1/2 = 1`
    have hhalf : ENNReal.ofReal (2 * (min (ε / 4) (1 / 4) : ℝ)) ≤ 1 / 2 := by
      calc ENNReal.ofReal (2 * (min (ε / 4) (1 / 4) : ℝ))
          ≤ ENNReal.ofReal (1 / 2) :=
            ENNReal.ofReal_le_ofReal (by have := min_le_right (ε / 4) (1 / 4 : ℝ); linarith)
        _ = 1 / 2 := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    calc x + ENNReal.ofReal (2 * (min (ε / 4) (1 / 4) : ℝ))
        ≤ 1 / 2 + 1 / 2 := add_le_add hx hhalf
      _ = 1 := ENNReal.add_halves 1
  · have hd : dist ((min (ε / 4) (1 / 4) : ℝ)) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      calc (min (ε / 4) (1 / 4) : ℝ) ≤ ε / 4 := min_le_left _ _
        _ < ε := by linarith
    exact (hball hd).le

/-- **The Hausdorff content bound for a planar Kakeya set — fully elementary, NO axioms.**

Combines the open-cover measurable selection (`exists_measurable_selection_of_isOpen`) with the
cover-agnostic Córdoba spine (`Wiring.content_bound_step`): every countable cover of `S` is fattened to
an **open** cover at vanishing `ediam^d` cost (`exists_thickening_radius_rpow_le`), the elementary
selection runs against that open cover (full coverage `= 1` on every direction), the spine bounds the
content of the fattened cover, and the per-cover overshoot `η` is sent to `0`
(`ENNReal.le_of_forall_pos_le_add`). This **eliminates the descriptive-set-theory crux entirely**: the
selection is `Classical.choice`-clean, so the headline rests on no measurable-selection axiom. -/
theorem kakeya_hausdorffContentBound_elementary
    {S : Set Plane} (h : IsKakeya S) {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2) :
    HausdorffContentBound S d := by
  obtain ⟨cR, hcRpos, hcR⟩ := content_ratio_lower hd0 hd2
  set D : ℝ≥0∞ := volume (Metric.closedBall (0 : Plane) 1) with hD
  have hDpos : 0 < D := volume_closedBall_one_pos
  have hDtop : D ≠ ⊤ := volume_closedBall_one_ne_top
  refine ⟨1 / 2, by norm_num, D⁻¹ * ENNReal.ofReal cR, ?_, ?_⟩
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hDtop) (ENNReal.ofReal_pos.mpr hcRpos).ne'
  · intro t hcov hdiam
    rcases eq_or_ne (∑' n, Metric.ediam (t n) ^ d) ⊤ with htop | hfintop
    · rw [htop]; exact le_top
    refine ENNReal.le_of_forall_pos_le_add (fun η hηpos _ => ?_)
    -- per-piece overshoot budget `ηn` with `∑ ηn ≤ η`
    set ηn : ℕ → ℝ≥0∞ := fun n => (η : ℝ≥0∞) * (1 / 2) ^ (n + 1) with hηndef
    have hηnpos : ∀ n, 0 < ηn n := fun n =>
      ENNReal.mul_pos (by exact_mod_cast hηpos.ne') (pow_ne_zero _ (by norm_num))
    have hgeo : ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ (n + 1) = 1 := by
      have hsub : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 :=
        ENNReal.sub_eq_of_eq_add (by norm_num) (ENNReal.add_halves 1).symm
      have hinv : ((1 : ℝ≥0∞) / 2)⁻¹ = 2 := by rw [one_div, inv_inv]
      calc ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ (n + 1)
          = (∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ n) * (1 / 2) := by
            simp_rw [pow_succ]; rw [ENNReal.tsum_mul_right]
        _ = 1 := by rw [ENNReal.tsum_geometric, hsub, hinv]; rw [ENNReal.mul_div_cancel] <;> norm_num
    have hηnsum : ∑' n, ηn n ≤ (η : ℝ≥0∞) := by
      rw [hηndef, ENNReal.tsum_mul_left, hgeo, mul_one]
    -- choose fattening radii (one per cover piece)
    have hfat : ∀ n, ∃ δ : ℝ, 0 < δ ∧ Metric.ediam (t n) + ENNReal.ofReal (2 * δ) ≤ 1 ∧
        (Metric.ediam (t n) + ENNReal.ofReal (2 * δ)) ^ d ≤ Metric.ediam (t n) ^ d + ηn n :=
      fun n => exists_thickening_radius_rpow_le (hdiam n) hd0 (hηnpos n)
    choose δ hδpos hδle1 hδrpow using hfat
    set V : ℕ → Set Plane := fun n => Metric.thickening (δ n) (t n) with hVdef
    have hVopen : ∀ n, IsOpen (V n) := fun n => Metric.isOpen_thickening
    have hVmeas : ∀ n, MeasurableSet (V n) := fun n => (hVopen n).measurableSet
    have htV : ∀ n, t n ⊆ V n := fun n => Metric.self_subset_thickening (hδpos n) (t n)
    have hVediam_le : ∀ n, Metric.ediam (V n) ≤ Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) := by
      intro n
      have hkey := Metric.ediam_thickening_le (s := t n) ((δ n).toNNReal)
      rw [Real.coe_toNNReal (δ n) (hδpos n).le] at hkey
      refine hkey.trans (le_of_eq ?_)
      congr 1
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      rfl
    have hVdiam : ∀ n, Metric.ediam (V n) ≤ 1 := fun n => (hVediam_le n).trans (hδle1 n)
    have hScov : S ⊆ ⋃ n, V n := hcov.trans (Set.iUnion_mono htV)
    have hFo : IsOpen (⋃ n, V n) := isOpen_iUnion hVopen
    -- the elementary measurable selection against the OPEN fattened cover
    obtain ⟨a, ha, hcovsel⟩ := exists_measurable_selection_of_isOpen h hFo hScov
    have hcov_ae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.Icc (0 : ℝ) 1 →
        1 ≤ volume {τ : ℝ | τ ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + τ • dir θ ∈ ⋃ n, V n} :=
      Filter.Eventually.of_forall (fun θ _ => hcovsel θ)
    have hstep := content_bound_step hd0 hcRpos hcR V hVmeas hVdiam a ha hcov_ae
    -- ∑ ediam(V)^d ≤ ∑ ediam(t)^d + η
    have hsum_le : ∑' n, Metric.ediam (V n) ^ d ≤ ∑' n, Metric.ediam (t n) ^ d + (η : ℝ≥0∞) := by
      calc ∑' n, Metric.ediam (V n) ^ d
          ≤ ∑' n, (Metric.ediam (t n) ^ d + ηn n) :=
            ENNReal.tsum_le_tsum (fun n =>
              (ENNReal.rpow_le_rpow (hVediam_le n) hd0.le).trans (hδrpow n))
        _ = (∑' n, Metric.ediam (t n) ^ d) + ∑' n, ηn n := ENNReal.tsum_add
        _ ≤ (∑' n, Metric.ediam (t n) ^ d) + (η : ℝ≥0∞) := add_le_add le_rfl hηnsum
    exact hstep.trans hsum_le

/-! ### The lone selection axiom — now DISCHARGED elementarily (see above)

The former axiom `kakeya_borel_selection` (the textbook von Neumann / Jankov–von Neumann measurable
selection for an arbitrary Borel graph) has been **removed**: the headline no longer needs it. The
Kakeya selection is obtained *elementarily* by `exists_measurable_selection_of_isOpen` once the cover
is fattened to an open superset (`kakeya_hausdorffContentBound_elementary`) — a compact unit segment
inside an open set has a tube neighbourhood, so a dense base point gives full coverage, no descriptive
set theory required. The abstract JvN *reduction* `kakeya_aeMeasurable_selection_of_jvn` and the
projection-is-analytic down payment `analyticSet_proj_and_Icc_subset` are kept above as honest,
hypothesis-gated structure (they introduce no axiom). -/

/-- **The concrete crux (Davies 1971, measure form).** For a Kakeya set `S ⊆ ℝ²`, every
`d`-dimensional Hausdorff measure with `d < 2` is positive. Free `ℝ≥0∞`-density wrapper around
`kakeya_hausdorffContentBound_elementary`; the `d = 0` endpoint comes from monotonicity of `μH` in `d`
against the `d = 1` content bound. -/
theorem hausdorffMeasure_pos_of_isKakeya
    (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    ∀ d : ℝ≥0, (d : ℝ≥0∞) < 2 → μH[(d : ℝ)] S ≠ 0 := by
  have key : ∀ e : ℝ, 0 < e → e < 2 → μH[e] S ≠ 0 := fun e he0 he2 =>
    hausdorffMeasure_ne_zero_of_contentBound he0 (kakeya_hausdorffContentBound_elementary h he0 he2)
  intro d hd
  rcases eq_or_lt_of_le (zero_le d) with hd0 | hd0
  · have hd0R : (d : ℝ) = 0 := by exact_mod_cast hd0.symm
    have hmono : μH[(1 : ℝ)] S ≤ μH[(d : ℝ)] S := by
      rw [hd0R]; exact Measure.hausdorffMeasure_mono (by norm_num) S
    exact fun hz => key 1 one_pos (by norm_num) (le_antisymm (hz ▸ hmono) (zero_le _))
  · have hd2R : (d : ℝ) < 2 := by exact_mod_cast hd
    exact key d (by exact_mod_cast hd0) hd2R

/-- **Davies 1971.** A Kakeya set in `ℝ²` has Hausdorff dimension at least `2` — the genuine content of
the planar Kakeya conjecture (the upper bound is free). Frostman's lemma lifts each `μH[d] S ≠ 0`
(`d < 2`) to `↑d ≤ dimH S`, and the supremum over `d < 2` reaches `2`. The headline is now **fully
machine-checked with no mathematical axioms** (`#print axioms = [propext, Classical.choice, Quot.sound]`):
the selection crux is discharged elementarily via the open-cover route, no descriptive set theory. -/
theorem two_le_dimH (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    2 ≤ dimH S := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  exact le_dimH_of_hausdorffMeasure_ne_zero (hausdorffMeasure_pos_of_isKakeya S h r hr)

end LeanFormalizations.Kakeya2D

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

/-! ### The headline, routed through the standard Jankov–von Neumann selection -/

/-- **The Kakeya measurable selection, as a Kakeya-agnostic Jankov–von Neumann statement.**

The lone remaining axiom of the headline. It is the **standard measurable-selection theorem**: a Borel
set `G ⊆ ℝ × Plane` (here `ℝ` is the direction parameter, Plane the base point) whose section over
every `θ ∈ [0,1]` is non-empty admits a selector `a : ℝ → Plane` that is **a.e.-measurable** (w.r.t.
Lebesgue measure) with `(θ, a θ) ∈ G` for all `θ ∈ [0,1]`. This is Jankov–von Neumann uniformization
(the von Neumann selection theorem) — a consequence of analytic sets being universally measurable —
which `mathlib` v4.29.1 lacks: it has `AnalyticSet` and its closure/projection API
(`MeasureTheory/Constructions/Polish/Basic.lean`) but neither universal measurability of analytic sets
nor the Souslin-scheme selector.

This statement carries **no Kakeya content whatsoever** — every Kakeya-specific fact (non-empty Borel
sections via `IsKakeya`, joint measurability of the covered length) is *proven* in
`kakeya_aeMeasurable_selection_of_jvn` and the bricks above. It is strictly weaker than Π¹₁
(coanalytic) uniformization: working with the **a.e.-coverage** graph (covered length `= 1`) keeps the
graph Borel, where pointwise segment-containment would make it coanalytic. See the file header,
`ON-LINE-REQUEST.md`, `STATUS.md`. -/
axiom kakeya_borel_selection :
    ∀ G : Set (ℝ × Plane), MeasurableSet G →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∃ p : Plane, (θ, p) ∈ G) →
      ∃ a : ℝ → Plane, AEMeasurable a ∧ ∀ θ ∈ Set.Icc (0 : ℝ) 1, (θ, a θ) ∈ G

/-- **The Hausdorff content bound for a Kakeya set, via the standard JvN selection.** Composes the
proven reduction `kakeya_aeMeasurable_selection_of_jvn` (Kakeya geometry + measurability) with the
`AEMeasurable` wiring `kakeya_hausdorffContentBound_of_aeMeasurableSelection`, feeding both off the
Kakeya-agnostic axiom `kakeya_borel_selection`. -/
theorem kakeya_hausdorffContentBound_jvn
    {S : Set Plane} (h : IsKakeya S) {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2) :
    HausdorffContentBound S d := by
  refine kakeya_hausdorffContentBound_of_aeMeasurableSelection hd0 hd2 (fun C hC hcov => ?_)
  obtain ⟨a, ha, hcov'⟩ :=
    kakeya_aeMeasurable_selection_of_jvn kakeya_borel_selection h C hC hcov
  exact ⟨a, ha, Filter.Eventually.of_forall (fun θ hθ => hcov' θ hθ)⟩

/-- **The concrete crux (Davies 1971, measure form).** For a Kakeya set `S ⊆ ℝ²`, every
`d`-dimensional Hausdorff measure with `d < 2` is positive. Free `ℝ≥0∞`-density wrapper around
`kakeya_hausdorffContentBound_jvn`; the `d = 0` endpoint comes from monotonicity of `μH` in `d` against
the `d = 1` content bound. -/
theorem hausdorffMeasure_pos_of_isKakeya
    (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    ∀ d : ℝ≥0, (d : ℝ≥0∞) < 2 → μH[(d : ℝ)] S ≠ 0 := by
  have key : ∀ e : ℝ, 0 < e → e < 2 → μH[e] S ≠ 0 := fun e he0 he2 =>
    hausdorffMeasure_ne_zero_of_contentBound he0 (kakeya_hausdorffContentBound_jvn h he0 he2)
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
(`d < 2`) to `↑d ≤ dimH S`, and the supremum over `d < 2` reaches `2`. The headline now rests on the
single Kakeya-agnostic axiom `kakeya_borel_selection` (Jankov–von Neumann measurable selection). -/
theorem two_le_dimH (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    2 ≤ dimH S := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  exact le_dimH_of_hausdorffMeasure_ne_zero (hausdorffMeasure_pos_of_isKakeya S h r hr)

end LeanFormalizations.Kakeya2D

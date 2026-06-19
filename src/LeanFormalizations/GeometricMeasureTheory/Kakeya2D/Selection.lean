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

open MeasureTheory
open scoped ENNReal

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

end LeanFormalizations.Kakeya2D

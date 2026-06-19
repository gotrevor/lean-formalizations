/-
# The honest (measurable-selection) route — the wiring (W)

This file assembles the proven measurable-selection spine (`MeasurableRoute.lean`:
`measurable_coveredLength`, `exists_continuum_dominant_scale`, `exists_shift_ge_integral`,
`exists_continuum_caseA_numerator`, and the zero-`ediam` negligibility helpers) with the proven
single-scale content brick (`NetThinning.caseA_content`) into the headline-shaped Hausdorff content
bound, taking a **measurable base-point selection** as a *hypothesis* (zero new axioms).

This is the route that replaces the murky `Engine.kakeya_subresolution_content` (Case-B residual) with
the clean, citable Jankov–von Neumann measurable selection. Once `hsel` is discharged (the deep crux,
descriptive set theory), the headline `davies_kakeya_2d` can be rewired through this lemma and the
Case-B axiom retired. See `STATUS.md` ledger, `PENDING_WORK.md` §Reflection-2026-06-19, and
`Kakeya2D/CASE_B_ANALYSIS.md`.

Architecture note: this file imports BOTH `Engine` (for `content_ratio_lower`, `Plane`,
`HausdorffContentBound`) and `MeasurableRoute` (the spine). `Engine` does not import `MeasurableRoute`,
so the graph is acyclic; keeping the wiring here (not in `MeasurableRoute`) leaves room for the
eventual headline switch to call it from `Engine`-level code.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Engine
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.MeasurableRoute

open MeasureTheory
open scoped NNReal ENNReal

namespace LeanFormalizations.Kakeya2D

/-- **The Hausdorff content bound from a measurable base-point selection (the wiring W).**
Given, for every measurable cover `C` of the Kakeya set `S`, a **measurable** selection
`a : ℝ → Plane` whose unit segment over each direction `θ∈[0,1]` covers length `≥ 1` in `⋃ C n` —
the **a.e. / measure form** `1 ≤ vol{t∈[0,1] : aθ+t·dirθ ∈ ⋃ C n}`, which is all the continuum
pigeonhole consumes (`hsel`) — the Hausdorff content bound `HausdorffContentBound S d` holds for every
`d∈(0,2)`. No new axioms: the selection is a *hypothesis* here (the one deep input, Jankov–von Neumann,
to be discharged separately; the a.e./measure form makes its graph Borel — see `Selection.lean`). The
proof reduces the cover to closed pieces, takes the measurable selection, extracts
the cap-free continuum dominant scale + base angle via `exists_continuum_caseA_numerator`, and feeds
the genuine scale-`j` sub-fiber to `caseA_content` (the zero-`ediam` pieces are dropped via
`volume_coveredFiber_biUnion_subsingleton_zero` — they carry no covered length). NO Case B. -/
theorem kakeya_hausdorffContentBound_of_measurableSelection
    {S : Set Plane} {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2)
    (hsel : ∀ (C : ℕ → Set Plane), (∀ n, MeasurableSet (C n)) → S ⊆ ⋃ n, C n →
        ∃ a : ℝ → Plane, Measurable a ∧
          ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.Icc (0 : ℝ) 1 →
            1 ≤ volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • dir θ ∈ ⋃ n, C n}) :
    HausdorffContentBound S d := by
  obtain ⟨cR, hcRpos, hcR⟩ := content_ratio_lower hd0 hd2
  set D : ℝ≥0∞ := volume (Metric.closedBall (0 : Plane) 1) with hD
  have hDpos : 0 < D := volume_closedBall_one_pos
  have hDtop : D ≠ ⊤ := volume_closedBall_one_ne_top
  refine ⟨1, zero_lt_one, D⁻¹ * ENNReal.ofReal cR, ?_, ?_⟩
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hDtop) (ENNReal.ofReal_pos.mpr hcRpos).ne'
  · intro t hcov hdiam
    -- Reduce to closed cover pieces (same `ediam`, still covering `S`); they are measurable.
    set U : ℕ → Set Plane := fun n => closure (t n) with hUdef
    have hUcl : ∀ n, IsClosed (U n) := fun n => isClosed_closure
    have hUmeas : ∀ n, MeasurableSet (U n) := fun n => (hUcl n).measurableSet
    have hediam_eq : ∀ n, Metric.ediam (U n) = Metric.ediam (t n) :=
      fun n => Metric.ediam_closure (t n)
    have hUcov : S ⊆ ⋃ n, U n := hcov.trans (Set.iUnion_mono fun n => subset_closure)
    have hUdiam : ∀ n, Metric.ediam (U n) ≤ 1 := fun n => (hediam_eq n).le.trans (hdiam n)
    rw [show (∑' n, Metric.ediam (t n) ^ d) = ∑' n, Metric.ediam (U n) ^ d from by
      simp_rw [hediam_eq]]
    -- The measurable base-point selection (the hypothesis), already in a.e. / measure form.
    obtain ⟨a, ha, hcov_ae⟩ := hsel U hUmeas hUcov
    -- Uncapped dyadic scale function (zero-diameter pieces → bucket `0`).
    set g : ℕ → ℕ := fun n =>
      if 0 < (Metric.ediam (U n)).toReal then dyadicIdx (Metric.ediam (U n)).toReal else 0 with hgdef
    -- Cap-free continuum dominant scale + base angle, with the discrete numerator in hand.
    obtain ⟨j, α, hnum⟩ := exists_continuum_caseA_numerator ha hUmeas g hcov_ae
    -- Genuine scale-`j` sub-fiber (`ediam > 0`) and the null zero-`ediam` part.
    set s0 : Set ℕ := {n | g n = j ∧ 0 < (Metric.ediam (U n)).toReal} with hs0def
    set Z : Set ℕ := {n | g n = j ∧ (Metric.ediam (U n)).toReal = 0} with hZdef
    set A : ℕ → Set ℝ := fun i =>
      {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧
        a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
          ∈ ⋃ n ∈ s0, U n} with hAdef
    have hwne : ∀ i : ℕ, dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) ≠ 0 := by
      intro i h
      have h1 := norm_dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
      rw [h, norm_zero] at h1; exact one_ne_zero h1.symm
    have hAmeas : ∀ i, MeasurableSet (A i) := by
      intro i
      have hF : MeasurableSet (⋃ n ∈ s0, U n) :=
        MeasurableSet.biUnion (Set.to_countable _) (fun n _ => hUmeas n)
      have hmap : Measurable (fun u : ℝ =>
          a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)) :=
        measurable_const.add (measurable_id.smul measurable_const)
      rw [hAdef]
      simp only [Set.setOf_and, Set.setOf_mem_eq]
      exact measurableSet_Icc.inter (hmap hF)
    have hA01 : ∀ i, A i ⊆ Set.Icc (0 : ℝ) 1 := fun i u hu => hu.1
    have hAmem : ∀ i u, u ∈ A i ↔ (u ∈ Set.Icc (0 : ℝ) 1 ∧
        a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
          ∈ ⋃ n ∈ s0, U n) := fun i u => Iff.rfl
    -- Zero-`ediam` pieces are subsingletons.
    have hZsub : ∀ n ∈ Z, (U n).Subsingleton := by
      intro n hn
      have hne : Metric.ediam (U n) ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (hUdiam n)
      have hz : Metric.ediam (U n) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hn.2 with h | h
        · exact h
        · exact absurd h hne
      exact (Metric.ediam_eq_zero_iff).mp hz
    -- The fiber partitions into genuine ⊔ zero.
    have hsplit : (g ⁻¹' {j} : Set ℕ) = s0 ∪ Z := by
      ext n
      simp only [hs0def, hZdef, Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro hgn
        rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := Metric.ediam (U n))) with h | h
        · exact Or.inr ⟨hgn, h.symm⟩
        · exact Or.inl ⟨hgn, h⟩
      · rintro (⟨hgn, _⟩ | ⟨hgn, _⟩) <;> exact hgn
    -- Transport: the full-fiber covered length equals the genuine one (zero pieces null).
    have hs0sub : s0 ⊆ (g ⁻¹' {j} : Set ℕ) := fun n hn => hn.1
    have hUmono : (⋃ n ∈ s0, U n) ⊆ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), U n :=
      Set.biUnion_subset_biUnion_left hs0sub
    have hvol_eq : ∀ i : ℕ, volume {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧
          a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
            ∈ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), U n} = volume (A i) := by
      intro i
      have hAsub : A i ⊆ {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧
          a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
            ∈ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), U n} := by
        intro u hu
        obtain ⟨h1, h2⟩ := (hAmem i u).mp hu
        exact ⟨h1, hUmono h2⟩
      have hdiff : {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧
            a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
              ∈ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), U n} \ A i
          ⊆ {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧
            a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
              ∈ ⋃ n ∈ Z, U n} := by
        intro u hu
        obtain ⟨⟨h1, h2⟩, hnA⟩ := hu
        rw [hsplit, Set.biUnion_union] at h2
        rcases h2 with h2s | h2z
        · exact absurd ((hAmem i u).mpr ⟨h1, h2s⟩) hnA
        · exact ⟨h1, h2z⟩
      have hznull : volume {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧
          a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j) + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
            ∈ ⋃ n ∈ Z, U n} = 0 :=
        volume_coveredFiber_biUnion_subsingleton_zero (hwne i) (Set.to_countable Z) hZsub
          (Set.Icc (0 : ℝ) 1)
      refine measure_congr ((MeasureTheory.ae_eq_set).mpr ⟨measure_mono_null hdiff hznull, ?_⟩)
      rw [Set.diff_eq_empty.mpr hAsub, measure_empty]
    have hnum' : ENNReal.ofReal (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
        ≤ ∑ i ∈ Finset.range (2 ^ j), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * volume (A i) :=
      le_of_le_of_eq hnum (Finset.sum_congr rfl (fun i _ => by rw [hvol_eq i]))
    -- Window on the genuine sub-fiber (via `dyadicIdx_window`).
    have hwin : ∀ n ∈ s0, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ≤ Metric.ediam (U n)
        ∧ Metric.ediam (U n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
      intro n hn
      have hpos : 0 < (Metric.ediam (U n)).toReal := hn.2
      have hdi : dyadicIdx (Metric.ediam (U n)).toReal = j := by
        have : g n = j := hn.1
        simp only [hgdef] at this; rw [if_pos hpos] at this; exact this
      have hle1 : (Metric.ediam (U n)).toReal ≤ 1 := by
        have := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (hUdiam n); simpa using this
      have hwindow := dyadicIdx_window hpos hle1
      rw [hdi] at hwindow
      have heq : Metric.ediam (U n) = ENNReal.ofReal (Metric.ediam (U n)).toReal :=
        (ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num) (hUdiam n))).symm
      exact ⟨by rw [heq]; exact ENNReal.ofReal_le_ofReal hwindow.1.le,
        by rw [heq]; exact ENNReal.ofReal_le_ofReal hwindow.2⟩
    -- hscov: the image of `A i` lands in the genuine sub-fiber union.
    have hscov : ∀ i : ℕ, (fun u => a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)
        + u • dir (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)) '' (A i) ⊆ ⋃ n ∈ s0, U n := by
      intro i x hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact hu.2
    -- Finite/infinite split on the genuine sub-fiber.
    by_cases hfin : s0.Finite
    · have hbiUeq : (⋃ n ∈ s0, U n) = ⋃ n ∈ hfin.toFinset, U n := by
        ext x; simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
      refine caseA_content hd0.le hcRpos hcR j α (fun i => a (α + (i : ℝ) * (1 / 2 : ℝ) ^ j)) A
        hAmeas hA01 U hfin.toFinset (fun n hn => (hwin n (hfin.mem_toFinset.mp hn)).2)
        (fun n hn => (hwin n (hfin.mem_toFinset.mp hn)).1) (fun i => ?_) hnum'
      rw [← hbiUeq]; exact hscov i
    · -- infinite genuine sub-fiber ⟹ `∑' ediam^d = ⊤`
      have hinf : s0.Infinite := hfin
      haveI : Infinite ↥s0 := Set.infinite_coe_iff.mpr hinf
      have hεpos : 0 < ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ^ d :=
        ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top
      have h3 : ∑' _n : ↥s0, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ^ d = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hεpos.ne'
      have h2 : ∑' n : ↥s0, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ^ d
          ≤ ∑' n : ↥s0, Metric.ediam (U ↑n) ^ d :=
        ENNReal.tsum_le_tsum (fun n => ENNReal.rpow_le_rpow (hwin ↑n n.2).1 hd0.le)
      have h1 : ∑' n : ↥s0, Metric.ediam (U ↑n) ^ d ≤ ∑' n, Metric.ediam (U n) ^ d :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      have htop : ∑' n, Metric.ediam (U n) ^ d = ⊤ := top_le_iff.mp (h3 ▸ (h2.trans h1))
      rw [htop]; exact le_top

/-- **The measurable base-point selection — the lone remaining axiom (Jankov–von Neumann / KRN).**

For a planar Kakeya set `S` and *any* measurable cover `C` of `S`, there is a **measurable**
base-point selection `a : ℝ → Plane` whose unit segment over each direction `θ ∈ [0,1]` lies in
`⋃ C n`. `IsKakeya S` already supplies, for each direction, *some* base point whose unit segment lies
in `S ⊆ ⋃ C n` (`affineSegment ℝ a (a+dir θ) ⊆ S`) — but only via `Classical.choice`. The sole content
of this axiom is that the selection can be made **measurable in `θ`**.

This is a standard measurable-selection theorem — Kuratowski–Ryll-Nardzewski for the closed-valued
multifunction `B(θ) = {a : segment(a,θ) ⊆ ⋃ C n}`, or Jankov–von Neumann uniformization of its
(coanalytic) graph — which `mathlib` v4.29.1 does not yet provide (`SetTheory/Descriptive` is only
`Tree.lean`). It is **citable and believed-true**, and it replaces the murky bespoke Case-B residual
`Engine.kakeya_subresolution_content` (whose own truth a human auditor cannot easily check) as the
headline's lone axiom — a faithfulness upgrade. Discharging it (descriptive set theory) is the
standing crux. See `ON-LINE-REQUEST.md` UPDATE 5, `Kakeya2D/CASE_B_ANALYSIS.md`, `STATUS.md`. -/
axiom kakeya_measurable_selection {S : Set Plane} (h : IsKakeya S)
    (C : ℕ → Set Plane) (hC : ∀ n, MeasurableSet (C n)) (hcov : S ⊆ ⋃ n, C n) :
    ∃ a : ℝ → Plane, Measurable a ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, Set.Icc (0 : ℝ) 1 ⊆ {t | a θ + t • dir θ ∈ ⋃ n, C n}

/-- **The Hausdorff content bound for a Kakeya set (the honest measurable-selection route).**
Instantiates the wiring `kakeya_hausdorffContentBound_of_measurableSelection` with the measurable
selection axiom. This is the content-bound source the headline now uses, replacing the discrete
Case-B route `Engine.kakeya_hausdorffContentBound`. -/
theorem kakeya_hausdorffContentBound_sel
    {S : Set Plane} (h : IsKakeya S) {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2) :
    HausdorffContentBound S d := by
  apply kakeya_hausdorffContentBound_of_measurableSelection hd0 hd2
  intro C hC hcov
  obtain ⟨a, ha, hcovpt⟩ := kakeya_measurable_selection h C hC hcov
  refine ⟨a, ha, Filter.Eventually.of_forall (fun θ hθIcc => ?_)⟩
  calc (1 : ℝ≥0∞) = volume (Set.Icc (0 : ℝ) 1) := by
          rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
    _ ≤ volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a θ + t • dir θ ∈ ⋃ n, C n} :=
          measure_mono (fun t ht => ⟨ht, hcovpt θ hθIcc ht⟩)

/-- **The concrete crux (Davies 1971, measure form), via the measurable-selection route.** For a
Kakeya set `S ⊆ ℝ²`, every `d`-dimensional Hausdorff measure with `d < 2` is positive. Free
`ℝ≥0∞`-density wrapper around `kakeya_hausdorffContentBound_sel`; the `d = 0` endpoint comes from
monotonicity of `μH` in `d` against the `d = 1` content bound. -/
theorem hausdorffMeasure_pos_of_isKakeya
    (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    ∀ d : ℝ≥0, (d : ℝ≥0∞) < 2 → μH[(d : ℝ)] S ≠ 0 := by
  have key : ∀ e : ℝ, 0 < e → e < 2 → μH[e] S ≠ 0 := fun e he0 he2 =>
    hausdorffMeasure_ne_zero_of_contentBound he0 (kakeya_hausdorffContentBound_sel h he0 he2)
  intro d hd
  rcases eq_or_lt_of_le (zero_le d) with hd0 | hd0
  · have hd0R : (d : ℝ) = 0 := by exact_mod_cast hd0.symm
    have hmono : μH[(1 : ℝ)] S ≤ μH[(d : ℝ)] S := by
      rw [hd0R]; exact Measure.hausdorffMeasure_mono (by norm_num) S
    exact fun hz => key 1 one_pos (by norm_num) (le_antisymm (hz ▸ hmono) (zero_le _))
  · have hd2R : (d : ℝ) < 2 := by exact_mod_cast hd
    exact key d (by exact_mod_cast hd0) hd2R

/-- **Davies 1971.** A Kakeya set in `ℝ²` has Hausdorff dimension at least `2` — the genuine content
of the planar Kakeya conjecture (the upper bound is free). Frostman's lemma lifts each `μH[d] S ≠ 0`
(`d < 2`) to `↑d ≤ dimH S`, and the supremum over `d < 2` reaches `2`. The headline now routes through
the clean measurable-selection axiom `kakeya_measurable_selection`. -/
theorem two_le_dimH (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    2 ≤ dimH S := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  exact le_dimH_of_hausdorffMeasure_ne_zero (hausdorffMeasure_pos_of_isKakeya S h r hr)

end LeanFormalizations.Kakeya2D

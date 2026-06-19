/-
# Capacitability: "analytic sets are universally (`NullMeasurable`) measurable"

This is the sole remaining hole of the `jvn` / von Neumann measurable-selection route
(`VonNeumannSelection.lean`): brick A,

  `analyticSet_nullMeasurableSet : AnalyticSet s → NullMeasurableSet s μ`

i.e. **Choquet's capacitability theorem** (analytic sets are universally measurable). mathlib has the
`AnalyticSet` API + Lusin separation (`AnalyticSet.measurableSet_of_compl`) but **no** capacity /
Souslin-operation machinery, so this is a from-scratch DST build.

`lake env lean wip/GeometricMeasureTheory/Capacitability.lean` kernel-checks it.

## What is PROVEN here (no `sorry`) — the whole reduction is now machine-checked
The headline `analyticSet_nullMeasurableSet` (σ-finite `μ`) is reduced, with NO remaining hole except
the single finite-measure Choquet core, by two proven steps:

* `analyticSet_nullMeasurableSet_finite` (PROVEN from the core): for a **finite** measure, inner
  approximation by compacts ⟹ `NullMeasurable`. Sandwich `F = ⋃ Kₙ ⊆ s ⊆ G = toMeasurable μ s` with
  `μ F = μ s = μ G`, so `μ (s \ F) ≤ μ (G \ F) = 0` and `s =ᵐ[μ] F` (`ae_eq_set`).
* `analyticSet_nullMeasurableSet` (PROVEN from the finite case): **σ-finite reduction** via
  `spanningSets`. `s = ⋃ₙ (s ∩ spanningSets μ n)`; on each finite piece `μ.restrict (spanningSets μ n)`
  is finite, the finite case applies, and `nullMeasurableSet_restrict` transfers
  `NullMeasurableSet s (μ.restrict Dₙ)` to `NullMeasurableSet (s ∩ Dₙ) μ`; union closes it.

## The SOLE remaining hole: the finite Choquet core
`exists_isCompact_subset_outerMeasure_le` (finite `μ`): for analytic `s` and `ε > 0`, a compact
`K ⊆ s` with `μ s ≤ μ K + ε`. This is the genuine content of Choquet's theorem (inner regularity of
analytic sets by compacts). The Souslin scheme of cylinder images is set up below
(`cylImg`/`_zero`/`_decomp`/`analyticSet_cylImg`); the argument (Kechris 29.7 / Cohn, App.) is:

Let `f : (ℕ→ℕ) → X` continuous with `range f = s` (a nonempty analytic set;
`VonNeumann.analyticSet_exists_nat_nat_range`). The **Souslin scheme** is `A σ n := f '' cylinder σ n`.
For finite `μ` with outer measure `μ*`:
* `μ*` is monotone and continuous from below; at each scheme node a finite sub-union of children captures
  all but `ε·2⁻ⁿ` of the measure (the **regularisation**);
* the pruned finitely-branching subtree `C = {α | ∀ i, α i ≤ nᵢ}` is **compact** in `ℕ→ℕ` (a closed
  subset of `∏ᵢ Finset.range (nᵢ+1)`), so `K = f '' C` is compact, `K ⊆ s`, and the regularisation
  budget gives `μ* s ≤ μ K + ε` (the **measure-extraction core**);
* (already discharged here) inner + outer regularity ⇒ `NullMeasurable`.
A port of `RemyDegenne/brownian-motion`'s `Choquet/` stack (see `ON-LINE-REQUEST.md`) is the mechanical
alternative to this from-scratch proof; whichever lands first discharges the core.
-/
import Mathlib

open MeasureTheory Set Topology Function Filter
open scoped ENNReal

namespace LeanFormalizations.Capacitability

/-! ## The Souslin scheme of a continuous map out of Baire space -/

/-- The Souslin scheme of a continuous map out of Baire space: `cylImg f σ n = f '' cylinder σ n`, the
continuous image of the length-`n` cylinder based at `σ`. -/
def cylImg {X : Type*} (f : (ℕ → ℕ) → X) (σ : ℕ → ℕ) (n : ℕ) : Set X :=
  f '' PiNat.cylinder (E := fun _ => ℕ) σ n

/-- The root of the scheme is the whole range (`cylinder · 0 = univ`). -/
theorem cylImg_zero {X : Type*} (f : (ℕ → ℕ) → X) (σ : ℕ → ℕ) :
    cylImg f σ 0 = range f := by
  rw [cylImg, PiNat.cylinder_zero, image_univ]

/-- **Regularity of the scheme:** every node is the union of its (countably many) children, obtained by
fixing the `n`-th coordinate. From `PiNat.iUnion_cylinder_update`. -/
theorem cylImg_decomp {X : Type*} (f : (ℕ → ℕ) → X) (σ : ℕ → ℕ) (n : ℕ) :
    cylImg f σ n = ⋃ k, cylImg f (update σ n k) (n + 1) := by
  rw [cylImg, ← PiNat.iUnion_cylinder_update σ n, image_iUnion]
  rfl

/-- Each scheme node is analytic (continuous image of an open cylinder). -/
theorem analyticSet_cylImg {X : Type*} [TopologicalSpace X] {f : (ℕ → ℕ) → X} (hf : Continuous f)
    (σ : ℕ → ℕ) (n : ℕ) : AnalyticSet (cylImg f σ n) :=
  (PiNat.isOpen_cylinder (E := fun _ => ℕ) σ n).analyticSet_image hf

/-! ## Brick A, decomposed: the whole reduction is proven, the sole hole is the finite Choquet core -/

/-- **The finite Choquet core (THE crux; the sole remaining `sorry` of the `jvn` route).** For a
**finite** measure `μ`, every analytic set is inner-approximated by compacts: for `ε > 0` there is a
compact `K ⊆ s` with `μ s ≤ μ K + ε` (`μ s` = outer measure). This is the genuine content of Choquet's
capacitability theorem; see the file header for the Souslin-scheme argument and the port alternative. -/
theorem exists_isCompact_subset_outerMeasure_le
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (hs : AnalyticSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ K ⊆ s ∧ μ s ≤ μ K + ε := by
  sorry

/-- **Finite-measure capacitability (PROVEN from the core).** For a finite measure, every analytic set
is `μ`-`NullMeasurable`. Build `F = ⋃ₙ Kₙ ⊆ s` from compacts `Kₙ` with `μ s ≤ μ Kₙ + n⁻¹`; then
`μ F = μ s`, and with `G = toMeasurable μ s ⊇ s` (`μ G = μ s`) the sandwich gives `μ (s \ F) = 0`, i.e.
`s =ᵐ[μ] F`. -/
theorem analyticSet_nullMeasurableSet_finite
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (hs : AnalyticSet s) :
    NullMeasurableSet s μ := by
  -- compact inner approximations `Kₙ ⊆ s` with `μ s ≤ μ Kₙ + n⁻¹`
  have hK : ∀ n : ℕ, ∃ K, IsCompact K ∧ K ⊆ s ∧ μ s ≤ μ K + (↑n)⁻¹ := fun n =>
    exists_isCompact_subset_outerMeasure_le μ hs
      (ε := (↑n)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n))
  choose K hKc hKs hKμ using hK
  have hFmeas : MeasurableSet (⋃ i, K i) := MeasurableSet.iUnion fun i => (hKc i).measurableSet
  have hFsub : (⋃ i, K i) ⊆ s := iUnion_subset hKs
  -- `μ s ≤ μ (⋃ i, K i)`
  have hμF_ge : μ s ≤ μ (⋃ i, K i) := by
    refine ENNReal.le_of_forall_pos_le_add fun r hr _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.mpr hr.ne')
    calc μ s ≤ μ (K n) + (↑n)⁻¹ := hKμ n
      _ ≤ μ (⋃ i, K i) + (↑n)⁻¹ := add_le_add (measure_mono (subset_iUnion K n)) le_rfl
      _ ≤ μ (⋃ i, K i) + ↑r := add_le_add le_rfl hn.le
  have hμF : μ (⋃ i, K i) = μ s := le_antisymm (measure_mono hFsub) hμF_ge
  -- outer measurable hull `G = toMeasurable μ s ⊇ s` with `μ G = μ s`
  have hsG : s ⊆ toMeasurable μ s := subset_toMeasurable μ s
  have hμG : μ (toMeasurable μ s) = μ s := measure_toMeasurable s
  have hFG : (⋃ i, K i) ⊆ toMeasurable μ s := hFsub.trans hsG
  have hμFlt : μ (⋃ i, K i) ≠ ∞ := by rw [hμF]; exact (measure_lt_top μ s).ne
  -- `μ (s \ F) = 0` via the sandwich `s \ F ⊆ G \ F`, `μ (G \ F) = 0`
  have hdiff : μ (toMeasurable μ s \ ⋃ i, K i) = 0 := by
    rw [measure_diff hFG hFmeas.nullMeasurableSet hμFlt, hμG, hμF, tsub_self]
  have hsF0 : μ (s \ ⋃ i, K i) = 0 := measure_mono_null (diff_subset_diff_left hsG) hdiff
  have hFs0 : μ ((⋃ i, K i) \ s) = 0 := by rw [diff_eq_empty.mpr hFsub]; exact measure_empty
  exact hFmeas.nullMeasurableSet.congr (ae_eq_set.mpr ⟨hsF0, hFs0⟩).symm

/-- **Brick A — capacitability (PROVEN from the finite case via the σ-finite reduction).** For a
σ-finite measure `μ` on a Polish space, every analytic set is `μ`-`NullMeasurable`. The only use here is
`μ = volume` on `ℝ` (σ-finite). Reduction: `s = ⋃ₙ (s ∩ spanningSets μ n)`; on each finite piece the
finite case applies, transferred through `nullMeasurableSet_restrict`; the union is `NullMeasurable`. -/
theorem analyticSet_nullMeasurableSet
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : AnalyticSet s) (μ : Measure X) [SigmaFinite μ] : NullMeasurableSet s μ := by
  have hcover : s = ⋃ n, s ∩ spanningSets μ n := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  rw [hcover]
  refine NullMeasurableSet.iUnion fun n => ?_
  have hDmeas : MeasurableSet (spanningSets μ n) := measurableSet_spanningSets μ n
  have hDfin : μ (spanningSets μ n) ≠ ∞ := (measure_spanningSets_lt_top μ n).ne
  haveI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) := isFiniteMeasure_restrict.mpr hDfin
  have hnm : NullMeasurableSet s (μ.restrict (spanningSets μ n)) :=
    analyticSet_nullMeasurableSet_finite (μ.restrict (spanningSets μ n)) hs
  exact (nullMeasurableSet_restrict hDmeas.nullMeasurableSet).mp hnm

end LeanFormalizations.Capacitability

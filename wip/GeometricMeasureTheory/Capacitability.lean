/-
# Capacitability scaffolding: toward "analytic sets are universally measurable"

This is the sole remaining hole of the `jvn` / von Neumann measurable-selection route
(`VonNeumannSelection.lean`): brick A,

  `analyticSet_nullMeasurableSet : AnalyticSet s → NullMeasurableSet s μ`

i.e. **Choquet's capacitability theorem** (analytic sets are universally measurable). mathlib has the
`AnalyticSet` API + Lusin separation but no capacity/Souslin-operation machinery, so this is a
from-scratch DST build. This file sets up the **Souslin scheme of cylinder images** and proves the
reachable structural lemmas; the hard measure-extraction core (Choquet's argument) is the scoped `sorry`.

`lake env lean wip/GeometricMeasureTheory/Capacitability.lean` kernel-checks it.

## Proof architecture (Kechris 29.7 / Cohn, App.)
Let `f : (ℕ → ℕ) → X` be continuous with `range f = s` (a nonempty analytic set; `VonNeumann`'s
`analyticSet_exists_nat_nat_range`). The **Souslin scheme** is `A σ n := f '' cylinder σ n` (continuous
images of Baire cylinders, all analytic). It is a regular scheme:
* `cylImg_zero` : `A σ 0 = range f = s`;
* `cylImg_decomp` : `A σ n = ⋃ k, A (update σ n k) (n+1)` (each node is the union of its children);
* `analyticSet_cylImg` : each `A σ n` is analytic.

For a finite measure `μ` with outer measure `μ* = μ.toOuterMeasure`:
* (capacity) `μ*` is monotone and continuous from below — `measure_iUnion`-type continuity gives, at each
  node, a finite sub-union of children capturing all but `ε·2⁻ⁿ` of the measure (the **regularisation**);
* (Choquet) the resulting finitely-branching subtree's branch-closure intersection is a compact `K ⊆ s`
  with `μ*(s) ≤ μ(K) + ε` — this is the **measure-extraction core** (the scoped `sorry`), the genuine
  content needing compactness of the pruned subtree in `(ℕ → ℕ)` + continuity of `f`;
* inner regularity (`μ(K) ≤ μ*(s)`, `K ⊆ s`) + outer regularity ⇒ `s` is `μ`-`NullMeasurable`.
σ-finite / general `μ` reduces to the finite case. Only `μ = volume` on `ℝ` is actually needed.
-/
import Mathlib

open MeasureTheory Set Topology Function
open scoped ENNReal

namespace LeanFormalizations.Capacitability

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

/-- **Brick A — capacitability (the sole remaining `jvn`-route hole).** In a Polish space every analytic
set is `μ`-`NullMeasurable` for any measure. The scheme above (`cylImg_zero`/`_decomp`/`analyticSet_`)
is set up; the `sorry` is exactly the Choquet measure-extraction core (see the file header). Discharging
this makes `VonNeumann.jvn_of_measurableSelection` unconditional, hence
`Kakeya2D.Selection.kakeya_aeMeasurable_selection_of_jvn` an axiom-clean independent 2nd route to the
planar Kakeya headline. -/
theorem analyticSet_nullMeasurableSet
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : AnalyticSet s) (μ : Measure X) : NullMeasurableSet s μ := by
  sorry

end LeanFormalizations.Capacitability

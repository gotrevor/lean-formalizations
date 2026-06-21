/-
# Choquet capacitability core (finite measure, range of a continuous Baire map)

GOAL: replace the `sorry` with a real proof.

This is the inner-regularity-by-compacts core of Choquet's capacitability theorem:
for a FINITE Borel measure `μ` on a Polish (complete, second-countable metric) space `X`,
and a CONTINUOUS map `f : (ℕ → ℕ) → X` out of Baire space, the analytic set `range f`
is approximated from inside by a compact set up to `ε` in measure.

KEY MATHLIB TOOLS (verified present in current mathlib):
* `Monotone.measure_iUnion : Monotone s → μ (⋃ i, s i) = ⨆ i, μ (s i)`
  — continuity from below for ARBITRARY (non-measurable) monotone sets (regular outer measure).
* `Directed.measure_iInter` / continuity from above: for a decreasing sequence of MEASURABLE
  sets of finite measure, `μ (⋂ i, s i) = ⨅ i, μ (s i)`.
* `isCompact_univ_pi`, `Set.Finite.isCompact`, `Set.finite_Iic` — `{α | ∀ i, α i ≤ b i}` is compact.
* `IsCompact.image` (f continuous) ⟹ `f '' C` compact; compact ⟹ closed (T2) ⟹ measurable.

SUGGESTED ARGUMENT (Kechris, Classical DST, Thm 29.7):
The naive "cumulative bounds" regularisation (pick `b j` so the measure lost at level `j`
is `< ε·2^⁻ʲ`, set `C = {α | ∀ i, α i ≤ b i}` compact, `K = f '' C`) has a genuine GAP:
`⋂ⱼ closure (f '' Uⱼ) ⊆ f '' C` is FALSE without diameter control. The correct proof builds a
**Lusin scheme** of closed sets `F_w` (indexed by finite sequences `w`) with `diam (F_w) → 0`
along branches and `F_w ⊇ closure (⋃ₖ F_{w⌢k})`, representing `range f`, then runs the
regularisation on that scheme so the limit intersection is exactly the compact `K`. Producing such
a scheme from a continuous `f` (using a complete metric on `X` and the standard metric on `ℕ→ℕ`)
is the substantive step. If you cannot close it fully, make maximal honest progress and leave the
narrowest possible `sorry`.
-/
import Mathlib

open MeasureTheory Set Topology Filter
open scoped ENNReal

theorem choquet_core_range
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : (ℕ → ℕ) → X} (hf : Continuous f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ K ⊆ range f ∧ μ (range f) ≤ μ K + ε := by
  sorry

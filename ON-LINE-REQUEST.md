# ON-LINE-REQUEST — needs open-web / literature access (box has no general internet)

## 2026-06-19 — existing Lean/mathlib formalization of measurable selection / capacitability?

**Context.** Discharging the abstract `jvn` hypothesis of
`Kakeya2D/Selection.kakeya_aeMeasurable_selection_of_jvn` (the independent 2nd route to the planar
Kakeya headline) reduces — see `wip/GeometricMeasureTheory/VonNeumannSelection.lean` and
`PENDING_WORK.md` (top) — to ONE isolated lemma `exists_aemeasurable_section_of_continuous_range`,
whose proof needs either:
  - **(A)** *Capacitability*: analytic sets in a Polish space are universally / `NullMeasurable`
    measurable (Choquet's theorem via the Souslin operation); or
  - **(B)** the **Kuratowski–Ryll-Nardzewski** measurable-selection theorem for closed-valued
    measurable multifunctions; or
  - the **Jankov–von Neumann uniformization** theorem directly.

mathlib (v4.29.1, this repo's pin) has `MeasureTheory.AnalyticSet` + its closure/projection API and the
Lusin separation theorem (`AnalyticSet.measurablySeparable`, `measurableSet_of_compl`) in
`MeasureTheory/Constructions/Polish/Basic.lean`, the Baire-space machinery in
`Topology/MetricSpace/PiNat.lean` (`cylinder`, `longestPrefix`, `inter_cylinder_longestPrefix_nonempty`,
`exists_lipschitz_retraction_of_isClosed`), but NONE of (A)/(B)/Jankov–von Neumann.

**What I need from the web:**
1. Does any **public Lean 4 / mathlib branch, PR, or external library** already formalize ANY of:
   capacitability / universal measurability of analytic sets; Kuratowski–Ryll-Nardzewski; Jankov–von
   Neumann or any measurable-selection theorem? (Check: open & merged mathlib PRs, the mathlib
   `Mathlib/MeasureTheory/Constructions/Polish/` and any `DescriptiveSetTheory` additions post-v4.29.1,
   Zulip threads, the `carleson`/`marginis`/other DST-heavy projects.) If yes: exact location + the
   theorem signature, so I can port or bump.
2. A clean **textbook proof outline** of "analytic sets are universally measurable" optimized for
   formalization — ideally the shortest route from mathlib's *current* `AnalyticSet` API (Souslin
   scheme representation? inner-regularity + Lusin? capacity from an outer measure?). Kechris *Classical
   DST* 21.10 / 29.7 and Cohn *Measure Theory* App. are the standard refs; which decomposition has the
   fewest missing prerequisites in mathlib?
3. Whether the **von Neumann selection** is easier to get for **σ-compact codomain** (here `Y = ℝ²`):
   any selection theorem that exploits local compactness / σ-compactness to avoid full capacitability.

**Why it unblocks:** any one of these collapses the single remaining `sorry` in the `jvn` route into a
port/citation, making `kakeya_aeMeasurable_selection` unconditional (an independent, axiom-clean second
proof of the planar Kakeya headline). Not gating the existing headline (already axiom-clean via the
elementary open-cover route) — it is the next genuine mathematical target.

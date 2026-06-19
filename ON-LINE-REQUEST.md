# ON-LINE-REQUEST — vendor brownian-motion's Choquet stack (capacitability)

**Date**: 2026-06-19 (later lap) · **Branch**: `kakeya-davies`

## Context (already answered, acting on it)
The `ON-LINE-FINDINGS-2026-06-19-measurable-selection-followup.md` (now harvested) established:
the von Neumann / Jankov–von Neumann measurable-section theorem and Choquet capacitability are
**already formalized in Lean** in `RemyDegenne/brownian-motion`, files
`BrownianMotion/Choquet/{Capacity,AnalyticSet,Debut,MeasurableSection}.lean` (pinned to mathlib
`v4.30.0`). The recommended path is a **source-port** of that `Choquet/` stack to discharge our sole
remaining `jvn`-route hole, `Capacitability.analyticSet_nullMeasurableSet` (= "analytic sets are
universally / `NullMeasurable`"). The network-isolated box **cannot `require` or fetch** the repo, so
the source must be **vendored (copied) into this repo** by a networked lap.

## The ask (concrete)
1. **Vendor the 4–6 `Choquet/` source files** from `RemyDegenne/brownian-motion` into this repo under
   `wip/GeometricMeasureTheory/Choquet/` (preserve the upstream file structure & a header noting the
   upstream commit SHA + that it is pinned to mathlib v4.30.0). The key files (per the findings doc):
   `Capacity.lean`, `AnalyticSet.lean`, `Debut.lean`, `MeasurableSection.lean` (+ any small support file
   they import from the same `Choquet/` dir). Include the exact upstream **commit SHA** you copied from.
2. **Note the upstream statement** of `MeasurableSet.exists_measurable_section_right_nnreal`
   (`MeasurableSection.lean:478` at time of findings) and of the capacitability theorem in `Capacity.lean`
   / `AnalyticSet.lean` (exact declaration name + signature), so the offline lap can write the bridge
   lemma to our mathlib-`AnalyticSet` statement without guessing names.
3. **(Optional, helpful)** Note brownian-motion's *analytic-set* representation (`IsPavingAnalytic`?
   paving / Souslin-operation based) vs mathlib's `AnalyticSet` (continuous image of `ℕ→ℕ`), and whether
   upstream already has a bridge between the two — that bridge is the one piece a port still needs.

## Why this unblocks
Our `jvn` route (`wip/.../VonNeumannSelection.lean`) is **proven except** the single `sorry`
`analyticSet_nullMeasurableSet`. With the Choquet source vendored, an offline lap can (a) fix imports
for our toolchain (we are on **v4.29.1**; upstream targets v4.30.0 — a ≤2-minor patch), (b) write the
`AnalyticSet ⟷ IsPavingAnalytic` bridge, and (c) discharge the `sorry` as a corollary — making the
independent 2nd route to planar Kakeya axiom-clean. This is the mechanical alternative to the
from-scratch Kechris-29.7 proof being attempted locally; whichever lands first wins.

(Meanwhile the offline lap is banging on the from-scratch capacitability proof — do NOT treat this as
blocking; it is the parallel mechanical lane.)

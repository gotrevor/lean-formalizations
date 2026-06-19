# ON-LINE-FINDINGS 2026-06-19 — RESOLUTION: import brownian-motion, do NOT vendor

**Answers** the "vendor brownian-motion's Choquet stack" `ON-LINE-REQUEST.md`. **Decision (Trevor,
host): do NOT copy any source.** Brownian-motion will be consumed as a **direct `.lake` dependency**
(an external `require`, not vendored files) once it's built at a shared mathlib pin — see the
`lean-universe` / `lake-base` plan. Direct reference beats copy-with-attribution: no license header
bookkeeping, no drift, the proof stays upstream's. **This supersedes the vendor ask and the
from-scratch capacitability lane.** The treadmill is paused while the import infra is set up.

## Why vendoring was the wrong path (investigated this session, mirror `fbe9ec1`, 2026-06-14)
- **`public import` syntax**: every BM `Choquet/*.lean` uses Lean's module-system `public import`.
  davies' Lean (v4.29.1) would need every line rewritten to plain `import` — pure friction.
- **The section theorem drags in the probability stack**: `Debut.lean` imports
  `BrownianMotion.StochasticIntegral.Predictable` + `Mathlib.Probability.Martingale.BorelCantelli`,
  and `MeasurableSection.lean` imports `Debut`. That's the mathlib-*evolution* wall (`lean-universe.md`:
  BM needs v4.31, can't backport to v4.29.1). Vendoring the section theorem ⟹ vendoring half of BM.

## The good news for the import path (the bridge is small + well-targeted)
Our **actual** isolated hole is `Capacitability.analyticSet_nullMeasurableSet` (analytic ⟹
`NullMeasurable`) — which is the **capacitability core, NOT the section theorem**. That core is just 4
files (`Capacity, AnalyticSet, CompactSystem, CountableClosed`) and is **self-contained on mathlib
measure-theory/topology** — it does NOT touch `StochasticIntegral`/`Debut`/the probability stack. So
after `require`-ing BM the only work left is a short bridge:

- **Target decl**: `BrownianMotion.Choquet.IsPavingAnalyticFor.isCapacitable` (`Capacity.lean:346`);
  supporting `IsCapacitable` (def, `Capacity.lean:127`),
  `isCapacitable_mem_countableInfClosure_countableSupClosure` (`:269`), `IsCapacitable.fst` (`:335`).
- **The bridge to write**: BM's analytic notion is `IsPavingAnalytic` / `IsMeasurableAnalytic`
  (Souslin-operation / paving based) vs mathlib's `AnalyticSet` (continuous image of `ℕ→ℕ`). Prove
  `mathlib.AnalyticSet s → BM.IsMeasurableAnalytic s` (or directly `IsPavingAnalytic`), then apply
  `isCapacitable` + the capacity→`NullMeasurableSet` step. This is the single remaining piece.
- **The full section theorem** (if ever needed, not for this hole):
  `MeasurableSet.exists_measurable_section_left_nnreal` (`MeasurableSection.lean:472`),
  `IsMeasurableAnalytic.exists_measurable_section_right_nnreal` (`:466`) — these DO need the heavier
  Debut/predictable layer, so they only come for free once BM is fully imported at v4.31.

## The one constraint on "import via .lake"
Lake resolves **one mathlib commit per dependency graph**, so davies and BM must pin the **same**
mathlib. BM is built at **v4.30.0** (`lean-toolchain` + manifest `inputRev v4.30.0`); the
`lean-universe` base is **v4.31.0**. So davies bumps to the universe pin (v4.31) and `require`s the
pre-built BM from the shared store. (Note: the 4-file capacitability core's mathlib imports all
*exist* as far back as v4.29.1 — verified — but BM-as-a-whole needs v4.31, and we're importing the
whole package, so v4.31 is the shared pin.)

**Upstream**: `RemyDegenne/brownian-motion`, commit `fbe9ec1ba6479e024fa0ade762b644491ee6e2d9`
("feat: Doob Meyer Decomposition (#445)", 2026-06-14), mathlib v4.30.0. MIT-licensed.

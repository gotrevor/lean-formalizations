# ON-LINE-FINDINGS 2026-06-19 (follow-up) — measurable selection, refined ask

**Answers** the re-materialized `ON-LINE-REQUEST.md` (the `jvn` hole now isolated to
`exists_aemeasurable_section_of_continuous_range` in `wip/.../VonNeumannSelection.lean`; asks 1–3).

**This is a SUPPLEMENT.** The bulk was already answered today — read
`archive/findings/ON-LINE-FINDINGS-2026-06-19-measurable-selection.md` first. That file still stands:
the theorem you need is the **von Neumann / Jankov–von Neumann measurable section theorem**, it is
**already in Lean** in `RemyDegenne/brownian-motion` `Choquet/MeasurableSection.lean`
(`MeasurableSet.exists_measurable_section_right_nnreal`, line 478), mathlib lacks the capacitability
layer, the `Plane→ℝ≥0` reduction is a non-issue, and the highest-leverage move is to **restate the
axiom in a.e. form**. This follow-up only adds the genuinely-new deltas the lap's refined ask raised.

**Sources read this follow-up session:** corrected `reservoir-grep` over the full 705-repo Reservoir
mirror; `gh api` on the **mathlib4 `v4.31.0` tag** tree + `gh search prs`; `zulip-ro` (the "Is there
code for X?" corpus); `brownian-motion` `lean-toolchain` + `lake-manifest.json`; WebSearch on the
Arsenin–Kunugui theorem. Declaration names / paths / pins below were read directly, not recalled.

---

## ⭐ New bottom line

1. **mathlib 4.31.0 does NOT close the gap — upgrading buys nothing for this lemma.** (You're moving
   4.29.1 → 4.31.0 today, so this was worth checking.) At the **`v4.31.0` tag**,
   `Mathlib/MeasureTheory/Constructions/Polish/` = `Basic.lean, EmbeddingReal.lean,
   StronglyMeasurable.lean` — **identical to 4.29.1**. No `Capacity`/`MeasurableSection`/selection
   file, no `DescriptiveSetTheory` folder under `Constructions/`, and **zero merged PRs** for
   capacity / Kuratowski–Ryll-Nardzewski / measurable selection. The `AnalyticSet` API (Borel⟹analytic,
   projection-analytic, Lusin separation, Suslin) is present but still **stops exactly at the
   capacitability wall** (prior §2 holds verbatim at 4.31.0). Confidence **90%**.

2. **Full-ecosystem sweep confirms brownian-motion is the SOLE carrier** (corrected for the prior
   findings' regex bug — `\|` is a literal in `rg`, not alternation). Across all 705 Reservoir repos,
   the only files carrying the selection/Choquet decls are
   `RemyDegenne/brownian-motion/BrownianMotion/Choquet/{Capacity,AnalyticSet,Debut,MeasurableSection}.lean`.
   The two named-project leads are **dead ends**:
   - **`fpvandoorn/carleson`** — single hit is an English "we could have tried harder to *uniformize*
     the cases" comment in `TwoSidedCarleson/WeakCalderonZygmund.lean`. No DST. ❌
   - **`cameronfreer/exchangeability`** — hit is `deFinetti_RyllNardzewski_equivalence`, the **de
     Finetti–Ryll-Nardzewski exchangeability theorem** (a *name collision* — Ryll-Nardzewski has two
     famous theorems; this is NOT the KRN measurable-selection theorem). Irrelevant. ❌
   - **`marginis`** — not in the Reservoir mirror, could not audit; niche logic-paper formalizations,
     low prior. Treat as "not located," not "proven absent."
   - **Zulip "Is there code for X?"** — *zero* relevant discussion; the term **"capacitability" is
     absent from the entire corpus**. Nobody has asked for or announced this in Lean.

3. **Porting drift just shrank.** `brownian-motion` pins **mathlib `v4.30.0`** (`lean-toolchain` +
   manifest `inputRev v4.30.0`). Once davies is on **4.31.0**, the skew is **one minor version**
   (v4.30 → v4.31), not the multi-version gap the prior §6A flagged. The Choquet stack is the most
   stable layer of mathlib (Polish/analytic API barely moves), so a source-port should be a
   **mostly-mechanical** 4.30→4.31 patch. This materially improves the case for path (A). Confidence **70%**.

4. **Ask 3 — the σ-compact shortcut does NOT exist.** (See §A below.) σ-compactness of the *codomain*
   `ℝ²` buys nothing; the classical σ-compact theorem (Arsenin–Kunugui) needs σ-compact **sections**
   you don't have, and its proof routes through Jankov–von Neumann anyway. Capacitability /
   measurable-section remains the genuinely-needed tool. Confidence **80%**.

---

## §A — Ask 3: "is σ-compact codomain a lighter route?" → No, and here's exactly why

The classical theorem the ask is reaching for is the **Arsenin–Kunugui theorem**: *a Borel set in
`X × Y` whose sections are **Kσ (σ-compact)** has a Borel uniformization (and Borel projection).* Two
reasons it is **not** a shortcut for you:

- **It needs Kσ *sections*, not a σ-compact *codomain*.** Every selection theorem in play (JvN, KRN,
  Arsenin–Kunugui) already assumes a Polish / standard-Borel codomain — `ℝ²` being σ-compact is
  *already used up* and grants no lighter variant. Your sections are
  `G_θ = {p : coveredLength_θ(p) ≥ 1}`, a **Borel superlevel set of a measurable, non-semicontinuous
  function** (prior §5). That is not Kσ in general (not closed, not a countable union of compacts you
  can exhibit), so Arsenin–Kunugui's hypothesis fails just as KRN's closed-valued hypothesis did.
- **Even where it applies, it isn't lighter.** The literature's proofs of Arsenin–Kunugui (and its
  converse, Holický–Zelený, *Fund. Math.* 165) go *through* a Hurewicz-type dichotomy **and the
  Jankov–von Neumann selection theorem** — i.e. they sit on top of the same capacitability-grade
  machinery, not below it.

**Conclusion:** there is no local-compactness escape hatch. The only genuine way to **avoid DST
entirely** is still the **maximal-function / open-cover route** flagged in prior §5 (for an *open*
cover, `p ↦ coveredLength_θ(p)` is lower-semicontinuous ⟹ `sup_p` over a countable dense set is
measurable, no selection at all) — but that is a re-architecture to open covers, not a drop-in.

## §B — Ask 2: shortest formalization route for "analytic ⟹ universally measurable"

Do **not** try to bolt capacitability onto **mathlib's** `AnalyticSet` (defined as a continuous image
of Baire space `ℕ→ℕ`). Choquet capacitability is naturally stated over the **Souslin-operation /
paving** representation, which is exactly `brownian-motion`'s `IsPavingAnalytic` (`Choquet/AnalyticSet.lean`).
The cheapest path is to **port the self-contained `Choquet/` stack** and bridge to mathlib *only* at
the boundary lemmas mathlib already provides (`MeasurableSet.analyticSet`, `MeasurableSet.analyticSet_image`
= projection-is-analytic — your `4fc11b2` work). The prerequisite chain (prior §2) is: `Capacity` →
`CompactSystem`/`CountableClosed` → `AnalyticSet` (capacitability theorem) → `Debut` →
`MeasurableSection`. Textbook anchor: **Kechris, *Classical DST* §29 (capacitability of analytic sets,
Choquet's theorem)**; Cohn, *Measure Theory*, appendix. (Theorem numbers cited from memory — verify
against the text before quoting in a docstring.)

---

## Recommendation (unchanged in shape, sharper on timing)

- **Now (interim, cheap):** adopt the prior §4 **a.e. restatement** of the axiom so it is *verbatim*
  the named measurable-section theorem, with a docstring pointer to `RemyDegenne/brownian-motion`
  `MeasurableSection.lean:478`. This is the `formal_proof using lean4 at "<url>"` convention and a real
  faithfulness win even before any port.
- **Long pole (now more attractive):** **source-port** the `brownian-motion` `Choquet/` stack and
  discharge the axiom as a corollary. With davies on **4.31.0** and brownian-motion on **4.30.0**, the
  port is a one-minor-version patch, not a rewrite. (Network-isolated box can't `require` it — must be
  a source copy; a host/online lap can vendor the 6 files, then offline laps fix imports.)
- **Do NOT** wait on mathlib or chase Arsenin–Kunugui / Davies-duality / a σ-compact shortcut — none
  is lighter than what already exists in brownian-motion.

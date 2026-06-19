# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`)

**Thin pointer.** Durable overview = `STATUS.md`. Attack plan = `PENDING_WORK.md` §A0‴ + crux analysis
= `Kakeya2D/CASE_B_ANALYSIS.md`. Frozen plan = `Kakeya2D/PLAN.md`. **Newest dated baton =
`HANDOFF-2026-06-19-1530.md` — read that to resume.**

Unbounded expedition to prove `davies_kakeya_2d : KakeyaSetConjectureDim 2` (planar Kakeya, Davies
1971). The whole job is the lower bound `two_le_dimH`. Lane: only `Kakeya2D/`.

## State (one line)
`lake build` green (8298 jobs). The whole lower bound is machine-checked **down to ONE cited axiom**
`Engine.kakeya_subresolution_content` (NO `sorry`). This lap pinned the crux to **measurable
base-point selection** and built the full measure-theoretic spine of the alternative continuum route
(`Kakeya2D/MeasurableRoute.lean`, axiom-clean) — only the wiring assembly + the selection axiom remain.
`#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound, kakeya_subresolution_content]`.
The entire dominant-scale orchestration (the historic blocker) is now PROVEN — the shifted, faithful
Case A assembly. The lone axiom is the strictly-narrower **Case B** residual (cover dominated by pieces
finer than the net resolution = the Hausdorff-vs-box gap). Remaining = crack Case B (reference-gated;
the fixed-net multi-scale L² sum provably diverges for `d>1` — see the dated baton).

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- Commit every green build; never push; never fake green; disclosed `sorry`/`axiom` only; no smuggling.
- A separate dormant `sorry` lives in `Logic/FastGrowing/Basic.lean` — out of the Kakeya lane, leave it.

# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`)

**Thin pointer.** Durable overview = `STATUS.md`. Sharpened ask = `ON-LINE-REQUEST.md` §UPDATE 6.
Crux analysis = `Kakeya2D/CASE_B_ANALYSIS.md`. **Newest dated baton = `HANDOFF-2026-06-19-1115.md` —
read that to resume.** The headline now rests on ONE **Kakeya-agnostic** axiom `kakeya_borel_selection`
(textbook von Neumann / Jankov–von Neumann measurable selection); every Kakeya-specific fact is PROVEN
(`Kakeya2D/Selection.lean`). Next = discharge that selection (deep DST, multi-lap).

Unbounded expedition to prove `davies_kakeya_2d : KakeyaSetConjectureDim 2` (planar Kakeya, Davies
1971). The whole job is the lower bound `two_le_dimH`. Lane: only `Kakeya2D/`.

## State (one line)
`lake build` green (8300 jobs, HEAD `1f7dbfb`). The whole lower bound is machine-checked **down to ONE
Kakeya-agnostic axiom** `kakeya_borel_selection` (NO `sorry`):
`#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound, kakeya_borel_selection]`.
That axiom is the **textbook von Neumann / Jankov–von Neumann measurable selection** (a Borel set in
`ℝ × Plane` with non-empty sections over `[0,1]` has an a.e.-measurable selector) — zero Kakeya content.
Every Kakeya-specific fact is PROVEN + axiom-clean in `Kakeya2D/Selection.lean` (joint measurability of
the covered length ⟹ Borel graph; non-empty sections from `IsKakeya`; the reduction). The route is
`MeasurableRoute.lean` spine (a.e./measure form) → `Wiring.lean` lemmas A/B → `Selection.lean`. The old
Case-B residual `kakeya_subresolution_content` is now legacy/off-path (discrete route preserved in
`Engine.lean`). Remaining = discharge `kakeya_borel_selection` (deep DST: von Neumann selection from
mathlib's `AnalyticSet` API — multi-lap, reference-gated, see `ON-LINE-REQUEST.md` UPDATE 6).

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- Commit every green build; never push; never fake green; disclosed `sorry`/`axiom` only; no smuggling.
- A separate dormant `sorry` lives in `Logic/FastGrowing/Basic.lean` — out of the Kakeya lane, leave it.

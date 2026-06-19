# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`)

**Thin pointer.** Durable overview = `STATUS.md`. Attack plan = `PENDING_WORK.md` §A0′. Frozen plan =
`Kakeya2D/PLAN.md`. **Newest dated baton = `HANDOFF-2026-06-19-0945.md` — read that to resume.**

Unbounded expedition to prove `davies_kakeya_2d : KakeyaSetConjectureDim 2` (planar Kakeya, Davies
1971). The whole job is the lower bound `two_le_dimH`. Lane: only `Kakeya2D/`.

## State (one line)
`lake build` green (8297 jobs). The whole lower bound is machine-checked **down to ONE cited axiom**
`Engine.kakeya_dominant_scale_count` (NO `sorry`):
`#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound, kakeya_dominant_scale_count]`.
The axiom's hard combinatorial core (net-thinning shift average) + the base-angle Córdoba chain + the
geometric foundation are all PROVEN this lap (`NetThinning.lean`, R2). Remaining = wire the assembly
(Case A) + crack Case B (Hausdorff-vs-box gap) + restate the axiom to the shifted form (faithfulness).

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- Commit every green build; never push; never fake green; disclosed `sorry`/`axiom` only; no smuggling.
- A separate dormant `sorry` lives in `Logic/FastGrowing/Basic.lean` — out of the Kakeya lane, leave it.

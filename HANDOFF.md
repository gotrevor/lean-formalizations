# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`)

**Thin pointer.** Durable overview = `STATUS.md`. **Newest dated baton = `HANDOFF-2026-06-19-2130.md`
(lap-end checkpoint) — read that to resume; `HANDOFF-2026-06-19-2105.md` has the detailed anatomy.**
Open items / lesson = `PENDING_WORK.md` (top).

## State (one line)
`lake build` 🟢 green (8300 jobs, HEAD `02aa4e3`). **ALL headlines are axiom-clean**, including the
planar-Kakeya headline `davies_kakeya_2d : KakeyaSetConjectureDim 2` (Davies 1971):
`#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound]`. It proves the lower bound
via the *elementary open-cover selection* route (`Selection.kakeya_hausdorffContentBound_elementary`) —
no descriptive set theory, no measurable-selection axiom. Defs match `formal-conjectures` verbatim.

## This lap's headline event
The off-headline legacy axiom `kakeya_subresolution_content` (the discrete route's "Case-B residual",
cited by every prior lap as "true but deep") was found **UNSOUND** and **removed**; kernel-checked
refutation kept as `Engine.kakeya_subresolution_content_is_unsound`. So `Kakeya2D/` is now
axiom-declaration-free. Remaining holes = 1 disclosed, redundant, off-headline `sorry` (legacy discrete
Case-B branch, unclosable by the discrete approach) + 1 dormant out-of-lane `sorry` (FastGrowing).

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- Commit every green build; never push; never fake green; disclosed `sorry` only; **no smuggled/false axioms**.
- Do NOT re-introduce any abstract Case-B axiom (it is false — guard theorem present). Do NOT re-attack
  measurable selection (headline solved via the elementary route).
- The `Logic/FastGrowing/Basic.lean` `sorry` is out of the Kakeya lane — leave it.

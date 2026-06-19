# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`)

**Thin pointer.** Durable overview = `STATUS.md`. Attack plan = `PENDING_WORK.md` §A. Frozen plan =
`Kakeya2D/PLAN.md`. Newest dated baton = `HANDOFF-2026-06-19-*.md`. **Read `DIRECTION.md` first.**

Unbounded expedition to prove `davies_kakeya_2d : KakeyaSetConjectureDim 2` (planar Kakeya, Davies
1971). The whole job is the lower bound `two_le_dimH`. Lane: only
`src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/`.

## State — K1–K4 COMPLETE + K5 reduction/geometry COMPLETE, all axiom-clean. One Kakeya `sorry`.
`lake build` green (8295 jobs). The lone Kakeya `sorry` is now:
- `Engine.lean : kakeya_hausdorffContentBound` — for a planar Kakeya `S` and every `0<d<2`, the
  **Hausdorff content bound** `∃ r>0, c≠0, ∀ fine cover S⊆⋃tₙ, c ≤ ∑ ediam(tₙ)^d`. This is the
  multi-scale Córdoba estimate (an arbitrary cover ⟹ `∑ediam^d ≳ 1`).

`davies_kakeya_2d` `#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]` (single
`sorryAx`, pinned to that content bound). (A *separate, dormant* `sorry` lives in
`Logic/FastGrowing/Basic.lean` — out of the Kakeya lane, do not touch.)

## Done this lap (2026-06-19 review) — K5 switched to the measure-free cover route (`Cover.lean`)
Engine no longer reduces to "construct a Frostman measure" (which forces a weak-* limit mathlib
lacks). It reduces to the honest, mathlib-native **Hausdorff content bound**. New `Cover.lean`, all
`#print axioms`-clean:
- `hausdorffMeasure_ne_zero_of_content_bound` / `_diam_content` / `_contentBound` + the packaged
  `HausdorffContentBound` Prop — content bound ⟹ `μH[d]S≠0` via `hausdorffMeasure_apply`.
- `thickening_subset_iUnion_thickening` + `volume_thickening_le_tsum` — a cover of `S` thickens to a
  cover of `Sδ` (strict slack `δ<δ'` dissolves the closed-thickening `iInf` boundary issue), giving
  `vol(Sδ) ≤ ∑ vol((Uₙ)δ')`.
- `volume_thickening_le_of_ediam_le` — per-piece area `vol((U)δ') ≤ ofReal((ρ+δ')²)·vol(closedBall 0 1)`.
- `exists_index_ge_of_tsum_lt` — weighted pigeonhole `c≤∑aₙ`, `∑wₙ<c ⟹ ∃n, wₙ≤aₙ`.
- `CordobaL2.volume_thickening_tubes_ge` — K4 `L²` bound for an *explicit* tube family in any
  container `E` (drops `IsKakeya`); `volume_thickening_mul_ge` is its `E:=Sδ` corollary.
- `TubeFractional.volume_tube_ge_frac` — `ofReal(2δ‖v‖) ≤ vol(tube a v δ)`, the fractional
  (length-`‖v‖`) tube area bound (localized-Córdoba numerator).

## Next brick — the dyadic pigeonhole assembly (multi-lap; `PENDING_WORK.md` §A)
**All geometric/L² inputs are now built and axiom-clean.** Remaining = the bookkeeping + double
pigeonhole. Recommended entry = sub-brick (a): for a net direction `θ` with `ℓ_θ ⊆ ⋃Uₙ`, formalize
`∑ⱼ Lⱼ(θ) ≥ 1` and pigeonhole (`exists_index_ge_of_tsum_lt`) to a dominant scale + covered
sub-segment, needing the clean 1D brick `|ℓ_θ ∩ Uₙ| ≤ ediam Uₙ`. Then (b) direction pigeonhole and
(c) assemble step 4 via `volume_thickening_tubes_ge` + `volume_tube_ge_frac`. Online ref requested in
`ON-LINE-REQUEST.md` — not blocking.

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- `dimH_le_two`, `two_le_dimH`, K2–K4, and the whole K5 reduction/geometry are done + axiom-clean.
- Commit every green build; never push; never fake green; disclosed `sorry` only; no axiom-smuggling.

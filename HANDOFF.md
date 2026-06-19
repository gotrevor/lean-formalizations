# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`, 2026-06-19)

**Read `DIRECTION.md` first.** Unbounded expedition to prove `davies_kakeya_2d :
KakeyaSetConjectureDim 2` (planar Kakeya, Davies 1971). The whole job is the lower bound
`two_le_dimH`. Lane: only `src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/`.

## State — **K1 + K2 COMPLETE, axiom-clean.** One `sorry` left.
`lake build` green (8289 jobs). The ONLY open `sorry` in the Kakeya thread:
- `Engine.lean : hausdorffMeasure_pos_of_isKakeya` — the analytic crux `∀ d<2, μH[d] S ≠ 0`.
  Needs the K3→K4→K5 ladder below.

### Done (this lap — K1 + the whole K2 ladder)
- **K1 (`Engine.lean`).** `two_le_dimH` reduced (axiom-clean) to `hausdorffMeasure_pos_of_isKakeya`
  via Frostman (`le_dimH_of_hausdorffMeasure_ne_zero`) + `ENNReal.le_of_forall_nnreal_lt`.
- **K2 (`Tube.lean`, new, 100% sorry-free + axiom-clean).**
  `tube a v δ := cthickening δ (affineSegment ℝ a (a+v))`. Structural + thinness lemmas
  (`exists_core_witness`, `tube_transverse`, `tube_longitudinal`, `tube_subset_coordBox`).
  - `volume_tube_le` — single δ-tube area `≤ 6δ` (orthonormal `frame` + `volume_coordBox` via
    measure-preserving `ofLp∘frame.repr∘(·-a)` → `volume_pi_pi`; `perp`/`norm_perp`/`inner_perp`).
  - `volume_inter_tube_le` — **overlap `≤ 12δ²/(s+δ)`**, `s = |v₀w₁−v₁w₀| = |sin∠|` (lines-invariant;
    NOT `‖v-w‖`, which is false near-antipodal). `volume_two_slab` (parallelogram area `(2δ)²/|det|`
    via `addHaar_preimage_linearMap` + `det_toLpLin`/`det_fin_two`) + two-regime split.
  - `volume_tube_ge` — single δ-tube area `≥ 2δ` (K4 numerator prereq), via `frame_decomp` +
    `subBox_subset_tube` + `volume_frame_box` (general frame-box area). Area is now pinned `≍ δ`.

## Next brick — K3, the δ-discretization (feeds toward `hausdorffMeasure_pos_of_isKakeya`).
From `IsKakeya S`: for each unit direction `v`, `∃ a, affineSegment ℝ a (a+v) ⊆ S`, hence
`tube a v δ ⊆ Sδ` (= `cthickening δ S`) via `cthickening_mono`/`cthickening` of a subset.
Build the δ-separated direction net on the circle (compactness of `{v | ‖v‖=1}`) and a family of
`~δ⁻¹` tubes with pairwise separations `s ≈ kδ`, all inside `Sδ`. Then K4 (Córdoba `L²`):
`vol(Sδ) ≥ (∑∫1_{tube})² / ∑∑ overlap`, numerator `≳ 1` (each tube area `≈ δ`, `δ⁻¹` of them),
denominator `≲ ∑ₖ δ·δ²/(kδ+δ) ≈ δ·log(1/δ)` **by `volume_inter_tube_le`** ⟹ `vol(Sδ) ≳ 1/log(1/δ)`.
K5 (the deep step): uniform `1/log` content at every scale ⟹ Frostman measure ⟹ `μH[d] S > 0`
for every `d<2`. See `Kakeya2D/PLAN.md` and `PENDING_WORK.md` (three attack paths).

K2's overlap bound is the engine K4 runs on — that dependency is now discharged.

## Invariants
- Defs (`IsKakeya`, `KakeyaSetConjectureDim`) are the frozen audit surface — do not edit.
- `dimH_le_two`, `two_le_dimH`, and all of `Tube.lean` are done — do not touch.
- Commit every green build; never push; never fake green; disclosed `sorry` only.

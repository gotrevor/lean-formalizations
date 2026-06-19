# HANDOFF — Davies / planar Kakeya (branch `kakeya-davies`, 2026-06-18 START)

**Read `DIRECTION.md` first.** This branch is a dedicated, isolated CoW clone of the
`lean-formalizations` umbrella, set up to prove the planar Kakeya conjecture (Davies 1971).
Do not work on any other thread here.

## State at start
- Scaffold landed + **builds green** (`lake build LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Statement`).
- New target dir: `src/LeanFormalizations/GeometricMeasureTheory/Kakeya2D/`
  - `Defs.lean` — `IsKakeya`, `KakeyaSetConjectureDim` (verbatim from `formal-conjectures`). Audit + freeze.
  - `Engine.lean` — `dimH_le_two` **proven, axiom-clean**; `two_le_dimH` is the lone `sorry` (the crux).
  - `Statement.lean` — `davies_kakeya_2d : KakeyaSetConjectureDim 2`, assembled from the two halves.
  - `PLAN.md` — the K1–K5 ladder. `README.md` — what-to-audit + status.
- Wired into `src/LeanFormalizations.lean`.
- `#print axioms dimH_le_two = [propext, Classical.choice, Quot.sound]` (verified).

## Next brick
**K1 (free, do it first):** in `Engine.lean`, reduce `two_le_dimH` to
`∀ d : ℝ≥0, (↑d : ℝ≥0∞) < 2 → μH[d] S ≠ 0` using `le_dimH_of_hausdorffMeasure_ne_zero`
(from `Mathlib.Topology.MetricSpace.HausdorffDimension`) + ENNReal density to lift `∀ d<2, d ≤ dimH S`
to `2 ≤ dimH S`. This replaces the analytic `sorry` with a concrete Hausdorff-positivity `sorry` and
is a clean green lap. Then start K2 (δ-tube overlap bound). See `PLAN.md`.

## Invariants
- Defs are the trusted surface — keep faithful, do not edit.
- `dimH_le_two` is done — do not touch.
- Commit every green build; never push; never fake green; disclosed `sorry` only.

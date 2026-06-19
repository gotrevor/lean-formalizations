# Davies (planar Kakeya, `dimH = 2`) — milestone ladder

**Crux:** `two_le_dimH (S) (h : IsKakeya S) : 2 ≤ dimH S` in `Engine.lean`. The upper bound
`dimH_le_two` is done (axiom-clean) and the headline `davies_kakeya_2d` is assembled, so the
*entire* remaining content is this one inequality. It is genuinely hard — a single-paper
harmonic-analysis result, multi-week, many-lap. Attack it hardest-relevant-first; a lap that
lands one honest prerequisite (even leaving a disclosed `sorry` on the crux) is a success.

## What mathlib already gives you (do NOT reinvent)
- `MeasureTheory.dimH`, `μH[d]` (Hausdorff measure), full API in
  `Mathlib.Topology.MetricSpace.HausdorffDimension` + `…/Measure/Hausdorff.lean`.
- **The Frostman direction is already a lemma:** `le_dimH_of_hausdorffMeasure_ne_zero {s} {d : ℝ≥0}
  (h : μH[d] s ≠ 0) : ↑d ≤ dimH s`. This is the hinge — see K1.
- `dimH_le`, `dimH_mono`, `Real.dimH_univ_eq_finrank`, `dimH_iUnion`, scaling/Hölder image bounds.
- Plane geometry: `EuclideanSpace ℝ (Fin 2)`, `affineSegment`, inner-product/area machinery,
  `MeasureTheory.volume` on `ℝ²`, `Real.volume` basics.

## What mathlib does NOT have (you will build these)
- Any Kakeya maximal function, δ-tube geometry, or tube-overlap estimates.
- Marstrand projection / mass-distribution principle as a packaged theorem (but the one direction
  we need, `le_dimH_of_hausdorffMeasure_ne_zero`, exists — so we avoid the general principle).

## Ladder

### K1 — Reduce the crux to Hausdorff-measure positivity (pure mathlib, no analysis). FIRST BRICK.
Turn `two_le_dimH` into:
> `key : ∀ d : ℝ≥0, (d : ℝ≥0∞) < 2 → μH[d] S ≠ 0  ⟹  2 ≤ dimH S`

via `le_dimH_of_hausdorffMeasure_ne_zero` (gives `↑d ≤ dimH S` for each such `d`) plus
`le_of_forall_lt`/`ENNReal` density (`⊔` of `d < 2` is `2`). This replaces the analytic `sorry`
with a *concrete* one: `∀ d < 2, μH[d] S ≠ 0`. Provable immediately; do it lap 1.

### K2 — δ-tube infrastructure + the two-tube overlap bound (the geometric crux).
- Define `tube (a v : ℝ²) (δ)` = the δ-neighborhood of `affineSegment ℝ a (a+v)`.
- **Overlap lemma:** for unit `v,w` at angle `θ`, `volume (tube a v δ ∩ tube b w δ) ≲ δ² / (θ + δ)`.
  Elementary planar geometry; this is the heart of Córdoba's argument and the hardest *self-contained*
  brick. Anchors (`native_decide`/explicit): parallel tubes overlap `≈ δ`; orthogonal `≈ δ²`.

### K3 — δ-discretization of a Kakeya set.
From `IsKakeya S`: for a δ-net of directions on `S¹` (compactness), get a δ-tube whose core
segment lies in `S`, so `tube … δ ⊆ Sδ` (the δ-neighborhood of `S`). ~`δ⁻¹` tubes, distinct directions.

### K4 — Córdoba `L²` overlap estimate (Minkowski content lower bound).
Cauchy–Schwarz on `f = ∑ 1_{tube_i}`: `(∫ f)² ≤ volume(Sδ) · ∫ f²`, with `∫ f ≳ 1` (each tube has
area `≈ δ`, there are `≈ δ⁻¹`) and `∫ f² = ∑_{i,j} overlap ≲ Σ_θ δ²/(θ+δ) ≲ δ·log(1/δ)` by K2.
Conclude `volume(Sδ) ≳ 1 / log(1/δ)`.

### K5 — Bridge to Hausdorff positivity (close K1's concrete sorry).
Use the K4 Minkowski-content lower bound + a mass-distribution / Frostman construction to show
`μH[d] S > 0` for every `d < 2`. This is the subtle step (Minkowski ≠ Hausdorff in general); for
Kakeya the uniform `1/log` content at every scale feeds a Frostman measure. Assemble `two_le_dimH`.

## Ordering
K1 is free — land it first (concrete sorry). K2 is the self-contained geometric heart — bang on it.
K3 is moderate (compactness + selection). K4 is Cauchy–Schwarz once K2 holds. K5 is the deepest
(content→dimension). Decompose, read the source (Córdoba 1977; Wolff's survey; Tao's notes), feed
Aristotle a clean overlap/`L²` lemma, formalize one prerequisite per lap.

## Portability
Defs mirror `google-deepmind/formal-conjectures`' `Kakeya.lean` verbatim, so `davies_kakeya_2d`
ports directly onto that repo's `kakeya_2d` `sorry` (gated by the DeepMind/CLA legal step).

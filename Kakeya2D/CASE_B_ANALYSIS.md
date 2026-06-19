# Case B / `kakeya_subresolution_content` — the crux pinned to measurable selection

**Date**: 2026-06-19 (analysis lap). Branch `kakeya-davies`. This note records the result of an
independent re-derivation of *why* Case B is hard and *what exactly* unblocks it. The conclusion is
sharper than the previous "Hausdorff-vs-box gap" framing: **the lone remaining obstruction is the
measurability of the per-direction covered-length function** `θ ↦ ℓ_j(θ)`, equivalently the
existence of a **measurable base-point selection** for a Kakeya set (Jankov–von Neumann / KRN
measurable uniformization). mathlib has *no* measurable-selection theorem, so this is a genuine
infrastructure gap, not an ad-hoc combinatorial residual.

## Setup

`HausdorffContentBound S d` (the thing `kakeya_hausdorffContentBound` must produce) is: for some
`r,c>0`, every countable cover `S ⊆ ⋃ₙ Uₙ` with `ediam Uₙ ≤ r` has `∑ₙ ediam(Uₙ)^d ≥ c`, for each
`d<2`. Reduce to closed pieces `Cₙ = closure Uₙ` (same diameters); `E = ⋃ₙ Cₙ ⊇ S` is then an
**Fσ Kakeya set**. Group the pieces by dyadic scale `j` (`diam Cₙ ∈ (2⁻⁽ʲ⁺¹⁾, 2⁻ʲ]`); let
`Fⱼ = ⋃_{scale j} Cₙ` and `Mⱼ = #{scale-j pieces}`, so `∑ⱼ Mⱼ 2⁻⁽ʲ⁺¹⁾ᵈ ≤ ∑ₙ ediam^d =: Σ`.

For a direction `θ` with chosen segment `[a(θ), a(θ)+v(θ)] ⊆ E`, set
`ℓⱼ(θ) = vol{ t∈[0,1] : a(θ)+t·v(θ) ∈ Fⱼ }` (length covered by scale-`j` pieces). Because the segment
lies in `E = ⋃ⱼ Fⱼ`, countable subadditivity gives `∑ⱼ ℓⱼ(θ) ≥ 1` for **every** `θ`
(this is exactly `one_le_tsum_volume_fiber_union`, already proven).

## Why the discrete / single-fixed-net route fails (re-derived, 3 independent confirmations)

The single-scale Córdoba count (`cordoba_cover_count`, proven) at scale `δ=2⁻ʲ` with a `2⁻ʲ`-separated
net of `N=2ʲ` directions reads, after the `2⁻²ʲ` cancellation,
`Sⱼ² ≤ Mⱼ · poly(j)`, where `Sⱼ = ∑_{k<2ʲ} ℓⱼ(θ_k)` is the **aggregate** covered length over the net.
The catch is that this controls the *average* covered length per direction, `Sⱼ/2ʲ`, not any single
direction's value. Concretely:

- **(C1) Single fixed direction is too lossy.** Using only `θ=0` (in every net): `ℓⱼ(0) ≤ Sⱼ ≤
  √(Mⱼ poly)`. With `Mⱼ ≤ Σ 2^{jd}` this gives `ℓⱼ(0) ≤ √Σ · 2^{jd/2} √poly`, and `∑ⱼ 2^{jd/2}`
  **diverges** for every `d>0`. No contradiction. (The earlier "fixed coarse net diverges for `d>1`"
  finding is the same phenomenon seen through the coarse-net count `Mⱼ ≳ Sⱼ²2^{j-J}/poly`.)

- **(C2) The average decays the right way — but the net changes with scale.** `Sⱼ/2ʲ ≤
  √(Mⱼ poly)/2ʲ ≤ √Σ · 2^{j(d/2-1)} √poly`, and `∑ⱼ 2^{j(d-2)/2}` **converges for `d<2`**. So the
  *averaged* sum `∑ⱼ (Sⱼ/2ʲ) ≤ C(d)√Σ`. To turn this into a contradiction we'd need `∑ⱼ (Sⱼ/2ʲ) ≥
  const`, i.e. the **average over directions, at each scale, of the segment's scale-`j` covered
  length, summed over scales, is ≥ 1**. That is `∫₀¹ ∑ⱼ ℓⱼ(θ) dθ ≥ 1` — but the discrete `Sⱼ/2ʲ`
  uses the `2ʲ`-net (*scale-matched* resolution), which is a **different finite direction set for each
  `j`**. There is no single finite net on which `∑ⱼ ℓⱼ(θ) ≥ 1` holds for every member while also
  being `2⁻ʲ`-separated at every scale `j`.

- **(C3) Path-1 "cell-thinning" closes it iff cells fill, which needs the dominant-scale *density*.**
  Pigeonhole each direction to its dominant scale `j(θ)`; group by value; thin the value-`m*` group to
  one direction per `2⁻ᵐ*` angular cell. The Córdoba count then yields content `≳ 2^{m*(2-d)}/poly ≥ c`
  **provided the `2^{m*}` cells fill**, i.e. `D_{m*} := #{θ : j(θ)=m*} ≥ 2^{m*}`. With an adaptive fine
  net of `2ᴷ` directions, `D_{m*} = δ_{m*}·2ᴷ` where `δ_m = ` *measure* of `{θ : j(θ)=m}`; choosing
  `K` past the (fixed, cover-dependent) dominant scale `M₀` of the distribution `δ` makes the cells
  fill. **But `δ_m` is well-defined only if `{θ : j(θ)=m}` is measurable.**

All three roads end at the same place: the argument closes the moment we may **integrate over the
continuum of directions** (`∫₀¹ ∑ⱼ ℓⱼ(θ) dθ ≥ 1`, pigeonhole to a dominant scale `j*`, single-scale
Córdoba at resolution `2⁻ʲ*`). The continuum is "the scale-matched net at every resolution at once",
so it dissolves the net-scale circularity. The *only* thing blocking the integral is the measurability
of `θ ↦ ℓⱼ(θ)`.

## The actual crux: measurability of `θ ↦ ℓⱼ(θ)` (= measurable base-point selection)

`IsKakeya S` provides, per direction, *some* base point via `Classical.choice` — a bare choice
function `θ ↦ a(θ)`, not measurable. For the integral `∫₀¹ ℓⱼ(θ) dθ` to even exist we need `a`
measurable (then `ℓⱼ` is measurable by Fubini — see below). For a **closed** (or Fσ) Kakeya set the
valid-base-point multifunction `B(θ) = {a : segment(a,θ) ⊆ E}` is closed-valued and measurably
varying, so a measurable selection exists by **Kuratowski–Ryll-Nardzewski / Jankov–von Neumann**.
mathlib (v4.29.1) has **no** measurable-selection theorem (`Mathlib.SetTheory.Descriptive` is just
`Tree.lean`; no analytic-set uniformization), so this is a real multi-month infrastructure gap.

The discrete-net machinery in this repo (`exists_dominant_shift`, the `min(·,J)` cap, Case A/B split)
was precisely an attempt to *avoid* measurable selection by using finitely many base points — and
Case B is the unavoidable residue of that avoidance (the cap conflates all sub-resolution scales).

## What IS provable now (the keystone), and the honest route

Given a **measurable** selection `a : ℝ → Plane`, the keystone
`measurable_covered_length` (built this lap, `MeasurableRoute.lean`, no axiom):
`θ ↦ volume {t∈[0,1] : a θ + t•dir θ ∈ F}` is measurable for measurable `F` — via
`measurable_measure_prodMk_left` (Fubini) applied to the measurable set
`{(t,θ) : a θ + t•dir θ ∈ F} ∩ ([0,1]×univ)`. This is the prerequisite the continuum route needs and
the discrete route was invented to dodge.

**Honest route — REFINED (only ONE deep input remains; no new continuum Córdoba needed):**
1. `kakeya_measurable_selection` (Jankov–von Neumann; **true**, mathlib gap — the *sole* deep input):
   an Fσ Kakeya set admits a measurable `θ ↦ a(θ)` with `segment(a(θ),θ) ⊆ E`.
2. `measurable_coveredLength` (**proven this lap**) ⟹ `ℓⱼ` measurable; `one_le_tsum_volume_fiber_union`
   ⟹ `∑ⱼ ℓⱼ(θ) ≥ 1`; Tonelli (`lintegral_tsum`) + `exists_index_ge_of_tsum_lt` ⟹ a dominant `j*`
   with `scaleWeight j* ≤ ∫_{[0,1]} ℓ_{j*}(θ) dθ`. This is `exists_continuum_dominant_scale`
   (**proven this lap**) — **cap-free, so no Case B**: `j*` is the *genuine* dyadic scale (the fiber
   `{g n = j*}` has the real diameter window `(2⁻⁽ʲ*⁺¹⁾, 2⁻ʲ*]`, no `min(·,J)` conflation).
3. **Continuous shift-average** (the next brick — bounded measure theory, **no deep machinery**, was
   blocked *only* by measurability, which (2) now supplies): partition `[0,1)` into the `2^{j*}` cells
   `[i·2⁻ʲ*, (i+1)·2⁻ʲ*)` and substitute `θ = α + i·2⁻ʲ*`; then
   `∫_{[0,1]} ℓ_{j*} = ∫_{[0,2⁻ʲ*)} (∑_{i<2^{j*}} ℓ_{j*}(α + i·2⁻ʲ*)) dα`, so **some base angle `α`**
   has `∑_{i<2^{j*}} ℓ_{j*}(α + i·2⁻ʲ*) ≥ 2^{j*}·∫ℓ_{j*} ≥ 2^{j*}·scaleWeight j*` — exactly the
   discrete numerator. (Continuous analog of the proven `exists_shift_ge`; the integral never exceeds
   `1` here, so the `∫=⊤` corner is vacuous.)
4. **Existing discrete `caseA_content`** (already proven, `NetThinning.lean`): the shifted `2^{j*}`-net
   at base angle `α`, resolution `2⁻ʲ*`, with the numerator from (3) and the genuine scale-`j*` window
   from (2), gives `D⁻¹·cR ≤ ∑'ₙ ediam(Uₙ)^d`. **No new count is built** — the count happens at the
   dominant scale's own resolution, which is precisely what (2)'s cap-free `j*` guarantees. The
   finite/infinite-fiber split (already in `Engine`) handles `s` finite.

**Key consequence:** the earlier "two deep inputs (selection + continuum Córdoba)" framing was
pessimistic. The continuum Córdoba `L²` is **not** needed — the discrete `caseA_content` suffices once
the dominant scale is found at the right (uncapped) resolution. So the route reduces to **one deep
axiom (measurable selection)** + **one bounded provable brick (the continuous shift-average, step 3)**
+ already-proven machinery. That is a materially better state than the current ad-hoc Case-B residual.

## Do NOT relitigate
- The fixed-net L² sum for `d>1` (proven divergent — (C1) above is the same fact).
- The unshifted-grid axiom (possibly adversarially false; superseded by the shifted form already).
- Bourgain bush alone (gives only `dim ≥ 3/2` in the plane).

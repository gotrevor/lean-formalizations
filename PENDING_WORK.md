# PENDING_WORK — lean-formalizations

## ♾️ ACTIVE (2026-06-19): planar Kakeya (Davies) — open `sorry` inventory + attack paths

Branch `kakeya-davies`. **K1 + K2 + K3 + K4 are COMPLETE + axiom-clean, and K5's measure-free
reduction + covering geometry are DONE + axiom-clean.** ONE open `sorry` (`kakeya_hausdorffContentBound`),
now pinned precisely to the K5 **multi-scale Córdoba Hausdorff content bound** (§A below).

### ✅ DONE — K2 (`Tube.lean`): `volume_inter_tube_le` (overlap `≤ 12δ²/(s+δ)`, `s=|sin∠|`),
`volume_tube_le` (`≤6δ`), `volume_tube_ge` (`≥2δ`). Determinant/`addHaar_preimage_linearMap` route.
### ✅ DONE — K3 (`Discretize.lean`, `Directions.lean`): `exists_tube_subset_thickening` (δ-tube of
every direction ⊆ Sδ); explicit trig net `dir θ=(cos θ,sin θ)` with `norm_dir`, `dir_det`
(`det=sin(φ−θ)`), `dir_sep` (Jordan `(2/π)|φ−θ|≤|det|`), `exists_tube_family`; the K2↔K3 interface
`volume_inter_dirTube_le` (overlap `≤ 6πδ/(|k−j|+1)`).
### ✅ DONE — K4 (`Cordoba.lean`, `CordobaL2.lean`): the **full Córdoba L² content bound**.
`double_sum_le_log` (harmonic `∑1/(|k−j|+1) ≤ 2n(1+log n)`), `sum_overlap_le` (denominator
`∑∑vol(T_j∩T_k) ≤ 6πδ·2N(1+logN)`), `sum_tube_ge` (numerator `∑vol(T_k) ≥ N·2δ`),
`lintegral_sum_indicator`/`lintegral_sq_sum_indicator` (∫f, ∫f²), `lintegral_sq_le_measure_mul`
(Cauchy–Schwarz via Hölder p=q=2), `volume_thickening_mul_ge` (`(N·2δ)² ≤ vol(Sδ)·denom`), and the
capstone **`volume_thickening_log_ge`: `1 ≤ vol(Sδ)·12π(1+log(1/δ))`** for `δ≤1/2`. All axiom-clean.

### A. `Engine.lean : kakeya_hausdorffContentBound` — the deep crux (NEW framing 2026-06-19).
**Strategy switched to the measure-free cover route (path 2).** The weak-* limit (path 1) and the
mathlib-Frostman-construction (path 3) are both retired as primary — see "retired" note below.
Engine's crux is now the single named obligation **`kakeya_hausdorffContentBound`**: for a planar
Kakeya `S` and every `0<d<2`, a **Hausdorff content lower bound** — `∃ r>0, ∃ c≠0, ∀ countable cover
S⊆⋃tₙ with ediam tₙ ≤ r, c ≤ ∑ₙ ediam(tₙ)^d`. The `d=0` endpoint is free (μH monotone in `d`).

**Reduction machinery — DONE + axiom-clean (`Cover.lean`, 2026-06-19):**
- `hausdorffMeasure_ne_zero_of_content_bound` / `_of_diam_content` / `_of_contentBound`: the content
  bound ⟹ `μH[d] S ≠ 0`, straight from mathlib's `Measure.hausdorffMeasure_apply`. **No measure to
  build, no weak-* limit.** (`HausdorffContentBound S d` is the packaged Prop.)
- `thickening_subset_iUnion_thickening` / `volume_thickening_le_tsum`: a cover `S⊆⋃Uₙ` thickens to
  `Sδ⊆⋃(Uₙ)δ'`, so `vol(Sδ) ≤ ∑ vol((Uₙ)δ')` — **strict slack `δ<δ'` dissolves the closed-thickening
  inf boundary issue** (`iInf_lt_iff`). The cover-side upper bound pairing with K4's lower bound.
- `volume_thickening_le_of_ediam_le`: per piece, `vol((U)δ') ≤ ofReal((ρ+δ')²)·vol(closedBall 0 1)`
  when `ediam U ≤ ρ` (disc containment + `addHaar_closedBall'`, `finrank=2`);
  `volume_closedBall_one_pos`/`_ne_top` (the constant `≠0`, `≠⊤`, for use as the Frostman `C`).
- `exists_index_ge_of_tsum_lt`: weighted pigeonhole `c≤∑aₙ`, `∑wₙ<c` ⟹ `∃ n, wₙ≤aₙ`.
- **`CordobaL2.volume_thickening_tubes_ge`** (DONE): the K4 `L²` bound `(N·2δ)² ≤ vol(E)·denom` for an
  EXPLICIT base-point family `b` and ANY measurable container `E ⊇` the N net-direction δ-tubes
  (drops `IsKakeya`; `volume_thickening_mul_ge` is now its `E:=Sδ` corollary). The reusable
  localized-Córdoba entry point.
- **`TubeFractional.volume_tube_ge_frac`** (DONE): `ofReal(2δ‖v‖) ≤ vol(tube a v δ)` for `v≠0` — the
  fractional (length-`‖v‖`) tube area bound, the localized-Córdoba numerator for sub-unit segments.
- **`Cover.one_le_tsum_ediam_of_covers`** (DONE): covered unit segment ⟹ `∑ₙ ediam(Uₙ) ≥ 1`; and the
  end-to-end axiom-clean `kakeya_hausdorffContentBound_one` / `hausdorffMeasure_one_ne_zero`.

**Remaining = `kakeya_hausdorffContentBound` (the multi-scale Córdoba estimate, multi-lap).** Given a
cover `{Uₙ}`, `ediam Uₙ ≤ r`, show `∑ ediam(Uₙ)^d ≳ 1`. The obstruction is **mixed scales** (the
single-scale bricks above only lower-bound the *count* of pieces, never `∑ediam^d`, since pieces can
be arbitrarily small). Plan (finite-net double pigeonhole — cleaner than a measure on S¹):
  1. Group pieces by dyadic scale `j` (`ediam ∈ (2⁻ʲ⁻¹,2⁻ʲ]`); `∑ⱼ Mⱼ·2⁻⁽ʲ⁺¹⁾ᵈ ≤ ∑ediam^d`.
  2. For each net direction `θₖ` (`exists_tube_family`, K3): `ℓ_{θₖ}⊆⋃Uₙ`, so `∑ⱼ Lⱼ(k) ≥ 1`
     (`Lⱼ(k)` = length of `ℓ_{θₖ}` covered by scale-`j` pieces). Pigeonhole over `j` (weights
     `6/π²(j+1)²`, via `exists_index_ge_of_tsum_lt`) ⟹ a good scale `j(k)` with `L_{j(k)}(k)≳1/j²`.
  3. Pigeonhole over the `N≈2^{j*}` net directions ⟹ a **dominant scale `j*`** carrying a definite
     fraction of directions, each `≳1/j*²`-covered at scale `2⁻ʲ*`.
  4. **Localized Córdoba** at `δ=2⁻ʲ*` (the hard new derivation): the scale-`j*` cover pieces form a
     container `E` for the δ-tubes about the covered sub-segments. Feed `E` to
     `volume_thickening_tubes_ge` ⟹ `(num)² ≤ vol(E)·denom`, with `vol(E) ≤ M·π(2δ)²` (per-piece
     area), forcing `M ≳ 2^{2j*}/poly(j*)`, hence `∑_{scale j*} ediam^d ≳ M·2⁻ʲ*ᵈ ≳ 2^{j*(2-d)}/poly
     ≥ c` for `r` small (`d<2`).
**DONE (2026-06-19):** the fractional `volume_tube_ge` — `TubeFractional.volume_tube_ge_frac`:
`ofReal(2δ‖v‖) ≤ vol(tube a v δ)` for `v≠0`, via the `e=‖v‖⁻¹•v` frame box (reuses `volume_frame_box`,
`frame_decomp`; no new change-of-variables). The localized-Córdoba numerator input is now in hand.

**DONE (2026-06-19):** sub-brick (a) core — `Cover.one_le_tsum_ediam_of_covers`: a covered unit
segment `ℓ ⊆ ⋃Uₙ` forces `∑ₙ ediam(Uₙ) ≥ 1` (pull back along the isometry `φ:t↦a+t•v`; pieces
`Tₙ={t∈[0,1]|φt∈Uₙ}` cover `[0,1]`, each length `≤ ediam(Uₙ)`; outer-measure subadditivity). Wired
end-to-end axiom-clean: `kakeya_hausdorffContentBound_one` + `hausdorffMeasure_one_ne_zero`
(`μH[1]S≠0`, NO sorry) — proof the whole K5 stack composes. (Geometrically the trivial `dimH≥1`.)

**DONE (2026-06-19, this lap) — sub-bricks (a′), (b), (c) ALL built + axiom-clean.** Every
component lemma of the multi-scale estimate is now in the library; only the cross-scale orchestration
(reference-gated) remains. New (all `#print axioms` = clean):
  (a′) `Cover.exists_pullback_cover` — refines `one_le_tsum_ediam_of_covers` to expose
      `1 ≤ ∑ₙ volume(Tₙ)` + the pullback pieces `Tₙ ⊆ [0,1]`. `Cover.exists_dominant_scale` —
      regroup `∑ₙ fₙ` by dyadic scale fn `g` (`ENNReal.tsum_fiberwise`) + pigeonhole vs telescoping
      weights `scaleWeight j = 1/(2(j+1)(j+2))` (`tsum < 1`, polynomial decay `≳1/j²` — geometric
      would be killed by `δ=2⁻ʲ`) ⟹ dominant scale `j`, covered `≥ scaleWeight j`.
      `Cover.exists_dominant_scale_of_covers` assembles them.
  (b) `Cover.exists_global_dominant_scale` — finite nonempty direction set `s`, per-direction
      profiles `L k ·` with `1 ≤ ∑ⱼ L k j` ⟹ single scale `j`, `s.card·scaleWeight j ≤ ∑_{k∈s} L k j`
      (sum to `≥|s|` via `Summable.tsum_finsetSum`, pigeonhole vs `|s|·scaleWeight`).
  (c) `CordobaL2.volume_thickening_sets_ge` — localized Córdoba `L²` for ARBITRARY measurable
      per-direction sets `R k ⊆ T_k^full`, `R k ⊆ E` ⟹ `(∑ vol(R k))² ≤ vol(E)·denom` (overlaps
      transfer via `R k ⊆` full tube; `volume_thickening_fracTubes_ge` is now a thin instance).
      `TubeFractional.volume_thickening_covered_ge` — `vol(cthickening δ φ(A)) ≥ 2δ·vol(A)` (general
      covered set, frame box). `TubeFractional.tube_smul_subset`/`affineSegment_smul_subset` —
      fractional tube ⊆ full tube. **`CordobaL2.cordoba_cover_count`** — the fully-assembled
      single-scale count: net pts `a k`, covered sets `A k ⊆ [0,1]`, container `P`, `φₖ(A k) ⊆ P` ⟹
      `(∑ₖ 2δ·vol(A k))² ≤ vol(cthickening δ P)·6πδ·2N(1+log N)`. With `vol(Pδ) ≤ M·C·δ²` this is
      `M ≳ (∑vol A k)²/(δ²·logN)`.

**THE remaining obstruction — the net-scale circularity (reference-gated).** `cordoba_cover_count`
needs the net `δ*`-separated with `N≈1/δ*`, `δ*=2⁻ʲ*` the dominant scale; but `j*` is the pigeonhole
OUTPUT, needing the net as INPUT. `sum_overlap_le` ties width = separation = δ, so one fixed net
can't serve all scales. Resolution needs the precise nesting (fix fine net → per-direction dominant
scale → group by `j(θ)` → **thin** to a `2⁻ʲ*`-separated subnet, with the covered-length retention
argument) OR a cleaner cross-scale sum. **Exact structure requested in `ON-LINE-REQUEST.md`
(2026-06-19 UPDATE).** This is the lone gap between the built bricks and `kakeya_hausdorffContentBound`.

**Next-lap entry:** harvest any `ON-LINE-FINDINGS-*` first; then wire the cross-scale orchestration
(the net-thinning combinatorics) connecting `exists_global_dominant_scale` + `cordoba_cover_count` +
`volume_thickening_le_of_ediam_le` into `Engine.kakeya_hausdorffContentBound`. If no findings yet,
attack the net-thinning lemma directly (a `2⁻ʲ*`-separated subnet of a fine net, one direction per
angular cell, retaining covered length) — the only genuinely-new piece left.

**Retired (do NOT relitigate):** path 1 (weak-* limit) needs `Measure`-topology/lsc support mathlib
lacks cleanly; path 3 needs a Frostman *construction* mathlib doesn't have (only the spreading
direction `le_hausdorffMeasure`). `Frostman.lean` is kept as the documented mass-distribution
alternative but is no longer on the critical path.

---

## 🔭 OPEN-ITEM INVENTORY (refreshed 2026-06-17, operator directive)

`src/` is **100% axiom-free** (0 custom axioms, 0 `sorry`/`admit`; `lake build` green, 8274
jobs). Three threads are COMPLETE + axiom-clean — **do not reopen**: Curtis 1990
(no-Frobenius-formula), π/e-transcendence + squaring-the-circle (the `hermite_lindemann` axiom
was discharged + deleted 2026-06-16), and constructible numbers / Wantzel (full iff + 5 classical
impossibilities). Completion records below.

### ✅ COMPLETE (2026-06-18) — power-tower SHARP `iff` (the `0 < x < e^(-e)` divergence)
**DONE, axiom-clean.** The operator-directed target of the 2026-06-17 `DIRECTION.md` is
finished. `EngineLower.tower_diverges_lower` (`0<x<e^(-e) ⟹ ¬∃L`) + the headline
`Statement.tower_converges_iff_full` (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`) are
both proved; `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The proof followed
the planned route exactly: `fixedpoint_exists` (IVT fixed point `y`), `log_fixedpoint_lt_neg_one`
(the repelling seed `x<e^(-e) ⟹ log y < -1` — by contradiction, `log y ≥ -1 ⟹ y ≥ 1/e ⟹
-ye ≤ -1`, no `v·e^v` monotonicity lemma needed), `strict_two_cycle_exists` (IVT on `g-id`
both sides of `y`, where `g'>1` on a neighbourhood from continuity of `g'` + `g'(y)=(log y)²>1`),
and the even/odd-trapping bound (`a(2n) ≥ γ₀ > β₀ ≥ a(2n+1)`) ⟹ distinct limits ⟹ no limit.
The subsequence construction is now the shared `tower_subseq_limits` (used by both directions).
The Lóczi §3 reference was NOT needed (no `ON-LINE-REQUEST` filed).

### ✅ COMPLETE (2026-06-16) — π/e-transcendence, axiom-clean, `hermite_lindemann` DELETED
`Transcendence.transcendental_pi` proved from first principles, axiom-clean;
`squaring_the_circle_impossible_uncond` rewired to it; the cited axiom deleted → repo
math-axiom count = **0**. Assembly: `ETranscendental.lean` (`e_transcendental`, the Hermite
assembly of `exp_polynomial_approx`) → `PiLindemann.lean` (combinatorial reduction + non-monic
analytic engine) → `MonicRootSums.lean` (fact (a) `sum_aeval_roots_int`, Aristotle `9a19f72e`)
→ `SubsetSumEsymm.lean` (fact (b) `subsetSum_esymm_rational`, fundamental theorem of symmetric
polynomials, Aristotle `b7252abe`) → `PiTranscendental.lean`. Both Aristotle proofs independently
kernel-verified. (For the *alternative* path not taken — adopting mathlib PR #28013 on a future
bump — see `archive/findings/ON-LINE-FINDINGS-2026-06-15-pi-transcendence.md`.)


## ✅ COMPLETE (2026-06-14, operator-bounded run): Curtis verification hardening

All four items in `DIRECTION.md` are built, green, sorry-free, axiom-clean
(commits `ea89147`, `0498df8`). Every optional stretch part was also done:

1. ✅ `Boundary.n2_polynomial_relation_exists` — Sylvester hypersurface; n=2/n=3 line.
2. ✅ three new Lemma-2 anchors (⟨3,7,11⟩, ⟨3,13,14⟩, ⟨5,11,23⟩, one also direct) +
   ✅ stretch `frobeniusNumber_6_9_20` (McNugget 43, outside Curtis's family).
3. ✅ `symmetric_guess_not_a_formula` (worked) + ✅ stretch `no_single_polynomial_formula`.
4. ✅ `Curtis/FINDINGS.md` + fixed stale docstrings in `Engine.lean` / `Curtis/README.md`.

Run self-stopped on completion per `DIRECTION.md` (sentinel written). The PARKED targets
below remain Trevor's call for a future, separately-scoped run.

---

## ✅ COMPLETE (2026-06-14, power-tower LOWER half run)

Mandatory `tower_converges_of_mem` (convergence on the FULL Euler interval
`[e^(-e), e^(1/e)]`) is PROVED and **fully axiom-clean** (`[propext,
Classical.choice, Quot.sound]`). The lower-bound crux `two_cycle_collapse` (no
nontrivial 2-cycle of `t↦x^t` for `x ≥ e^(-e)`) is **machine-checked, no axiom** —
via the slope bound `g'(t) ≤ |log x|/e ≤ 1` (`EngineLower.lean`): contraction +
Banach for `x > e^(-e)`, antitone-on-interval for the boundary `x = e^(-e)`.
(The DIRECTION's "subtract the tangent-line inequalities" sketch is mathematically
invalid; the derivative/slope bound is the correct mechanism.)

### Sharp `iff` lower direction (`0 < x < e^(-e)` diverges) — NOW THE ACTIVE TARGET
`tower_converges_iff_full` was omitted as a stretch on the 6-14 run (the convergence half
`tower_converges_of_mem` + `tower_diverges` shipped; the lower divergence requires a *genuine
attracting 2-cycle*, multi-lap real analysis). **As of 2026-06-17 it is the directed goal —
see `DIRECTION.md` and "THE ONE ACTIVE ITEM" at the top.** NO `sorry` was ever left here.

---

## ✅ COMPLETE (2026-06-15): P1 Layer 1 — constructible-numbers algebraic core + all three classical impossibilities

`Geometry/Constructible/` — **PROVED, axiom-clean** (`[propext, Classical.choice,
Quot.sound]` on every headline). Exactly the Layer-1 plan below, and then some:
- `IsSqrtTower` / `IsConstructible` on `IntermediateField ℚ ℝ`; engine
  `IsSqrtTower.finrank_eq_pow_two` (degree `2ⁿ`) via tower law + quadratic step.
- **Doubling the cube**: `cbrt2_not_constructible` (`minpoly ℚ ∛2 = X³−2`,
  Kummer-irreducible; `[ℚ(∛2):ℚ]=3`).
- **Trisecting 60°**: `cos20_not_constructible` (triple-angle ⟹ `2cos20°` root of the
  monic `X³−3X−1`, irreducible by integral-root theorem; degree 3).
- **Squaring the circle**: `squaring_the_circle_impossible (hπ : Transcendental ℚ π)`
  via `IsConstructible.isAlgebraic`. Conditional on `π`-transcendence (mathlib gap).
- Constructibles form a **subfield closed under √** (`IsSqrtTower.sup_exists` +
  `IsConstructible.{add,sub,mul,neg,inv,sqrt}`, `isConstructible_ratCast`).

### ✅ DONE (2026-06-16): P1 Layer 2 + the full converse — Wantzel as an iff
The geometric faithfulness layer is COMPLETE and axiom-clean, and then some:
- `ConstructiblePoint : ℝ×ℝ → Prop` (inductive: `{(0,0),(1,0)}` closed under
  line∩line / line∩circle / circle∩circle). `ConstructiblePoint.isConstructible_coords`
  proves geometry ⟹ algebra via `line_meet_line` / `line_meet_circle` /
  `circle_meet_circle` (`ConstructiblePoint.lean`).
- **Converse** (`Converse.lean`): `AxisConstructible` closed under `+,−,·,⁻¹,/,√` by
  explicit compass constructions; tower induction `isSqrtTower_le_axisField` gives
  algebra ⟹ geometry. Headline `isConstructible_iff_constructiblePoint`.
- Geometric impossibility headlines (`cbrt2_point_not_constructible`,
  `heptagon_point_not_constructible`); positive `isConstructible_cos_pi_div_five`
  (pentagon); heptagon added (`Heptagon.lean`, 5th classical instance).

### ✅ DONE (2026-06-16): squaring-the-circle is now UNCONDITIONAL
`squaring_the_circle_impossible_uncond` no longer takes a hypothesis — it is wired to the
axiom-clean `Transcendence.transcendental_pi` (full Lindemann assembly; see the π completion
record at the top). The "multi-year wall" was discharged from first principles. No axiom remains.

### ✅ DONE (2026-06-16): regular heptagon / 7-gon
`Heptagon.lean` — `twoCosHept_not_constructible`, axiom-clean. Minpoly `X³+X²−2X−1`
derived from `cos(4θ)=cos(3θ)` at `θ=2π/7` (factor out the `c=1` root).

## 🅿️ PARKED — future runs, Trevor's call (NOT this run; do not start)

Preserved for a future, separately-scoped run. These are genuine extensions but are
**explicitly out of scope now** — do NOT treat them as "open frontier" when deciding to stop.

### P2. Upstream Curtis to `Mathlib.NumberTheory.FrobeniusNumber`
mathlib has the n=2 Chicken-McNugget theorem and notes it stops at n=2; Curtis's n=3
impossibility is the natural sequel. Needs a mathlib style pass (drop the bespoke
`IsAdmissible`/audit framing for an idiomatic statement) and an AI-contribution-policy check
(reference corpus: `2026-06-07-mathlib-ai-contribution-policy.md`). Web/CLA-gated.

### P3. Sharpen the "not algebraic" framing
State explicitly: `(s₁,s₂,s₃,g)` lies on no proper hypersurface of ℂ⁴ (graph Zariski-dense).
A short repackaging of `no_polynomial_relation`. (Item 4 of the active run *documents* this;
P3 would be a full theorem-level statement — defer.)

---

## Lemma2.lean lint warnings — LEAVE THEM
The unused-variable warnings on `lemma2`'s hypotheses (`h1,h2,h3,hk_hi,hr_hi`) are the
*mathematical* hypotheses of Curtis's Lemma 2, kept for the audit surface even though this
proof path doesn't consume all of them. Do not strip them. The two unused-simp-arg warnings
are inside Aristotle-verified tactic blocks — not worth the regression risk to touch.

## Aristotle
Nothing genuinely open → Aristotle correctly idle. The old Lemma-1 job (`80d9166c`) is
OBSOLETE (the proof needs no Lemma 1). Do not feed redundant cross-confirms. The verification
items 1–4 are all elementary and do NOT need Aristotle.

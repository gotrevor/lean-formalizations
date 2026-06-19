# PENDING_WORK — lean-formalizations

## 🧘 Reflection — 2026-06-19 (deep-reflection lap, strong model)

A full altitude pass over the expedition. Read STATUS, all recent HANDOFFs, `CASE_B_ANALYSIS.md`,
the Engine/MeasurableRoute/NetThinning source, git log -40, and the reference corpus. Verified the
real kernel state: `#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound,
kakeya_subresolution_content]`, build green (8298 jobs), 1 dormant out-of-lane `sorry` (FastGrowing).

**1. Destination — CONFIRMED, with an honesty recalibration.** `davies_kakeya_2d` (planar Kakeya ⟹
`dimH = 2`, Davies 1971) is a real, famous, single-paper theorem, defs verbatim-portable to
`formal-conjectures`. K1–K5 + the dominant-scale assembly + Case-A are all built and axiom-clean; the
whole lower bound is a kernel proof modulo ONE axiom. **The realistic, valuable endpoint is exactly
"one narrow cited axiom + a fully-built remainder" — and we are essentially there.** The honest call
is to make that one axiom as *clean and citable* as possible. Right now it is **not**:
`kakeya_subresolution_content` is a bespoke 8-hypothesis statement whose own mathematical truth a human
auditor cannot easily check, and the live assembly instantiates it at `J=1`, where Case A (`j=0`) is
near-vacuous and the axiom carries essentially the *entire* lower bound for any realistic fine cover.
The "strictly weaker residual / Case A needs no axiom" framing in prior docstrings was over-optimistic.

**2. Highest-value thing — the measurable-selection route, not more discrete patching.** The discrete
net route provably *cannot* escape Case B: for any fixed `J`, a cover by pieces all finer than `2⁻ᴶ`
triggers the sub-resolution case. So chipping the discrete axiom further is a dead end. The honest
narrowing integrates over the **continuum** of directions (dissolving the net-scale circularity), whose
ONLY blocker is a **measurable base-point selection** `θ↦a(θ)` — a clean, standard, citable theorem
(Jankov–von Neumann / KRN). The spine of that route is ALREADY proven + axiom-clean this expedition
(`measurable_coveredLength`, `exists_continuum_dominant_scale`, `exists_shift_ge_integral`).

**3. What an outside expert would say we're missing — already largely captured, one re-aim.** The
architecture is right (keep the Córdoba ladder — 95% built, don't pivot to Davies' duality and throw it
away). The missing move is to **re-aim the cited axiom**: stop treating `kakeya_subresolution_content`
as the destination, and route the headline through the measurable-selection spine so the cited axiom
becomes the citable `kakeya_measurable_selection`. That is a genuine *faithfulness* upgrade (a reader
can confirm Jankov–von Neumann is true; they cannot easily confirm the bespoke residual).

**4. Faithfulness at altitude.** `Statement.lean` / `Defs.lean` audited against the source: headline
`davies_kakeya_2d : KakeyaSetConjectureDim 2` unfolds to "every Kakeya set in ℝ² has `dimH = 2`",
defs mirror `formal-conjectures` verbatim. No statement drift. The one caveat is the *axiom* honesty
above (a proof-side, not statement-side, issue), now recorded in the STATUS ledger.

**KEEP:** the Córdoba L² route + the measurable-selection architecture + the lap-over-lap narrowing
discipline (it has produced monotone progress, not circling).
**STOP:** (a) relitigating the fixed-net L² sum for `d>1` (proven dead end); (b) treating
`kakeya_subresolution_content` as the destination axiom or calling it a "narrow residual"; (c) further
discrete-route patching to dodge Case B (provably impossible).
**SINGLE HIGHEST-VALUE NEXT TARGET: (W)** build `kakeya_hausdorffContentBound_of_measurableSelection`
(takes the measurable selection as a *hypothesis*, zero new axioms; all pieces proven), then switch the
headline to a clean `kakeya_measurable_selection` axiom, retiring `kakeya_subresolution_content`.
Reasoning: it converts the headline's lone axiom from a murky bespoke residual into a standard named
theorem using pieces already in hand, and makes (S) — discharging measurable selection — the genuine,
well-posed standing crux for subsequent laps. (S) is useless without (W) — the headline can't reach it
otherwise — so (W) is the true shortest path, not an easy-leaf detour. **After (W): (S)** = discharge
measurable selection (Jankov–von Neumann / KRN, or a bespoke argmin-‖a‖ over `B(θ)={a:segment⊆E}`).

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

### A0‴. ⭐ MILESTONE (2026-06-19, measurable-route lap): Case B pinned to MEASURABLE SELECTION; two route bricks built.

**Committed (`0455775`, `94db0d8`), full library green (8298 jobs), both new lemmas `#print
axioms`-clean.** This lap re-derived the Case-B obstruction independently from three angles
(`Kakeya2D/CASE_B_ANALYSIS.md`) and pinned it precisely: the proof closes the instant one integrates
over the **continuum** of directions (`∫₀¹ ∑ⱼ ℓⱼ(θ) dθ ≥ 1` → dominant scale `j*` → single-scale
Córdoba at `2⁻ʲ*`); the continuum is "the scale-matched net at every resolution at once", so the
net-scale circularity that forces the discrete cap / Case B never arises. **The lone blocker is the
measurability of `θ ↦ ℓⱼ(θ)`, i.e. a measurable base-point selection** (`IsKakeya` gives only
`Classical.choice`; Jankov–von Neumann / KRN — a genuine mathlib v4.29.1 gap, no measurable-selection
theorem present). The discrete `2ᴶ`-net machinery (cap + Case A/B) was built *only* to avoid this
integral; Case B is the residue of that avoidance.

**Two provable bricks of the honest (measurable-selection) route built this lap (`MeasurableRoute.lean`,
both take the selection as a HYPOTHESIS — no new axioms):**
- `continuous_dir` / `measurable_dir`.
- `measurable_coveredLength` — **keystone**: for measurable base-point `a` and direction `w` and
  measurable target `F`, `θ ↦ vol{t∈[0,1] : a θ + t•w θ ∈ F}` is measurable (Fubini,
  `measurable_measure_prodMk_right`). The prerequisite the continuum route needs and the discrete
  route dodged.
- `exists_continuum_dominant_scale` — **cap-free, no Case B**: given a measurable selection covering
  the arc `θ∈[0,1]`, a dominant scale `j` with `scaleWeight j ≤ ∫_{[0,1]} vol{t∈[0,1]:
  a θ+t·dir θ ∈ ⋃_{g n=j} C n} dθ`. Assembled from the keystone + `one_le_tsum_volume_fiber_union`
  (per-direction `∑ⱼ ℓⱼ ≥ 1`) + Tonelli (`lintegral_tsum`) + the `scaleWeight` pigeonhole.

**UPDATE (same lap, cont.) — the continuum Córdoba is NOT needed; spine COMPLETE.** Architecture
insight (`CASE_B_ANALYSIS.md`): once `j*` is the *uncapped* dominant scale, the count is done at its
own resolution `2⁻ʲ*` by the **existing discrete `caseA_content`**, fed by a **continuous
shift-average**. So no continuum Córdoba `L²` build is needed. The continuous shift-average is now
**PROVEN** this lap: `exists_shift_ge_integral` (`MeasurableRoute.lean`, axiom-clean) — for measurable
`f` with `∫_{[0,1]}f < ⊤`, some `α∈[0,2⁻ʲ)` has `2ʲ·∫f ≤ ∑_{i<2ʲ} f(α+i·2⁻ʲ)` (cell tiling +
translation invariance + `ae_eq_of_ae_le_of_lintegral_le`). The whole measure-theoretic SPINE of the
honest route (steps 2–4) is now proven: `measurable_coveredLength` → `exists_continuum_dominant_scale`
→ `exists_shift_ge_integral` → existing `caseA_content`.

**ONLY two items remain (in order):**
1. **(W) Wiring** (no new axioms): `kakeya_hausdorffContentBound_of_measurableSelection` taking a
   measurable base-point selection as a *hypothesis* — reduce to closed pieces (Engine does this),
   build `ℓ_{j*}`, apply the three spine lemmas + `caseA_content` (uncapped `g = dyadicIdx` gives the
   genuine scale-`j*` window; finite/infinite-fiber split as in Engine). Mirrors the Engine assembly
   at the *uncapped* dominant scale ⟹ no Case B. A real ~150-line assembly but all pieces proven.
2. **(S) Measurable selection** `∃ measurable a, ∀θ, segment(a θ,θ) ⊆ E` for the Fσ Kakeya set. The
   ONE genuine mathlib gap (descriptive set theory; KRN/JvN; true theorem). Reference-gated
   (`ON-LINE-REQUEST.md` UPDATE 5 ask 1). Possibly a bespoke explicit selection (argmin-‖a‖ over the
   closed-valued `B(θ)`) sidesteps full KRN.

**NEXT-LAP ENTRY:** harvest any `ON-LINE-FINDINGS-*` (UPDATE 5) first. Then do (W) (it's all-proven
pieces; gives a hypothesis-gated headline), then attack (S). The discrete Case-A/B path
(`Engine.kakeya_subresolution_content`) stays the live critical path until (W)+(S) land — do NOT delete it.

### A0″. ⭐ MILESTONE (2026-06-19, Case-A discharge lap): opaque dominant-scale axiom GONE; Case B isolated.

**Committed, `lake build` green (8297 jobs), `#print axioms` verified:** `davies_kakeya_2d` now =
`[propext, Classical.choice, Quot.sound, kakeya_subresolution_content]` (NO `sorryAx`). The former
monolithic `kakeya_dominant_scale_count` is **deleted**. The headline `kakeya_hausdorffContentBound`
is a real proof from the proven bricks; the lone axiom is the strictly-narrower **Case B** residual.

**What got proven this lap (the whole dominant-scale orchestration — the historic blocker):**
- `NetThinning.dyadicIdx` + `dyadicIdx_window` — the dyadic length window `2⁻⁽ʲ⁺¹⁾ < ρ ≤ 2⁻ʲ`.
- `NetThinning.caseA_content` — base-angle, finite-fiber content brick (Córdoba count + `content_ratio_lower`
  constant + numerator ⟹ `D⁻¹·cR ≤ ∑'ₙ ediam(Uₙ)^d`).
- `Engine.kakeya_hausdorffContentBound` — full assembly: closed-piece reduction (`Metric.ediam_closure`)
  → per-direction measurable pullbacks (`exists_measurable_pullback_cover`) → capped dyadic scale fn
  `g = min(dyadicIdx, J)` → per-scale union length `L` → `exists_dominant_shift` (shifted `2ʲ`-subnet,
  base angle `c = β·2⁻ᴶ`) → numerator `1/((j+1)(j+2)) ≤ ∑ 2·2⁻ʲ·vol A` → **Case A** (`j<J`: genuine
  scale-`j` window, finite/infinite-fiber split — infinite ⟹ `tsum=⊤`) via `caseA_content`; **Case B**
  (`j=J`) cites `kakeya_subresolution_content`. This is the SHIFTED (faithful) form; the former
  unshifted axiom (possibly adversarially false) is discarded — the faithfulness finding is resolved.

**THE remaining crux = `kakeya_subresolution_content` (Case B, the Hausdorff-vs-box gap).** Cover
dominated by pieces FINER than the net resolution `2⁻ᴶ`; the scale-`J` fiber is not a single scale, so
`cover_content_per_scale` (needs the `ediam ≥ 2⁻⁽ʲ⁺¹⁾` lower bound) does not apply.

**Sharp obstruction worked out this lap (recorded in `ON-LINE-REQUEST.md` UPDATE 4):** the multi-scale
Córdoba `L²` sum with the *fixed* `2ᴶ`-net **provably diverges to 0 for `d>1`** (the relevant range):
the min of `∑_{j≥J} S_j² 2^{j(1-d)}` s.t. `∑_{j≥J} S_j ≥ 2ᴶ⁻¹` is `(2ᴶ⁻¹)²/∑_{j≥J}2^{j(d-1)} = 0` since
`∑_{j≥J}2^{j(d-1)} = ∞` for `d>1`. The coarse net's count `M_j ≳ S_j²2^{j-J}/poly` is too weak at fine
scales. So a single fixed net cannot close `d>1`; the right count at sub-scale `j` needs the **`2ʲ`-net**
(`M_j ≳ S_j(j)²/poly(j)`), but each scale then uses a different net — no single cross-scale sum is
obviously bounded below. Case B is exactly "no single dominant scale — mass at unboundedly fine scales".

**THREE attack paths for Case B (next lap):**
1. **Contradiction via piece-count bound.** Assume `Σ = ∑ediam^d < c`. Then `M_j ≤ Σ·2^{jd}` (bounds
   #fine pieces per scale). Feed this into the per-scale Córdoba *upper* bound on `S_j` and sum; show
   the total coverable length `< 2ᴶ` (required), contradiction. (This WORKS for `d<1` — I verified the
   arithmetic — but the headline needs `d→2`, so `d<1` alone doesn't reduce the essential dependency;
   the `d>1` version needs the right-resolution per-scale count.) Reference-gated: need the exact
   inequality for `d>1` (UPDATE 4 ask 1).
2. **Davies' 1971 projection/duality** — may sidestep the multi-scale Córdoba entirely and be more
   formalization-tractable. Reference-gated (UPDATE 4 ask 2; first request point 2 — re-asked urgently).
3. **Uncap the scale function** so Case A handles ANY genuine dominant scale `j ≤ J` (currently the
   `min(·,J)` cap conflates all sub-`2⁻ᴶ` pieces into bucket `J`, spuriously triggering Case B even
   when a genuine coarse dominant scale exists). Needs an `exists_dominant_shift` variant that EITHER
   finds a genuine `j ≤ J` (Case A) OR certifies scales `> J` carry ≥ half the aggregate (true Case B,
   `j₀ > J`). Tightens which covers hit the axiom; does NOT eliminate it (genuinely-fine covers remain).

### A0′. ⭐ BREAKTHROUGH (2026-06-19, retention lap): the net-thinning combinatorics is PROVEN + a faithfulness fix identified.

**Three new `#print axioms`-clean bricks (`NetThinning.lean`), the literal "retention" gap from A0:**
- `sum_range_mul_eq_sum_shift` — AP decomposition `∑_{k<B·M} L k = ∑_{β<B} ∑_{i<M} L(β+B·i)`
  (explicit bijection `range(B·M) ≃ range B ×ˢ range M`, `k↦(k%B,k/B)`).
- `exists_shift_ge` — the **shift pigeonhole** `∃ β<B, ∑_{k<B·M} L k ≤ B·∑_{i<M} L(β+B·i)`: some
  dyadic shift `β` of the coarse subnet captures ≥ the FULL average of the fine net's covered length.
- `one_le_tsum_volume_fiber_union` — `vol(⋃ₙTₙ) ≤ ∑ⱼ vol(⋃_{g n=j}Tₙ)`; gives the per-direction
  `1 ≤ ∑ⱼ L k j` with `L k j = vol(⋃_{g n=j} Tₙ)` = the genuine covered (UNION) length per scale.

**The full resolution of the net-scale circularity (now fully mapped, mathematically airtight):**
1. Fix a FINE net of `2ᴶ` directions `k·2⁻ᴶ` (each with its OWN chosen base point — FINITE, so NO
   measurability issue). Pull back (`exists_pullback_cover`): `vol(⋃ₙ Tₙᵏ) ≥ 1`.
2. `L k j := vol(⋃_{g n=j} Tₙᵏ)` (union, NOT the overcounted `∑vol` — overlaps among same-scale
   pieces would otherwise inflate the numerator). `one_le_tsum_volume_fiber_union ⟹ 1 ≤ ∑ⱼ L k j`.
3. `exists_global_dominant_scale` (generic, already proven) on `s=range 2ᴶ`, this `L` ⟹ a global
   dominant scale `j*` with `∑_{k<2ᴶ} L k j* ≥ 2ᴶ·scaleWeight j*`.
4. `exists_shift_ge` (B=2^{J-j*}, M=2^{j*}, needs `j*≤J`) ⟹ a shift `β` with
   `∑_{i<2^{j*}} L (β+2^{J-j*}·i) j* ≥ 2^{j*}·scaleWeight j*`. The subnet directions are
   `β·2⁻ᴶ + i·2⁻ʲ*` — a `2⁻ʲ*`-separated AP with **base angle `θ₀ = β·2⁻ᴶ`** — covered length
   retained EXACTLY (no loss). `A_i := ⋃_{g n=j*} Tₙ^{β+2^{J-j*}i}`, `φ_i(A_i) ⊆ ⋃_{g n=j*} tₙ`.
5. Feed the shifted subnet to (a **base-angle generalization of**) `cover_content_per_scale`.

**TWO genuinely-open residuals (both now crisply isolated — the only things left):**
- **(R1) `j* ≤ J` / Case B.** Step 4 needs `j* ≤ J`. Force it by CAPPING the scale fn at `J`
  (`g_J n = min(scale n, J)`); then `j*≤J`. If `j*<J` (**Case A** — fully clean, no measurability,
  no base-point issue) proceed. If `j*=J` (**Case B**: the cover is dominated by pieces FINER than
  the net resolution `2⁻ᴶ`) the bucket isn't a single scale → handle separately (many tiny pieces ⟹
  large `∑ediam^d` directly, OR re-run at larger `J`). Case B is a smaller, separate sub-lemma.
- **(R2) base-angle Córdoba.** `cover_content_per_scale`/`cover_count_lower`/`cordoba_cover_count`/
  `volume_thickening_sets_ge`/`sum_overlap_le`/`sum_tube_ge`/`volume_inter_dirTube_le` all hardcode
  the net direction `dir(k·δ)`. The overlap depends ONLY on the angle gap `(k−j)·δ` (shift-invariant
  — see `dir_det`/`dir_sep`: gap of `c+kδ`,`c+jδ` is `(k−j)δ`), so adding a base angle `c` and using
  `dir(c+k·δ)` is MECHANICAL (each lemma's math is verbatim). ~7 lemmas, 3 files. **Alternative:**
  ROTATE the whole config by `−c` (isometry; `ediam`-invariant, `dir`-equivariant) to reduce the
  shifted net to the unshifted one on the rotated cover (same `∑ediam^d`) — avoids touching Córdoba
  but needs a rotation `LinearIsometryEquiv` on `EuclideanSpace ℝ (Fin 2)` + `R(dir φ)=dir(φ−c)`.

**⚠️ FAITHFULNESS FINDING — the current axiom uses the UNSHIFTED grid; its TRUTH is uncertain.**
`kakeya_dominant_scale_count` asserts the **unshifted** net `dir(k·2⁻ʲ)` (k<2ʲ) is well-covered at
some scale. The shift-average proves only that SOME shift `θ₀` works (the unshifted `θ₀=0` may be
adversarially defeatable: cover the dyadic-grid directions only at scales ≠ their own). So the axiom
is **SUFFICIENT** for `davies_kakeya_2d` (the reduction is a valid kernel proof) but its OWN truth is
not established — a possibly-unprovable lemma. **The provably-true form is the SHIFTED net**
(`∃ c, dir(c+k·2⁻ʲ)` well-covered). NEXT LAP: restate the axiom to the shifted form (do (R2) first),
which is both the faithfulness fix AND the form the proven bricks discharge. Don't try to prove the
unshifted form — it may be false. (See `ON-LINE-REQUEST` UPDATE 3.)

**NEXT-LAP ENTRY (precise):** (i) ✅ (R2) DONE this lap — the Córdoba chain
(`volume_inter_dirTube_le`…`cover_content_per_scale`) is base-angle generalized (`c`); (ii) restate
`kakeya_dominant_scale_count` to the shifted form `∃ c, …` (or delete it and prove
`kakeya_hausdorffContentBound` directly); (iii) wire the assembly (Case A); (iv) isolate Case B (R1).

**UPDATE (retention lap, cont.) — bricks now ALL built; assembly + Case B are what's left:**
This lap proved, all `#print axioms`-clean (`NetThinning.lean`): `exists_measurable_pullback_cover`
(closed-piece cover ⟶ measurable pullback `Tₙ`, `φ(Tₙ)⊆Uₙ`, `vol(⋃Tₙ)≥1`), `one_le_tsum_volume_fiber_union`,
`exists_dominant_shift` (fine-net profiles ⟶ dominant scale `j≤J` + shift `β`, retained covered
length), and base-angle `cover_content_per_scale`. **The assembly is now a (mechanical) integration:**
  • Reduce to CLOSED cover pieces `Uₙ = closure tₙ` (same `ediam`, still covers `S`) — gives
    measurable covered sets via `exists_measurable_pullback_cover`. [prove `kakeya_hausdorffContentBound`
    directly; the axiom's `Finset s`/numerator shape is for the unshifted form we're discarding.]
  • For `k < 2ᴶ`: `v_k = dir(k·2⁻ᴶ)` (`norm_dir`), `IsKakeya` ⟹ base point `a_k` (`choose`),
    `exists_measurable_pullback_cover` ⟹ `T^k`. Capped scale `g_J n = min(scale n, J)`,
    `L k j = vol(⋃_{g_J n=j} T^k_n)`; `one_le_tsum_volume_fiber_union ⟹ 1 ≤ ∑ⱼ L k j`, `hsupp` from cap.
  • `exists_dominant_shift ⟹ j≤J, β`; subnet covered sets `A_i = ⋃_{g_J n=j} T^{β+2^{J-j}i}_n`
    (measurable), base angle `c = β·2⁻ᴶ`, directions `dir(c + i·2⁻ʲ)`. Numerator
    `∑ᵢ 2δ vol(A_i) ≥ 2·scaleWeight j = 1/((j+1)(j+2))` at `δ=2⁻ʲ`.
  • **Finset-truncation worry DISSOLVES via a finite/infinite split on the scale-`j` fiber
    `{n : g_J n = j}`:** if INFINITE, there are ∞-many pieces each `ediam ≥ 2⁻⁽ʲ⁺¹⁾`, so
    `∑'ₙ ediam^d = ∞ ≥ c` trivially; if FINITE, take `s = ` that fiber (`Set.Finite.toFinset`) and run
    base-angle `cover_content_per_scale`. No ε-truncation needed.
  • Feed `c, A_i, s` to base-angle `cover_content_per_scale` ⟹ `∑_{n∈s} ediam(Uₙ)^d ≥` const; and
    `ediam(closure tₙ)=ediam tₙ` ⟹ `∑'ₙ ediam(tₙ)^d ≥ c`. Done — EXCEPT Case B.
  • **Case B = `j = J` (cap saturated):** the bucket `{n : g_J n = J} = {n : ediam tₙ ≤ 2⁻ᴶ}` is NOT a
    single scale, so `cover_content_per_scale` (needs `2⁻⁽ʲ⁺¹⁾ ≤ ediam ≤ 2⁻ʲ`) doesn't apply, and the
    pieces can be arbitrarily small so the count `|s|` doesn't bound `∑ediam^d`. **This is the genuine
    remaining obstacle (R1)** — it is exactly the Hausdorff-vs-box gap (box-dim-2 = K4 is proven;
    promoting to Hausdorff for an arbitrarily-fine cover is the deep part). Hypotheses to try next lap:
    pick `J` adaptively so `j < J` (needs a bound on the dominant scale — unclear it exists for general
    covers); OR a separate sub-lemma handling sub-resolution covers via K4 (`volume_thickening_log_ge`)
    at scale `2⁻ᴶ` (gives `|s| ≳ 2^{2J}/poly` but still needs an `ediam` lower bound — the crux).
    See `ON-LINE-REQUEST` UPDATE 3 ask 3b (how the literature handles this for non-measurable Kakeya sets).

### A0. ⭐ MILESTONE (2026-06-19, late lap): crux narrowed to ONE crisp axiom + machine-checked reduction.
`davies_kakeya_2d` now `#print axioms`-reduces to `[propext, Classical.choice, Quot.sound,
**kakeya_dominant_scale_count**]` — NO `sorryAx`. The monolithic `kakeya_hausdorffContentBound` sorry is
GONE; it is now a full kernel-checked proof from the single axiom `kakeya_dominant_scale_count`
(`Engine.lean`), via the new bricks (all axiom-clean this lap):
- `Cover.cover_content_per_scale` — Córdoba piece-count ⟹ Hausdorff content contribution
  `(∑ₖ 2δ vol A k)²·η^d ≤ (∑_{n∈s} ediam^d)·C₀` (division-free).
- `Engine.exists_const_mul_pow_le` / `exists_pos_le_pow_div` — exponential beats any fixed poly
  (root-free Bernoulli + √b induction): the uniform content constant `c ≤ b^j/(1+j)^m`.
- `Engine.content_ratio_lower` — the assembled real-analysis constant:
  `cR·(4·(1/4)^j)·(12π(1+j log2)) ≤ (1/((j+1)(j+2)))²·((1/2)^(j+1))^d` for all `j`.

**THE remaining obligation = discharge `kakeya_dominant_scale_count`** (the dominant-scale extraction /
net-thinning — see its docstring + `ON-LINE-REQUEST.md` UPDATE 2 for the verbatim statement). Three
attack paths for next lap:
  1. **Decompose-and-narrow:** prove the *geometric wiring* of the axiom in Lean from existing bricks
     (`exists_pullback_cover` per net direction → dyadic scale fn `g` on cover pieces →
     `exists_global_dominant_scale` to a global `j*`), isolating the genuinely-open *thinning* as a
     SMALLER axiom (covered-length retention when passing to the `2⁻ʲ*`-net). This shrinks the axiom
     even if the thinning stays open. **Likely the best next step.**
  2. **Reference-driven:** harvest any `ON-LINE-FINDINGS-*` answering UPDATE 2, then transcribe the
     dominant-scale lemma (Wolff/Mattila/Bourgain–Demeter) directly.
  3. **LP route:** attempt to prove the multi-net LP lower bound (objective `∑ⱼ Sⱼ²2^{-jd}/(1+j)`
     over full `2⁻ʲ`-nets) is bounded below — or find the extra cover structure it needs. (Naive
     versions diverge; see UPDATE 2.) Lower priority — high risk it needs path-2 insight first.

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

**THREE ATTACK PATHS for the net-thinning crux (per unblock protocol, 2026-06-19):**
1. **Per-direction dominant scale → group by value → cell-thin (the "standard" route).** Fix a fine
   net of `2ᴶ` directions (`J` large). Each direction `θ`: `exists_dominant_scale` ⟹ dominant scale
   `j(θ)≤J` with covered length `≥scaleWeight(j(θ))`. Pigeonhole the *value* `j(θ)` over the `2ᴶ`
   directions (finitely many values `≤J`, weights `~1/j²`) ⟹ a value `j*` shared by `≳2ᴶ/J²`
   directions. Partition the circle into `2^{j*}` angular cells of width `2⁻ʲ*`; the `≳2ᴶ/J²` good
   directions occupy `≳min(2^{j*}, 2ᴶ/J²)` cells (pigeonhole). Pick one good direction per occupied
   cell ⟹ a `2⁻ʲ*`-separated subnet of `n*≈2^{j*}` directions, each covered `≳scaleWeight(j*)≳1/j*²`
   at scale `j*`. Feed to `cover_count_lower` (ρ=2⁻ʲ*, δ=2⁻ʲ*, N=n*). **Risk/open point:** need
   `2ᴶ/J² ≳ 2^{j*}` so cells fill — i.e. `j*` can't be too close to `J`. Resolve by choosing `J`
   adaptively or arguing the `j*=J` case separately (then pieces are at the finest scale = trivial).
   This is the route I believe the literature uses; `ON-LINE-REQUEST` asks for the exact retention bound.
2. **Aggregate per-scale + convexity, no thinning (longshot).** Use `cover_count_lower` at EVERY
   dyadic scale `j` with the FULL net `N_j=2ʲ`; get `S_j² ≤ M_j·C·(1+j)` where `S_j=∑_{k<N_j}vol(A_j^k)`.
   Need a lower bound forcing `∑_j M_j 2⁻ʲᵈ ≥ c`. The naive nested-net bound `∑_j S_j ≥ N_{J₀}` +
   Cauchy–Schwarz DIVERGES (proven dead end — see handoff). BUT maybe a *weighted* convexity
   (Hölder with exponent tied to `d`) over the per-scale `S_j² ≤ M_j poly(j)` closes it without
   thinning. Low confidence; try only if path 1 stalls.
3. **Bypass the net entirely — direct content bound via the K4 Minkowski bound at the dominant scale.**
   Instead of re-running Córdoba on the net, use the EXISTING `volume_thickening_log_ge`
   (`vol(Sδ)≳1/log(1/δ)`) at `δ=2⁻ʲ*` together with `volume_thickening_le_tsum`/`cover_count_lower`'s
   container bound: `1/log(1/δ) ≲ vol(Sδ) ≤ ∑_{n} vol((Uₙ)δ)`, split by scale, dominant-scale term
   `≈ M_{j*}·δ²`. Combine with a pigeonhole isolating the `j*≈log(1/δ)` term. **Risk:** same
   mixed-scales obstruction (other-scale terms can dominate) unless a pigeonhole over `δ` choices is
   added; essentially reduces to path 1's bookkeeping but reuses K4 wholesale. Worth scoping as it may
   shortcut the localized-Córdoba re-derivation.

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

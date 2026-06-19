# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8300 jobs) · **Updated**: lap 2026-06-19 (⚠️→✅ FALSE AXIOM FOUND & REMOVED; Kakeya2D now axiom-DECLARATION-free) · `9596dad` · **`davies_kakeya_2d` (planar Kakeya, Davies 1971) is a COMPLETE machine-checked proof with NO mathematical axioms: `#print axioms = [propext, Classical.choice, Quot.sound]` (re-verified this lap).** The headline routes through the *elementary open-cover* selection (`exists_measurable_selection_of_isOpen` + `kakeya_hausdorffContentBound_elementary`, `Selection.lean`). **This lap's finding:** the off-headline legacy axiom `kakeya_subresolution_content` (the discrete-route "Case-B residual"), cited by every prior lap as "true but deep", is **PROVABLY FALSE** — kernel-checked refutation `kakeya_subresolution_content_is_unsound` (it dropped the `hcR` link cR↔d, so its conclusion had to hold for arbitrary `cR>0` vs a fixed finite `∑'ediam^d`; and even with `hcR` it fails for `d>1` via spatially-separated segments). The false axiom is **removed**; its sole use (Case-B branch of the legacy `kakeya_hausdorffContentBound`) is now a disclosed `sorry`. So `Kakeya2D/` is now axiom-declaration-free; remaining holes = 1 disclosed off-headline `sorry` (legacy Case-B, redundant) + 1 dormant out-of-lane `sorry` (FastGrowing). **Faithfulness re-verified against `~/src/formal-conjectures/FormalConjectures/Wikipedia/Kakeya.lean`: `IsKakeya`/`KakeyaSetConjectureDim` match verbatim; `davies_kakeya_2d` is a drop-in axiom-clean proof of that repo's `kakeya_2d := sorry` (line 70).**

> ♾️ **EXPEDITION COMPLETE (headline) — branch `kakeya-davies` (2026-06-19): planar Kakeya
> conjecture (Davies 1971).** Target `davies_kakeya_2d : KakeyaSetConjectureDim 2`
> (`GeometricMeasureTheory/Kakeya2D/`) is **PROVEN and axiom-clean**:
> `#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound]` (verified this lap). Upper
> bound `dimH_le_two` done; the lower bound `two_le_dimH` is complete via K1 (reduction to a Hausdorff
> **content** bound for all `d<2`) + the full Córdoba `L²` ladder (K2–K4) + the measure-free cover
> route K5 + the **measurable selection, now discharged elementarily**.
> **The selection crux — formerly the lone axiom `kakeya_borel_selection` (von Neumann /
> Jankov–von Neumann), believed multi-lap deep DST — was eliminated this lap by an ELEMENTARY argument
> that bypasses descriptive set theory entirely.** Key insight: route the content bound through an
> **open** cover (fatten each cover piece to an open superset at vanishing `ediam^d` cost,
> `exists_thickening_radius_rpow_le`); then for an open target a compact unit segment has a **tube
> neighbourhood** inside it (`IsCompact.exists_thickening_subset_open`), so *any* base point near the
> Kakeya base point — in particular one from a fixed dense sequence — gives full coverage `= 1`. The
> first-hit dense-sequence selector is measurable (`measurable_find` + `measurable_coveredLength`).
> Chain: `exists_measurable_selection_of_isOpen` (axiom-clean selection for open covers) →
> `content_bound_step` (the cover-agnostic Córdoba spine, factored out of `Wiring.lean`) →
> `kakeya_hausdorffContentBound_elementary` (ε-fattening + send overshoot → 0) → `two_le_dimH`.
> **The abstract JvN reduction `kakeya_aeMeasurable_selection_of_jvn` + the projection-is-analytic
> down payment `analyticSet_proj_and_Icc_subset` are KEPT** as honest hypothesis-gated structure
> (no axiom). The legacy DISCRETE route (`Engine.kakeya_hausdorffContentBound`, Case A proven / Case B)
> is **preserved but fully superseded and OFF the headline path** — `davies_kakeya_2d` does not depend
> on it. Its reusable bricks (`NetThinning.caseA_content`, the Córdoba `L²` ladder) ARE reused by the
> elementary route.
> **UPDATE 2026-06-19 (review lap):** the discrete route's Case-B axiom `kakeya_subresolution_content`
> was found **UNSOUND** (kernel-checked refutation `kakeya_subresolution_content_is_unsound`) and
> **REMOVED**; its sole use is now a disclosed `sorry`. So `Kakeya2D/` is axiom-DECLARATION-free and
> ALL headlines are axiom-clean. The threads below are COMPLETE/axiom-clean and frozen — do not touch them.
> (`Logic/FastGrowing/Basic.lean` carries one dormant disclosed `sorry`, out of the Kakeya lane.)

## Where it stands
**All six headlines are now 100% axiom-free** — every one's `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]`, including the **Kakeya** headline `davies_kakeya_2d`. The Kakeya lower bound `two_le_dimH` is a full kernel proof via the *elementary open-cover selection* route (`Selection.lean`): fatten the cover to an open superset at vanishing `ediam^d` cost, then a compact unit segment in an open set has a tube neighbourhood, so a fixed dense base point achieves full coverage — no descriptive set theory, no measurable-selection axiom. This lap the LAST lane axiom (the off-headline legacy `kakeya_subresolution_content`) was found **unsound** and removed (kernel-checked refutation kept as a guard), so `Kakeya2D/` is axiom-declaration-free; the only remaining Kakeya hole is a disclosed, redundant, off-headline `sorry` in the legacy discrete route's Case-B branch. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
- **2026-06-19 (FRESH-MIND REVIEW lap — FALSE AXIOM caught & removed):** verified the headline
  `davies_kakeya_2d` is genuinely axiom-clean & faithful (re-ran `#print axioms`; defs match
  `formal-conjectures` verbatim). Then attacked the last lane axiom `kakeya_subresolution_content`
  per "attempt, don't classify" — and found it is **UNSOUND**: derived `False` from it (kernel-checked),
  now preserved as the sound theorem `kakeya_subresolution_content_is_unsound`. Root cause: a
  self-authored axiom that **dropped the `hcR` hypothesis** (cR↔d link) when abstracted out of
  `caseA_content`, so its conclusion had to hold for arbitrary `cR>0` against a fixed finite
  `∑'ediam^d`; independently false for `d>1` (arbitrary base points ⟹ unshared fine pieces,
  `∑ediam^d→0`). Removed the false axiom; replaced its only use (Engine Case-B branch) with a disclosed
  `sorry`; updated docstrings (the `_discrete` chain now carries `sorryAx`, NOT a proof). Headline
  unaffected. `Kakeya2D/` is now axiom-declaration-free. Commit `9596dad`. **Lesson:** a cited axiom is
  honest debt; a self-authored "surely-true residual" axiom is unchecked conjecture — refute it (try to
  derive `False`) before trusting it. The prior ledger's own "honesty caveat" had smelled this.
- **2026-06-19 (DEEP-REFLECTION lap, cont. — (W) the wiring COMPLETE, axiom-clean):** after the
  synthesis below, drove the measurable-selection wiring all the way to a proof.
  `kakeya_hausdorffContentBound_of_measurableSelection` (`Wiring.lean`, `#print axioms = [propext,
  Classical.choice, Quot.sound]` — the selection is a HYPOTHESIS, NO new axioms): given a measurable
  base-point selection for any measurable cover of the Kakeya set, the Hausdorff content bound (hence
  the whole lower bound) follows with **NO Case B**. New axiom-clean bricks fed it:
  `exists_continuum_caseA_numerator` (continuum→discrete glue) + `volume_coveredFiber_subsingleton_zero`
  / `_biUnion_` (zero-`ediam` negligibility). The assembly: closed-piece reduction → cap-free dominant
  scale + base angle → genuine sub-fiber `s0` with the `dyadicIdx` window → zero-`ediam` pieces
  transported away (they carry null covered length) → `caseA_content`, with the finite/infinite split.
  **So the honest route is built end-to-end; the ONLY open input is the selection axiom (S).** The
  headline still routes through `Engine` (`kakeya_subresolution_content`) until (S) lands + the rewire.
- **2026-06-19 (DEEP-REFLECTION lap — direction confirmed, axiom honesty recalibrated, STATUS resynced):**
  altitude pass over the whole expedition. Verified the real `#print axioms davies_kakeya_2d =
  [propext, Classical.choice, Quot.sound, kakeya_subresolution_content]` (STATUS had drifted to the
  stale `kakeya_dominant_scale_count` name — fixed). **Key finding:** the live axiom is instantiated at
  `J=1` in `Engine.kakeya_hausdorffContentBound`, so Case A (`j=0`) is near-vacuous and the axiom
  carries essentially the *whole* lower bound for any realistic fine cover — the "strictly weaker
  residual" framing was over-optimistic. The discrete net route provably *cannot* escape Case B (any
  cover by sub-resolution pieces triggers it for every fixed `J`), so the only honest narrowing is the
  **measurable-selection / continuum route**, whose full spine (`measurable_coveredLength`,
  `exists_continuum_dominant_scale`, `exists_shift_ge_integral`) is already PROVEN + axiom-clean.
  **Direction call (KEEP):** continue the Córdoba route; **single highest-value next target = (W)** wire
  the spine into `kakeya_hausdorffContentBound_of_measurableSelection`, then switch the headline to a
  clean, citable **Jankov–von Neumann measurable selection** axiom (S) — a real *faithfulness* upgrade
  (murky bespoke residual → standard named theorem). Reflection + reasoning: `PENDING_WORK.md`
  §Reflection-2026-06-19.
- **2026-06-19 (retention lap — net-thinning combinatorics PROVEN + faithfulness fix found):**
  cracked the documented open core of the lone axiom. New `NetThinning.lean` (all `#print
  axioms`-clean): `sum_range_mul_eq_sum_shift` (AP decomposition of a range sum via the bijection
  `range(B·M) ≃ range B ×ˢ range M`), `exists_shift_ge` (the **shift pigeonhole** — some dyadic
  shift of the `2⁻ʲ*`-subnet retains ≥ the FULL average of the fine net's dominant-scale covered
  length, so thinning fine→coarse loses NOTHING; the earlier "diverge to 0" dead ends were artifacts
  of the unshifted/fixed net), and `one_le_tsum_volume_fiber_union` (per-scale UNION measures total
  `≥` the full union — the genuine covered length, not the overcounted `∑vol`). The whole
  circularity is now mathematically resolved (fine net → global dominant scale → shift → `2⁻ʲ*`-net,
  bricks all proven); two crisp residuals left: (R2) base-angle generalize the Córdoba chain (or
  rotate), (R1) Case B (cover dominated by sub-resolution pieces). **Faithfulness finding:** the
  cited axiom asserts the UNSHIFTED grid is well-covered (truth uncertain — adversary may concentrate
  off-grid); the shift average proves the SHIFTED-net form, which is the genuinely-true statement —
  queued to restate the axiom accordingly. Details + next-lap plan: `PENDING_WORK.md` §A0′.
- **2026-06-19 (crux-narrowing lap — whole theorem reduced to ONE axiom):** the monolithic `sorry`
  in `kakeya_hausdorffContentBound` is GONE; the entire lower bound is machine-checked down to the
  single combinatorial axiom `kakeya_dominant_scale_count`. New axiom-clean bricks:
  `cover_content_per_scale` (Córdoba count ⟹ content contribution), `exists_const_mul_pow_le` /
  `exists_pos_le_pow_div` (exponential beats fixed poly, root-free), `content_ratio_lower` (the
  assembled exponential-beats-poly content constant). `davies_kakeya_2d` `#print axioms` =
  `[propext, Classical.choice, Quot.sound, kakeya_dominant_scale_count]` — no `sorryAx`.
- **2026-06-19 (review lap — Kakeya K5 measure-free route + 4 axiom-clean bricks):**
  reframed the crux. Engine no longer reduces to "construct a Frostman measure"
  (which forces a weak-* limit mathlib lacks) but to a **Hausdorff content bound**
  `kakeya_hausdorffContentBound` — the honest, mathlib-native form. New `Cover.lean`,
  all `#print axioms`-clean: `hausdorffMeasure_ne_zero_of_content_bound` (+`_diam`/`_contentBound`)
  turning a uniform cover lower bound into `μH[d]S≠0` via `hausdorffMeasure_apply`;
  `thickening_subset_iUnion_thickening` + `volume_thickening_le_tsum` (a cover of `S`
  thickens to a cover of `Sδ`, the strict slack `δ<δ'` dissolving the closed-thickening
  inf boundary); `volume_thickening_le_of_ediam_le` (per-piece area `≤π(ρ+δ')²`);
  `exists_index_ge_of_tsum_lt` (weighted pigeonhole). `davies_kakeya_2d` axioms =
  `[propext, sorryAx, Classical.choice, Quot.sound]` (single `sorryAx`, now pinned to
  the multi-scale Córdoba content bound). Also built (all axiom-clean): the K4 `L²`
  refactor `volume_thickening_tubes_ge` (explicit family in any container `E`), the
  fractional tube area bound `TubeFractional.volume_tube_ge_frac` (`≥2δ‖v‖`), and the
  per-direction length bound `one_le_tsum_ediam_of_covers` (`∑ediam ≥ 1` from a covered
  segment) — which composes the whole stack to an **axiom-clean `hausdorffMeasure_one_ne_zero`
  (`μH[1]S≠0`, NO sorry)**, certifying the K5 reduction/geometry pipeline. Remaining: the
  `d>1` upgrade = dyadic refinement + double pigeonhole + localized count (multi-lap;
  `PENDING_WORK.md` §A).
- **2026-06-19 (Goodstein — PROVED, axiom-clean):** `goodstein_terminates`
  (`∀ m, ∃ N, goodsteinSeq m N = 0`) is fully machine-checked,
  `#print axioms = [propext, Classical.choice, Quot.sound]`. `Defs.lean` carries
  the faithful hereditary-base **bump** (peel the top power: `e=log b n`,
  `c=n/b^e`, `r=n%b^e`, `bump b n = c·(b+1)^(bump b e) + bump b r`); the 14
  `Anchors` trajectories (`m=0..3`, incl. `goodsteinSeq 3 3 = 2`) are discharged
  by `native_decide`, and `bump 2 266 = 3^81+81+3` was checked. `Engine.lean`:
  `toOrdinal` (read `n` in hereditary base `b`, replace `b` by `ω`); a single
  combined strong induction `toOrdinal_mono_and_bound` (strict monotonicity +
  the CNF leading bound `toOrdinal b n < ω^(toOrdinal b (log b n)+1)`, which are
  mutually recursive) and its ℕ twin `bump_mono_and_bound`; the structural heart
  `toOrdinal_bump : toOrdinal (b+1) (bump b n) = toOrdinal b n` (base-bump leaves
  the ordinal fixed, via base-`(b+1)` digit extraction); then `seqOrd_step` (each
  nonzero step strictly drops `seqOrd m k := toOrdinal (k+2) (G k)`) and a
  well-foundedness (`Ordinal.lt_wf.has_min`) finish. Kirby–Paris PA-independence
  stays out of scope (README documents it). The bounded Goodstein run is COMPLETE.
- **2026-06-18 (Goodstein run STARTED — directed target):** new bounded run to
  formalize **Goodstein's theorem** (`∀ m, ∃ N, goodsteinSeq m N = 0`). Scaffold in
  `Logic/Goodstein/`: faithful-def `Defs.lean` (currently a STUB), `Anchors.lean`
  (hand-computed m=0..3 trajectories, `sorry`'d anti-vacuity lock), `Statement.lean`
  headline (`sorry`). The four prior threads stay complete + axiom-clean; the
  `sorry`s here are the ONLY ones in `src/`, so `--allow-stop` is closed until the
  def is faithful, the anchors are discharged, and the headline is proved. Plan
  (ordinal descent via `Ordinal.CNF`/`wellFoundedLT`) in `DIRECTION.md`.
- **2026-06-18 (power-tower SHARP iff — COMPLETE, axiom-clean):** proved the
  divergence direction below the lower endpoint, finishing Euler's theorem to the
  sharp `iff`. New in `EngineLower.lean`: `fixedpoint_exists` (IVT fixed point `y`
  of `f t=x^t`), `log_fixedpoint_lt_neg_one` (the repelling seed: `x<e^(-e) ⟹
  log y < -1`, the genuine content of the bifurcation), `strict_two_cycle_exists`
  (the attracting 2-cycle `β₀<y<γ₀` via IVT on `g-id` both sides of `y`, using
  `g'>1` on a neighbourhood of `y`), and `tower_diverges_lower` (the even/odd
  subsequences are trapped above `γ₀` / below `β₀`, so their limits differ ⟹ no
  limit). Headline `Statement.tower_converges_iff_full` (`x>0` converges **iff**
  `x ∈ [e^(-e), e^(1/e)]`), `#print axioms`-clean. Also factored the subsequence
  construction shared by both directions into `tower_subseq_limits`.
- **2026-06-16 (π COMPLETE modulo one Aristotle fact):** the **entire** Lindemann
  π-transcendence is now machine-checked and axiom-clean, reduced to a SINGLE open input.
  `MonicRootSums.transcendental_pi_of_subsetSumEsymm : (hsse) → Transcendental ℚ Real.pi`,
  where `hsse` is exactly `subsetSum_esymm_rational` (esymm of the subset-sums of the iπ
  conjugates is rational — Aristotle job `b7252abe`, running). Full chain, all axiom-clean:
  combinatorial reduction (★) → non-monic analytic engine → `hsum` bridge → conjugate-poly
  descent (`subsetSum_poly_lifts`) → zero-root removal → clear denominators → integer `F` →
  fact (a) `sum_aeval_roots_int` (PROVEN, Aristotle `9a19f72e`) → iπ-conjugate instantiation.
  When `b7252abe` lands (kernel-verified), `hsse` is discharged, `hermite_lindemann` dies, and
  `squaring_the_circle_impossible_uncond` becomes fully axiom-clean.
- **2026-06-16 (π algebraic-part lap, cont.):** **fact (a) DISCHARGED.** `sum_aeval_roots_int`
  (monic root-sum integrality, via `roots_esymm_int` + `power_sum_int` / Newton's identities)
  proved by Aristotle (job `9a19f72e`) and **independently kernel-verified** axiom-clean in
  `MonicRootSums.lean`. Wired: `subsetSum_relation_impossible_of_conjugatePoly` drops the
  `monic_rootsum` hypothesis; `subsetSum_poly_lifts` + `esymm_aroots_mem_range` reduce fact
  (b) to a SINGLE open fact `subsetSum_esymm_rational` (esymm of subset-sums is rational —
  the symmetric-function core). That fact is now an Aristotle job (`b7252abe`, RUNNING).
  Once it lands, π-transcendence is complete and `hermite_lindemann` dies.
- **2026-06-16 (π PROVEN — axiom deleted):** the algebraic part landed.
  `SubsetSumEsymm.subsetSum_esymm_rational` (fundamental theorem of symmetric polynomials over
  the subset-sums of the `iπ` conjugates) — Aristotle `b7252abe`, **kernel-verified axiom-clean**
  (the same 4-helper decomposition was independently developed locally this lap). Combined with
  the conjugate-machinery assembly → `transcendental_pi_axiomClean : Transcendental ℚ Real.pi`,
  axiom-clean. `squaring_the_circle_impossible_uncond` rewired to it; the `hermite_lindemann`
  axiom (and its dependent theorem) **deleted**. Repo now carries **0 math axioms**.
- **2026-06-16 (π algebraic-part lap):** drove the `hermite_lindemann`-at-π crux hard. New
  file `PiLindemann.lean`, **all axiom-clean**, reduces π-transcendence to exactly two named
  facts: (a) the monic root-sum integrality `sum_aeval_roots_int` (Aristotle job `9a19f72e`),
  (b) the symmetric-function construction of the integer conjugate polynomial. Everything
  else is machine-checked: `prod_one_add_exp_eq_sum_subsetSum` + `pi_exp_relation` (★) (the
  combinatorial reduction `e^{iπ}=−1 ⟹ K + ∑_{σ_t≠0} e^{σ_t}=0`); `no_intPoly_exp_relation`
  (the **general non-monic analytic engine** — the full integer-`N`/mod-`p` assembly over an
  arbitrary `F.aroots`, generalizing the `e` proof); `aroots_integralNormalization` +
  `hsum_of_monic_rootsum` (discharge `hsum` for **every** integer `F` from the monic case via
  `integralNormalization`/`scaleRoots`); and the capstone `subsetSum_relation_impossible`
  (assembles all three — the precise remaining frontier). The **entire analytic part of
  Hermite–Lindemann at π is now done**; only the algebraic conjugate-polynomial construction
  (the "algebraic part" PR #28013 supplies) remains.
- **2026-06-16 (review lap):** π-transcendence narrowing shipped: stated **Hermite–Lindemann** (nonzero algebraic α ⟹ `exp α` transcendental) as ONE disclosed `axiom`, machine-checked `Transcendental ℚ π` from it (Euler `exp(iπ) = -1`) → `squaring_the_circle_impossible_uncond`. Then **PROVED transcendence of `e`** end-to-end (`ETranscendental.lean`): algebraic reduction + analytic decay/prime-selection + Hermite-polynomial roots + the full integer-`N`/mod-`p` assembly of `exp_polynomial_approx`. `e_transcendental` is `#print axioms`-clean — the α=1 instance of the cited axiom discharged. New dir `NumberTheory/Transcendence/`.
- **2026-06-15 / 06-14 (older milestones, trimmed):** Constructible/Wantzel iff + 5 impossibilities
  COMPLETE axiom-clean; power-tower convergence on `[e^-e, e^1/e]`; Curtis crux `substCurve_eq_zero`
  closed (repo sorry-free + axiom-clean). See git history for detail.

## Outstanding
All six headlines (Curtis, power-tower sharp `iff`, Wantzel, e-/π-transcendence, squaring-the-circle,
AND Kakeya `davies_kakeya_2d`) are **COMPLETE and axiom-clean**. The headline target of this expedition
is achieved. Remaining work is cleanup of off-headline legacy structure + out-of-lane threads.
### Short-term
- ✅ **Headline DONE & axiom-clean** — `davies_kakeya_2d` via the elementary open-cover selection route.
- ✅ **Last lane axiom REMOVED** — `kakeya_subresolution_content` found unsound & deleted; kernel-checked
  refutation `kakeya_subresolution_content_is_unsound` kept as a permanent guard.
- **(optional) Legacy Case-B `sorry`** in `Engine.kakeya_hausdorffContentBound`: the discrete route's
  genuine sub-resolution gap. It is **redundant** (the elementary headline route already proves the same
  `HausdorffContentBound` soundly) and cannot be closed by the discrete approach (the abstract Case-B
  statement is FALSE). Options: leave as honest disclosed gap (current); or have the `_discrete` chain
  delegate to the sound elementary route (needs moving those lemmas above `Selection` in the import DAG);
  or remove the redundant `_discrete` chain (a Trevor call — "never delete structure"). Low value: it is
  off every headline.
- **(hygiene) Stale docstring refs** to `kakeya_subresolution_content` / `kakeya_measurable_selection` /
  `kakeya_borel_selection` in `Wiring.lean`, `MeasurableRoute.lean`, `Cover.lean`, `CASE_B_ANALYSIS.md`
  now describe removed/superseded objects; harmless (docstrings) but worth a cleanup pass.
### Long-term
- General Hermite–Lindemann for arbitrary algebraic α (e.g. `log 2`, `cos 1`) — bounded extension.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
- `Logic/FastGrowing/Basic.lean : fastGrowing_fundSeq_step` — a dormant disclosed `sorry` (limit-step
  index monotonicity of the fast-growing hierarchy), a separate thread, out of the Kakeya lane.
### To completion
- Curtis ✅ · Power-tower SHARP iff ✅ · Wantzel iff ✅ · e-transcendence ✅ · π-transcendence ✅ ·
  squaring-the-circle ✅ · **Kakeya (Davies) ✅** (`davies_kakeya_2d`, axiom-clean via the elementary
  open-cover selection route). Repo math-axiom count: **0**; no axiom under any headline. Remaining =
  off-headline cleanup (legacy discrete Case-B `sorry`, redundant) + 1 dormant out-of-lane `sorry`
  (FastGrowing).

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Curtis.no_polynomial_relation` | Curtis 1990, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `PowerTower.tower_converges_iff_full` | converges **iff** `x ∈ [e^-e, e^1/e]` (sharp), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.isConstructible_iff_constructiblePoint` | Wantzel iff, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.cbrt2_not_constructible` (+ trisection/nonagon/heptagon) | classical impossibilities, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.squaring_the_circle_impossible` | impossibility, **cond.** on `Transcendental ℚ π` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms (hypothesis explicit) |
| `Constructible.squaring_the_circle_impossible_uncond` | impossibility, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **axiom-clean** (uses `transcendental_pi_axiomClean`) |
| `Transcendence.transcendental_pi_axiomClean` | `π` transcendental (Lindemann 1882), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **fully proved (axiom deleted)** |
| `Transcendence.e_transcendental` (+ `transcendental_exp_{nat,int,rat}`) | `e`, `eⁿ`, `eᵃ`, `e^q` transcendental (Hermite 1873; rational-exponent Hermite–Lindemann), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Kakeya2D.davies_kakeya_2d` | planar Kakeya = `dimH S = 2` (Davies 1971), uncond. | `[propext, Classical.choice, Quot.sound]` (re-verified this lap) | ✅ **0 math axioms** — complete kernel proof, no `sorryAx`. Routes through the elementary open-cover selection (`kakeya_hausdorffContentBound_elementary`, `Selection.lean`). The legacy discrete route's "Case-B residual" axiom `kakeya_subresolution_content` was found **FALSE** this lap (kernel-checked refutation `kakeya_subresolution_content_is_unsound`) and **removed**; it only ever fed redundant off-headline `_discrete` lemmas, never this headline. |

**Math-axiom count: 0** — every headline (Curtis, power-tower, Wantzel, e/π, squaring-the-circle, AND
now Kakeya `davies_kakeya_2d`) is the bare trust base `[propext, Classical.choice, Quot.sound]`. The
former lone Kakeya axiom `kakeya_subresolution_content` was discovered **unsound** this lap and removed
(see What's-happened). **Two disclosed `sorry`s** remain, both OFF every headline:
(1) `Engine.kakeya_hausdorffContentBound` Case-B branch — the legacy discrete route's genuine
sub-resolution gap; redundant (the elementary headline route proves the same result soundly), kept only
as proven Case-A structure; (2) `FastGrowing.fastGrowing_fundSeq_step` — dormant, out of the Kakeya
lane. No 🟠/🔴 axioms anywhere; no axiom under any headline.

## Pointers
- Open items / attack paths: **`PENDING_WORK.md`** (§A0‴ = measurable-route milestone + §Reflection-2026-06-19) ·
  crux analysis: `Kakeya2D/CASE_B_ANALYSIS.md` · resume baton: newest **`HANDOFF-*.md`** ·
  online asks: `ON-LINE-REQUEST.md` UPDATE 5 · frozen plan: `Kakeya2D/PLAN.md`
- Active frontier files: `GeometricMeasureTheory/Kakeya2D/MeasurableRoute.lean` (the proven spine) +
  `NetThinning.lean` (`caseA_content`) + `Engine.lean` (the axiom + assembly template for (W)).

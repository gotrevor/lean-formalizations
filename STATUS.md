# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8295 jobs) · **Updated**: lap 2026-06-19 (review) · `aa43f7e` · **0 custom axioms; 2 disclosed `sorry` (Kakeya crux + dormant FastGrowing)**

> ♾️ **ACTIVE EXPEDITION — branch `kakeya-davies` (2026-06-19): planar Kakeya conjecture
> (Davies 1971).** Read `DIRECTION.md`. Target `davies_kakeya_2d : KakeyaSetConjectureDim 2`
> (`GeometricMeasureTheory/Kakeya2D/`). Upper bound `dimH_le_two` done; the job is the lower
> bound `two_le_dimH`, reduced (K1) to `μH[d] S≠0` for all `d<2`.
> **Progress: K1–K4 COMPLETE + axiom-clean — the whole Córdoba `L²` ladder: K2 (`Tube.lean`,
> two-tube overlap `≤12δ²/(s+δ)`), K3 (`Discretize`/`Directions`, δ-net of tubes in `Sδ`), K4
> (`Cordoba`/`CordobaL2`, the content bound `volume_thickening_log_ge`: `vol(Sδ) ≳ 1/log(1/δ)`).
> K5 SWITCHED to the measure-free cover route (`Cover.lean`): the reduction `HausdorffContentBound
> ⟹ μH[d]S≠0` (via `hausdorffMeasure_apply`), the covering geometry `vol(Sδ)≤∑vol((Uₙ)δ')`, the
> per-piece area bound, and a weighted pigeonhole — all PROVEN + axiom-clean.** The lone Kakeya
> `sorry` is now `Engine.kakeya_hausdorffContentBound` = the **multi-scale Córdoba content bound**
> (an arbitrary cover ⟹ `∑ediam^d ≳ 1`); attack plan in `PENDING_WORK.md` §A. The threads below
> are COMPLETE/axiom-clean and frozen — do not touch them. (`Logic/FastGrowing/Basic.lean` carries
> one dormant disclosed `sorry`, a separate fast-growing-hierarchy thread, out of the Kakeya lane.)

## Where it stands
The repo is **100% axiom-free** — every headline `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]`, and `grep '^axiom' src/` is empty. Three independent threads, all green and `src/` **sorry-free**. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
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
- **2026-06-15 2358/2343:** Constructible/Wantzel thread COMPLETE — full equivalence `isConstructible_iff_constructiblePoint` both directions (forward = degree obstruction; converse = explicit compass arithmetic). 5 impossibilities (cube, trisection, nonagon, heptagon, + geometric-point versions), pentagon positive. All axiom-clean.
- **2026-06-15:** Constructible Layer 1 (algebraic degree engine `IsSqrtTower.finrank_eq_pow_two`) + 3 classical impossibilities; Layer 2 geometric faithfulness bridge.
- **2026-06-14 (operator redirect):** Curtis verification-hardening run (n=2 boundary / Sylvester hypersurface, extra Frobenius anchors, refuted-candidate witness, findings doc) — complete, self-stopped.
- **2026-06-14:** Power-tower convergence on the full Euler interval `[e^(-e), e^(1/e)]` proved + axiom-clean; lower-bound crux `two_cycle_collapse` via slope/Banach (not the invalid tangent-subtraction sketch). Sharp-iff lower direction (`0<x<e^(-e)` diverges) omitted, no sorry.
- **2026-06-14 1511 & earlier:** Curtis crux `substCurve_eq_zero` closed (reformulation bypassing Lemma 1); repo sorry-free + axiom-clean. Engine, Step B, Lemma 2 (Brauer–Shockley, via Aristotle, verified) built.

## Outstanding
The five complete threads (Curtis, power-tower sharp `iff`, Wantzel, e-/π-transcendence,
squaring-the-circle) are **COMPLETE and axiom-free** and frozen. The active work is the Kakeya
expedition.
### Short-term (mirror PENDING_WORK §A top)
- **`Engine.kakeya_hausdorffContentBound`** — the planar-Kakeya **multi-scale Córdoba content
  bound** (`∀ 0<d<2`, arbitrary fine cover ⟹ `∑ediam^d ≳ 1`). The K5 measure-free reduction +
  covering geometry feed it; remaining = the dyadic double-pigeonhole + a localized Córdoba count.
### Long-term
- General Hermite–Lindemann for arbitrary algebraic α (e.g. `log 2`, `cos 1`) — bounded extension.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
- `Logic/FastGrowing/Basic.lean : fastGrowing_fundSeq_step` — a dormant disclosed `sorry` (limit-step
  index monotonicity of the fast-growing hierarchy), a separate thread, out of the Kakeya lane.
### To completion
- Curtis ✅ · Power-tower SHARP iff ✅ · Wantzel iff ✅ · e-transcendence ✅ · π-transcendence ✅ ·
  squaring-the-circle ✅. **Kakeya (Davies):** K1–K4 ✅ + K5 reduction/geometry ✅; crux
  `kakeya_hausdorffContentBound` open (1 `sorry`). Repo custom-axiom count: **0**.

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
| `Kakeya2D.davies_kakeya_2d` | planar Kakeya = `dimH S = 2` (Davies 1971), uncond. | `[propext, sorryAx, Classical.choice, Quot.sound]` | 🚧 **1 disclosed `sorry`** = `kakeya_hausdorffContentBound` (the multi-scale Córdoba content bound). K1–K4 + K5 reduction/geometry all axiom-clean; no custom axiom smuggled — the crux is an open `sorry`, not an axiom. |

**Custom-axiom count: 0** across the whole repo (`grep '^axiom' src/` is empty); every *complete*
headline's `#print axioms` is the bare trust base. **Two disclosed `sorry`s remain**, both honest
checkpoints (never faked, never an axiom stand-in): the active Kakeya crux
`Engine.kakeya_hausdorffContentBound` (`davies_kakeya_2d`'s single `sorryAx`), and the dormant
`FastGrowing.fastGrowing_fundSeq_step`. No 🟡/🟠/🔴 math axioms anywhere.

## Pointers
- Open items / attack paths: **`PENDING_WORK.md`** (§A = Kakeya K5) · resume baton: newest
  **`HANDOFF-*.md`** · online asks: `ON-LINE-REQUEST.md` · frozen plan: `Kakeya2D/PLAN.md`
- Active frontier file: `GeometricMeasureTheory/Kakeya2D/Cover.lean` (K5 cover route) + `Engine.lean`

# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8285 jobs) · **Updated**: lap N+1 · 2026-06-19 · `5bb249e` · **Branch `ntl-hjsw`** · **Active frontier: HJSW `3N/2` (`hjsw_lower`, 1 disclosed sorry — the covering count)**

> **Branch note.** On `ntl-hjsw` the five umbrella threads below stay complete & axiom-clean
> (unchanged). The one open item is the **no-three-in-line HJSW lower bound** `hjsw_lower`, a
> deliberately-disclosed `sorry` (gate is armed); its proven scaffolding + the new reduction toolkit
> are axiom-clean, and `3(p−1)` is native_decide-witnessed at p=5,7,11,13 (off-headline anchors).

## Where it stands
The repo is **100% axiom-free** — every headline `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]`, and `grep '^axiom' src/` is empty. Three independent threads, all green and `src/` **sorry-free**. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
- **2026-06-19 (HJSW reduction toolkit + obstruction theory):** the geometric half of the HJSW
  covering count is now formalized & axiom-clean in `NoThreeInLine/Hyperbola.lean`:
  `collinear_imp_modp_det_zero` (construction-agnostic: real-collinear ⇒ residues' det = 0 in
  `ZMod p`), `hyperbola_collinear_zmod` (mod-`p` Vandermonde core over the field),
  `hyperbola_lift_collinear_share_residue` (real-collinear triple of hyperbola-lifts ⇒ two share a
  residue = two lifts of one base point), `coord_diff_of_residue_eq` (same-residue lifts differ by
  `0`/`p`). This reduces no-three-in-line of any lift-union to a slope-`±1` *combinatorial*
  condition. NEW structural result (proven + verified): **uniform 3-of-4 lifts of one hyperbola hit
  `3(p−1)` iff `p=5`** (each base point is over-constrained by its slope-`±1` collision partners
  except at involution fixed points); a probe confirms no single structured base (hyperbola,
  rotated hyperbola, circle, monomial graph, parabola) reaches the count at `p=7`. ⇒ the actual
  HJSW construction needs the paper (sharpened `ON-LINE-REQUEST.md`); the geometry is discharged.
  **Breakthrough (same lap):** overturned the prior "need ≥2 curves" belief — a fresh scan found a
  *uniformly-defined* single base of size `|B|=p` that works: the **sheared hyperbola**
  `y·(2x+1) ≡ 1 (mod p)` (pole→0), whose `4p` lifts contain a `3(p−1)`-point no-3-collinear set,
  **verified at p=7,11,13** (the plain hyperbola `|B|=p−1` caps at 17 by over-constraint; the shear
  relieves it). Remaining: a closed-form lift-selection rule (non-uniform) + the general proof
  (Path B in `PENDING_WORK.md`). Self-contained HJSW also submitted to Aristotle (`083292d5`).
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

## Outstanding
The transcendence / squaring-the-circle thread AND the power-tower sharp `iff` are
**COMPLETE and axiom-free**. The active frontier on this branch is the HJSW lower bound:
### Short-term (mirror `PENDING_WORK.md` top)
- **`hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2*p)`** — the only open `sorry`. Geometric reduction
  done (toolkit above); blocker is the explicit HJSW construction (filed `ON-LINE-REQUEST.md`).
  Act on `ON-LINE-FINDINGS-*.md` when it lands; else execute Path B (slope-`±1` collision-graph CSP).
### Long-term
- General Hermite–Lindemann for arbitrary algebraic α (e.g. `log 2`, `cos 1`): the π assembly
  generalizes (its `no_intPoly_exp_relation` + symmetric-function descent are α-agnostic); a
  bounded extension, not required for any current headline.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
### To completion
- Curtis ✅ · **Power-tower SHARP iff ✅** · Wantzel iff ✅ · **e-transcendence ✅** ·
  **π-transcendence ✅ (axiom-clean)** · **squaring-the-circle ✅ (unconditional, axiom-clean)** ·
  **no-three-in-line: 2N upper + Erdős Θ(N) ✅ axiom-clean; HJSW `3N/2` ⏳ (covering count open).**
  Umbrella math-axiom count: **0**; the only open obligation is `hjsw_lower` (disclosed `sorry`).

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
| `NoThreeInLine.maxNoThreeInLine_upper` / `..._order` | 2N upper + Erdős Θ(N) lower, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `NoThreeInLine.hyperbola_noThreeCollinear` + reduction toolkit (`collinear_imp_modp_det_zero`, `hyperbola_collinear_zmod`, `hyperbola_lift_collinear_share_residue`, `coord_diff_of_residue_eq`) | arc + lift geometry for HJSW, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `NoThreeInLine.hjsw_lower` | HJSW `3N/2` (1975), uncond. | **`sorryAx`** (disclosed) | ⏳ OPEN — covering count; geometry reduced, construction network-gated. `3(p−1)` native_decide-witnessed at p=5,7,11,13 (off-headline `ax_*` artifacts only). |

**Umbrella math-axiom count (🟢+🟡+🟠): 0** across the five completed threads. **HJSW frontier:** `hjsw_lower` carries a single **disclosed `sorry`** (NOT a math axiom — it is honest open work, the gate is armed). It is 🟡-grade debt: *proven* mathematics (HJSW 1975) whose covering-count construction is not yet in hand here; the geometric reduction is formalized & axiom-clean, the next prerequisite = the paper's explicit point set (`ON-LINE-REQUEST.md`). No 🔴 anywhere (no unconditional headline depends on an open conjecture).

## Pointers
- Open items / attack paths: **`PENDING_WORK.md`** · resume baton: newest **`HANDOFF-*.md`** · online asks: `ON-LINE-REQUEST.md` · frozen plan: `NoThreeInLine/PLAN.md`
- Active frontier files: `Combinatorics/NoThreeInLine/{Hyperbola,Anchors}.lean`

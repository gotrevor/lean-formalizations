# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8287 jobs) · **Updated**: lap 2026-06-19-2300 · `977598b` · **MATH AXIOMS: 0**

> ♾️ **ACTIVE EXPEDITION (2026-06-19): Goodstein-independence growth theory.** Read
> `DIRECTION.md`. Unbounded run building the mathlib-only "Goodstein grows like `f_{ε₀}`"
> content of Kirby–Paris: growth theory of `ONote.fastGrowing`, the Hardy hierarchy, and
> `goodsteinLength` → `fastGrowingε₀`. **Section A (growth theory of `fastGrowing`) is now
> COMPLETE and axiom-clean — A1/A2/A3/A4 all proved**, incl. the headline domination crux
> `fastGrowing_lt_fastGrowingε₀` (every fixed `f_o` is eventually `< f_{ε₀}`). Modules
> `Logic/FastGrowing/{Basic,Hardy,Domination}.lean` are **`sorry`-free**. Next frontier:
> **C2/C3** (the `goodsteinLength` ↔ hierarchy bridge — the crown jewel) and the Hardy `B`
> ladder. The five threads below are COMPLETE/axiom-clean and frozen — don't touch them.

## Where it stands
The repo is **100% axiom-free** — every headline `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]`, and `grep '^axiom' src/` is empty. Three independent threads, all green and `src/` **sorry-free**. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
- **2026-06-19 lap 2 (A4 CLOSED — the headline growth crux, axiom-clean):** proved
  `fastGrowing_lt_fastGrowingε₀` (`∀ NF o, ∃ N, ∀ n ≥ N, f_o(n) < f_{ε₀}(n)`) — the
  unboundedness that *is* the Kirby–Paris growth gap. The lone `Domination.lean` sorry is
  gone. New engine in `Logic/FastGrowing/Domination.lean`: the **CNF `norm`** + the genuinely
  new theorem `lt_fundamentalSequence_of_norm_le` (for a limit `β` and `α<β` with `norm α ≤ x`,
  already `α < g_β(x)` — proved by structural induction over all 6 `fundamentalSequence`
  branches, with helpers `lt_oadd_cases` / `lt_oadd_of_lead_le`); **`reaches_of_lt`** (general
  `α<β ⟹ Reaches x β α`, WF recursion on `β`); the notation-successor `osucc` + 4 lemmas for
  the strict step (`fastGrowing_lt_succ_index`). Also added **general index monotonicity**
  `fastGrowing_le_of_lt` + Hardy twin `hardy_le_of_lt` (full A3, off the consecutive-index
  restriction). Every new headline `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
  The ON-LINE-REQUEST "fast-growing domination norm" ask was **resolved by independent
  derivation** (the `norm` above) — no external literature needed; request removed.
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
- **2026-06-14 & earlier:** Curtis (no-Frobenius-formula) thread + power-tower convergence on
  `[e^(-e), e^(1/e)]` proved axiom-clean; Curtis crux `substCurve_eq_zero`, Lemma 2
  (Brauer–Shockley, Aristotle-verified). Foundational, frozen.

## Outstanding
The five completed threads (transcendence/squaring-the-circle, power-tower sharp `iff`,
Wantzel, Curtis, Goodstein termination) are **COMPLETE and axiom-free**. The ACTIVE
expedition is the growth theory; **Section A is now done**. Remaining:
### Short-term (mirror PENDING_WORK top)
- **C2 — the semantic bridge** (the crown-jewel prerequisite): relate `Engine.toOrdinal` /
  `Engine.seqOrd` (Goodstein term → `Ordinal < ε₀`, already the termination descent) to
  `ONote.repr`, so the Goodstein descent is expressed on `ONote`. Then **C3** (`goodsteinLength`
  eventually tracks `fastGrowingε₀`) = C2 + A4 (now available). This is the formal
  "Goodstein grows too fast for PA".
- **B ladder (Hardy):** B2 characterization lemmas are present; B3 anchors done. **B4**
  (`H_{ω^α}=f_α`) is a long-horizon trap under mathlib's `ω[n]=n+1` (measured: not a constant
  shift) — needs a reformulated statement.
### Long-term
- General Hermite–Lindemann for arbitrary algebraic α — bounded extension of the π assembly.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
### To completion
- Curtis ✅ · Power-tower SHARP iff ✅ · Wantzel iff ✅ · e/π-transcendence ✅ ·
  squaring-the-circle ✅ · Goodstein termination ✅ · **fast-growing growth theory A1–A4 ✅**.
  Repo math-axiom count: **0**. Crown jewel C3 (growth bridge) outstanding.

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `FastGrowing.fastGrowing_lt_fastGrowingε₀` | `f_{ε₀}` dominates every fixed `f_o` (A4; Kirby–Paris growth gap), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **A4 closed this lap** |
| `Logic.Goodstein.goodstein_terminates` | Goodstein's theorem (termination), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Curtis.no_polynomial_relation` | Curtis 1990, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `PowerTower.tower_converges_iff_full` | converges **iff** `x ∈ [e^-e, e^1/e]` (sharp), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.isConstructible_iff_constructiblePoint` | Wantzel iff, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.cbrt2_not_constructible` (+ trisection/nonagon/heptagon) | classical impossibilities, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.squaring_the_circle_impossible` | impossibility, **cond.** on `Transcendental ℚ π` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms (hypothesis explicit) |
| `Constructible.squaring_the_circle_impossible_uncond` | impossibility, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **axiom-clean** (uses `transcendental_pi_axiomClean`) |
| `Transcendence.transcendental_pi_axiomClean` | `π` transcendental (Lindemann 1882), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **fully proved (axiom deleted)** |
| `Transcendence.e_transcendental` (+ `transcendental_exp_{nat,int,rat}`) | `e`, `eⁿ`, `eᵃ`, `e^q` transcendental (Hermite 1873; rational-exponent Hermite–Lindemann), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |

**Math-axiom count (🟢+🟡+🟠): 0.** The repo is **fully axiom-free** — `grep '^axiom' src/` is empty, every headline `#print axioms` is the bare trust base, and there is no `sorry` in `src/`. The `hermite_lindemann` axiom was discharged (full Lindemann assembly for `π`) and deleted this lap. No 🟡/🟠/🔴 anywhere.

## Pointers
- Open items / attack paths: **`PENDING_WORK.md`** · resume baton: newest **`HANDOFF-*.md`** · charter: `DIRECTION.md`
- Frontier files: `Logic/FastGrowing/{Basic,Domination,Hardy}.lean` (Section A ✅ sorry-free) · `Logic/Goodstein/{Engine,Length}.lean` (C2/C3 next)
- No `ON-LINE-REQUEST.md` open (the fast-growing norm ask was self-resolved this lap).

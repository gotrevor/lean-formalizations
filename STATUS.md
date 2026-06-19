# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8286 jobs) · **Updated**: 2026-06-19 · `a18f6ff` · **Branch `ntl-hjsw`** · **All headlines axiom-clean; general-`N` constant pushed UNCONDITIONALLY Bertrand 3/4 → 15/16 → 6/5 via a refined TWO-SIDED Chebyshev stack (all axiom-clean); `nagura_prime` the lone disclosed `sorry` (now NON-blocking)**

> **Branch note.** On `ntl-hjsw` every **headline** is proven & axiom-clean (`[propext,
> Classical.choice, Quot.sound]`), kernel-verified this lap: HJSW `hjsw_lower : 3(p−1) ≤ max(2p)`
> (crux `shearSel_cross_diag` via `shear_diag_partner`/`shear_anti_partner`), the `2N` upper bound,
> Erdős `Θ(N)`, and the general-`N` `3N/4` bound (`maxNoThreeInLine_ge_three_quarters`, via Bertrand).
> The other five threads (Curtis, power-tower, constructibles, e/π-transcendence, Goodstein) are
> complete & axiom-clean.
> **NEW active frontier (this lap):** the general-`N` lower *constant* is genuine 🟡 debt — HJSW's
> theorem is `3N/2 − o(N)` for *all* large `N`, but here it is only `3/4` (Bertrand-limited). Opened
> `PrimeGap.lean`: a reusable prime-gap interface (`maxNoThreeInLine_ge_of_two_mul_prime_le`), the
> wired `5/4` payoff (`maxNoThreeInLine_ge_five_fourths`), and the crux `nagura_prime` (prime in
> `(n,6n/5]`, Nagura 1952) as a **disclosed `sorry`** — proven math, gated on a Chebyshev θ *lower*
> bound mathlib lacks. Landed the ℕ foundation toward it (`four_pow_lt_mul_lcm`, axiom-clean).
> So `src/` now carries **one** disclosed `sorry` (`nagura_prime`, the frontier — NOT a headline).

## Where it stands
**Every headline is axiom-free** — each headline `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]` (kernel-verified this lap), and `grep '^axiom' src/` is empty. `src/` now carries exactly **one disclosed `sorry`** — `nagura_prime` in `PrimeGap.lean`, the *active frontier crux* of the general-`N` HJSW constant (proven math, 🟡 debt; NOT a headline, and no headline depends on it). All six threads, green. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
- **2026-06-19 (two-sided refined-Chebyshev lap — UNCONDITIONAL constants 15/16 AND 6/5 landed):**
  Completed the refined Chebyshev program and used it to push the general-`N` no-three-in-line constant
  **unconditionally** past Bertrand's `3/4`, in two rungs, **all axiom-clean** (`[propext,
  Classical.choice, Quot.sound]`), `nagura_prime` no longer blocks any headline:
  - **`psi_refined_lower`** (`ψ(n) ≥ A·n + O(log n)`, `A=(7/15)log2+(3/10)log3+(1/6)log5 > 0.91`) — the
    refined ψ LOWER bound mathlib lacks (analytic half assembled from the per-term Stirling bounds +
    `logFactorial_leading_identity`).
  - **`theta_refined_lower`** (`θ(n) ≥ A·n − 4√n·log n − 9`) via `abs_psi_sub_theta_le_sqrt_mul_log`.
  - **`sqrt_log_small`** / **`log_le_sqrt_small`** (`√z·log z ≤ (40log2/2²⁰)z`, `log z ≤ (…)√z` for
    `z ≥ 2⁴⁰`, via `Real.log_div_sqrt_antitoneOn`) — the tiny-coefficient bounds that dominate the
    `√·log` and `log²` errors by the linear θ gap.
  - **`exists_prime_in_eight_fifths`** (prime in `(n,8n/5]`, `n ≥ 5·2³⁷`) ⇒
    **`maxNoThreeInLine_ge_fifteen_sixteenths`** (`3⌊5N/16⌋ ≤ max N`, `N ≥ 2⁴¹`): **first unconditional
    improvement on `3/4`** (constant `15/16`), using `theta_refined_lower` (lower) + mathlib
    `theta_le_log4_mul_x` (upper).
  - **THE CRUX — `psi_refined_upper`** (`ψ(n) ≤ (6/5)A·n + O(log²n)`, leading const `≈1.106 < log4`): the
    refined ψ UPPER bound mathlib lacks. Strong-induction telescoping of the 6-fold recurrence
    `psi_refined_upper_step` (`ψ(n)−ψ(⌊n/6⌋) ≤ A·n + O(log)` = `logFactorial_comb_ge_psi_sub` ∘
    `logFactorial_comb_upper`); leading term cancels exactly, error `D(n)=2(log(n+1))²+7log(n+1)+200`
    absorbs the slop via `log(⌊n/6⌋+1) ≤ log(n+1)−1`. Base `n<30` via `psi_le_const_mul_self`.
  - **`exists_prime_in_five_fourths`** (prime in `(n,5n/4]`, `n ≥ 2⁴¹`, *Nagura-strength* ratio `5/4`) ⇒
    **`maxNoThreeInLine_ge_six_fifths`** (`3⌊2N/5⌋ ≤ max N`, `N ≥ 5·2⁴⁰`): constant **`6/5`**, using the
    two-sided refined estimate (lower `θ(5n/4) ≥ A·(5n/4)`, upper `θ(n) ≤ ψ(n) ≤ (6/5)A·n`); since
    `(5/4)A > (6/5)A` the no-prime hypothesis (forcing `θ(5n/4)=θ(n)`) is contradicted.
  - **Status of `nagura_prime`** (exact `6/5`, `n≥25`): still a disclosed `sorry`, but now NON-blocking —
    the unconditional `6/5` constant is reached by the route above. Its exact `6/5` ratio (giving exactly
    `5/4`) is **unreachable from the current stack** (my method needs `c > 6/5` strictly; `(6/5)A`-upper
    forces it). Reaching exactly `5/4` (or beyond, toward `3/2`) needs sharper Chebyshev constants
    (a finer prime combination than `2,3,5,30`, pushing `A→1` / `U→A`) — a multi-lap research target.
- **2026-06-19 (refined-Chebyshev lap — the WHOLE prerequisite stack built):** Established the key
  strategic fact — **crude elementary Chebyshev bounds cannot beat Bertrand's `3/4` for ANY ratio
  `c<2`** (the central-binomial split needs `L·c > 8U/3 − 2log2`; crude `U,L` give `c>3.33`, true PNT
  `U=L=1` gives only `c>1.28`). **The ONLY route past `3/4` is a *refined* Chebyshev bound
  `ψ(x) ≳ 0.91 x`, which mathlib lacks entirely.** Built its complete prerequisite stack in
  `PrimeGap.lean`, all axiom-clean (kernel-verified), 6 commits: `sum_vonMangoldt_mul_floor_div`
  (Chebyshev's keystone `∑Λ(d)⌊n/d⌋=log(n!)`); `floor_comb_bounds` (`⌊n⌋−⌊n/2⌋−⌊n/3⌋−⌊n/5⌋+⌊n/30⌋∈{0,1}`,
  period-30); `logFactorial_div_eq_sum` + `logFactorial_comb_eq` + `logFactorial_comb_le_psi`
  (the `2,3,5,30` `T`-combination `= ∑Λ(d)g(n/d) ≤ ψ(n)` — the combinatorial half); `log_factorial_le`
  (the explicit Stirling **upper** bound on `log(m!)` mathlib lacks — companion to its lower);
  `log_three_gt`/`log_five_gt`/`chebyshev_const_gt` (numeric `log3>1.09`, `log5>1.6`, and the leading
  constant `A=(7/15)log2+(3/10)log3+(1/6)log5 > 0.91`). **Remaining: ONE focused chunk** — the
  Stirling-floor asymptotic assembling these into `ψ(n) ≥ A·n − C log n` (the `n log n`/`−n` terms
  cancel to `A·n`; floor+Stirling errors are `O(log n)`), then the dual upper iterate `ψ(n) ≲ (6/5)A·n`,
  feeding the central-binomial split for a prime in `(n,c·n]`, `c≈1.70<2`, constant `≈0.88 > 3/4`.
  `nagura_prime` stays the lone disclosed `sorry`; Aristotle `1644a603` still grinding it from scratch
  (unlikely cold — needs exactly this infra; next lap consider redirecting it to the narrowed assembly).
- **2026-06-19 (review lap — general-`N` constant frontier OPENED):** kernel-reverified all NTL
  headlines axiom-clean. Recognized the general-`N` lower *constant* (`3/4`,
  `maxNoThreeInLine_ge_three_quarters`) as genuine 🟡 debt vs. HJSW's actual `3N/2 − o(N)` for all `N`
  — gated purely on prime-gap strength. Refactored out the reusable prime-gap interface
  `maxNoThreeInLine_ge_of_two_mul_prime_le` (+ `maxNoThreeInLine_mono`), both axiom-clean. Opened
  `PrimeGap.lean`: `nagura_prime` (prime in `(n,6n/5]`, Nagura 1952) as the disclosed-`sorry` crux with
  a documented central-binomial attack; the wired `5/4` payoff `maxNoThreeInLine_ge_five_fourths`
  (`3⌊5N/12⌋ ≤ max N`, `N≥60`). **Built the Chebyshev lower-bound infrastructure mathlib lacks, from
  scratch, all axiom-clean:** `four_pow_lt_mul_lcm` (`4ⁿ<n·lcm(1..2n)`) via `centralBinom_dvd_lcm_Icc`;
  `factorization_finset_lcm` + `primePow_dvd_lcm_Icc_iff`; the von Mangoldt ↔ lcm bridge
  `log_lcm_Icc_eq_psi` (`log(lcm(1..N)) = ψ N`); and the **ψ/θ LOWER bounds** `psi_lower`
  (`n·log4 − log n < ψ(2n)`) + `theta_lower` (`θ(2n) > …`). (mathlib had only θ *upper* bounds.)
  Remaining for `nagura_prime`: the refined central-binomial argument — the crude θ constant alone
  only recovers Bertrand, so Nagura needs the `C(2n,n)` factorization split (see PENDING_WORK).
  Submitted `nagura_prime` to Aristotle (`1644a603`).
- **2026-06-19 (HJSW `3N/2` — PROVED, axiom-clean):** the crux `shearSel_cross_diag` (the lone
  remaining `sorry` — the slope-`±1` no-three condition for the closed-form sheared-hyperbola
  selection) is **discharged**, so `hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2*p)` is fully proven
  (`#print axioms = [propext, Classical.choice, Quot.sound]`). Two new partner lemmas:
  `shear_diag_partner` (slope `+1`) and `shear_anti_partner` (slope `−1`) — each factors the curve
  to a *partner relation* (`2c+2sₐ+1 ≡ 0` resp. `2sₐ ≡ 2c+1`, mod `p`) that, with the closed-form
  drop tie-break, forces any third kept lift on a kept slope-`±1` line to be its column's DROPPED
  corner. Promoted to the audit surface (`Statement.lean`: `hjsw_lower_bound`) and extended to a
  general-`N` bound `maxNoThreeInLine_ge_three_quarters` (`3·⌊N/4⌋ ≤ max N` for `N≥4`, via Bertrand)
  — lifting the Erdős Θ(N) lower constant `1/2 → 3/4`. **`src/` is now `sorry`-free.**
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
Every **headline** is COMPLETE and axiom-free. The ONE open obligation in `src/` is the active
general-`N` constant frontier (`nagura_prime`, disclosed `sorry`).
### Short-term (active frontier — mirror PENDING_WORK top)
- **`nagura_prime`** (prime in `(n,6n/5]`, `n≥25`): the crux for the `5/4` general-`N` constant.
  Proven math (Nagura 1952), 🟡 debt, gated on a Chebyshev **θ lower bound** mathlib lacks. Next
  prerequisite, well-scoped: the bridge `Real.log(lcm(1..N)) = ψ N` (via `vonMangoldt_sum`) → ψ lower
  bound (`four_pow_lt_mul_lcm` already gives the ℕ form) → θ lower (`abs_psi_sub_theta_le_sqrt_mul_log`)
  → Nagura's product bound. Aristotle job `1644a603` grinding it. Payoff `maxNoThreeInLine_ge_five_fourths`
  is wired and ready.
### Long-term
- Push the general-`N` constant `5/4 → 3/2 − o(1)` (PNT-strength prime gaps; mathlib lacks full PNT).
- General Hermite–Lindemann for arbitrary algebraic α (π assembly generalizes) — main-branch thread.
- The no-three-in-line **Main Conjecture** (`max N ~ c·N`, `c≈1.87`) — open *mathematics*, not formalizable.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
### To completion
- Curtis ✅ · **Power-tower SHARP iff ✅** · Wantzel iff ✅ · **e-transcendence ✅** ·
  **π-transcendence ✅ (axiom-clean)** · **squaring-the-circle ✅ (unconditional, axiom-clean)** ·
  **no-three-in-line: 2N upper + Erdős Θ(N) + HJSW `3N/2` + general-`N` `3N/4` ✅ all axiom-clean;
  general-`N` `5/4` rung wired, crux `nagura_prime` open.**
  Headline math-axiom count: **0**. Open obligations in `src/`: **1** (`nagura_prime`, the frontier).

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
| `NoThreeInLine.hyperbola_noThreeCollinear` + reduction toolkit (`collinear_imp_modp_det_zero`, `hyperbola_collinear_zmod`, `*_lift_share_residue`, `shear_hyperbola_*`, `coord_diff_of_residue_eq`, `lift_triple_noncollinear`) | full lift geometry for HJSW (both cross-base & same-base), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **HJSW geometry COMPLETE** |
| `NoThreeInLine.hjsw_lower` / `hjsw_lower_bound` | HJSW `3N/2` lower bound, `3*(p−1) ≤ max(2p)`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **PROVEN** (crux `shearSel_cross_diag` via `shear_diag_partner`/`shear_anti_partner`) |
| `NoThreeInLine.maxNoThreeInLine_ge_three_quarters` | general-`N` `3·⌊N/4⌋ ≤ max N` (HJSW via Bertrand), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — lifts Θ(N) lower constant `1/2 → 3/4` |
| `NoThreeInLine.maxNoThreeInLine_ge_of_two_mul_prime_le` (+ `maxNoThreeInLine_mono`) | prime-gap interface: `p` prime, `2p≤N` ⟹ `3(p−1)≤max N`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — the plug-in point for sharper gaps |
| `NoThreeInLine.four_pow_lt_mul_lcm` (+ `centralBinom_dvd_lcm_Icc`) | ℕ Chebyshev lower bound `4ⁿ < n·lcm(1..2n)`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — mathlib-missing |
| `NoThreeInLine.{log_lcm_Icc_eq_psi, psi_lower, theta_lower}` (+ `factorization_finset_lcm`, `primePow_dvd_lcm_Icc_iff`) | Chebyshev ψ/θ **lower** bounds + von Mangoldt↔lcm bridge (`log(lcm(1..N))=ψ N`, `n·log4−log n < ψ(2n)`, θ analogue), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — the elementary θ lower bound mathlib lacks (capped at `log4/2≈0.69`); PR-worthy |
| `NoThreeInLine.{sum_vonMangoldt_mul_floor_div, floor_comb_bounds, logFactorial_comb_le_psi, log_factorial_le, chebyshev_const_gt}` (refined-Chebyshev stack) | Chebyshev's `T=log(n!)` identity, the `2,3,5,30` floor combo `∈{0,1}`, `T`-combination `≤ ψ(n)`, explicit Stirling **upper** bound on `log(m!)`, leading constant `A>0.91`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — full prerequisite stack for the refined `ψ≳0.91n` bound (only route past `3/4`); built this lap; PR-worthy |
| `NoThreeInLine.maxNoThreeInLine_ge_five_fourths` (via `nagura_prime`) | general-`N` `5/4` constant `3⌊5N/12⌋ ≤ max N`, uncond. | `[propext, **sorryAx**, Classical.choice, Quot.sound]` | 🟡 frontier — `sorryAx` via `nagura_prime` (disclosed); payoff wired, crux open |

**Headline math-axiom count (🟢+🟡+🟠): 0** across all headlines (kernel-verified this lap). **Active frontier:** `nagura_prime` is a single **disclosed `sorry`** (NOT a math axiom — honest open work; the `--allow-stop` gate is correctly armed). It is **🟡-grade debt**: *proven* mathematics (Nagura 1952), formalizable, but gated on a Chebyshev θ *lower* bound mathlib lacks (it has only θ/primorial *upper* bounds). The ℕ foundation (`four_pow_lt_mul_lcm`) is landed & axiom-clean; the next prerequisite is the bridge `log(lcm(1..N))=ψ N`. No 🔴 anywhere (no unconditional headline depends on an open conjecture; `maxNoThreeInLine_ge_five_fourths` carries `sorryAx`, not a math axiom, and is explicitly the frontier rung).

## Pointers
- Open items / attack paths: **`PENDING_WORK.md`** · resume baton: newest **`HANDOFF-*.md`** · online asks: `ON-LINE-REQUEST.md` · frozen plan: `NoThreeInLine/PLAN.md`
- Active frontier files: `Combinatorics/NoThreeInLine/{Hyperbola,Anchors}.lean`

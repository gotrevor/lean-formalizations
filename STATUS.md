# STATUS — lean-formalizations 📊
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8286 jobs, kernel-reverified) · **Updated**: reflection lap · 2026-06-19 · `4cb31c1` · **Branch `ntl-hjsw`** · **General-`N` no-three-in-line constant FRONTIER CLOSED: Bertrand 3/4 → 15/16 → 6/5 (axiom-clean) → 3/2−o(1) = HJSW optimal (via one cited PNT axiom `weakPNT`, 🟠). The original mandated target (HJSW 3N/2 axiom-clean in `Statement.lean`) is COMPLETE; the extension rests on a single clearly-cited deep axiom. `nagura_prime` lone `sorry` (non-blocking).**

> **Branch note (refreshed reflection lap, 2026-06-19).** On `ntl-hjsw` the mandated audit-surface
> headlines are proven & axiom-clean (`[propext, Classical.choice, Quot.sound]`, kernel-reverified this
> lap): HJSW `hjsw_lower_bound : 3(p−1) ≤ max(2p)` (crux `shearSel_cross_diag`), the `2N` upper bound,
> Erdős `Θ(N)`, the general-`N` `3N/4` (`maxNoThreeInLine_ge_three_quarters`, via Bertrand), AND the two
> **unconditional** improvements past Bertrand `3/4` (`maxNoThreeInLine_ge_{fifteen_sixteenths,six_fifths}`,
> via the refined two-sided Chebyshev stack). The six other threads (Curtis, power-tower, constructibles,
> e/π-transcendence, Goodstein) are complete & axiom-clean.
> **Frontier state:** the general-`N` constant ladder is **CLOSED to HJSW's optimal `3/2 − o(N)`**
> (`maxNoThreeInLine_ge_three_halves_sub`), resting on the single cited deep axiom **`weakPNT`** (the PNT,
> **🟠** — see ledger + `PENDING_WORK` `## Reflection`). `src/` carries exactly **one math axiom**
> (`weakPNT`) + **one disclosed `sorry`** (`nagura_prime`, non-blocking, superseded). The `weakPNT`-bearing
> `3/2` headline lives in `PrimeGap.lean`, NOT in the axiom-clean audit surface `Statement.lean`.

## Where it stands
**Reflection-lap call (2026-06-19): the no-three-in-line thread is at its natural, valuable endpoint.** The originally-mandated target — HJSW `3N/2` proved & axiom-clean, surfaced in `Statement.lean` — is **COMPLETE** (`hjsw_lower_bound`, kernel-clean this lap). The treadmill then *overshot* it, building the full general-`N` constant ladder up to HJSW's optimal `3/2 − o(N)` (`maxNoThreeInLine_ge_three_halves_sub`). That flagship `3/2` headline rests on **exactly one** clearly-cited deep axiom, **`weakPNT`** (the Prime Number Theorem `ψ(x) ∼ x`) — while the **audit surface** (`Statement.lean`) and **two unconditional improvements past Bertrand's `3/4`** (`maxNoThreeInLine_ge_fifteen_sixteenths`, `maxNoThreeInLine_ge_six_fifths`) are **fully axiom-clean** (re-verified by `#print axioms` this lap). `weakPNT` is **🟠** (named reason below): discharging it needs porting PNTAnd's ~4000-line Wiener–Ikehara Fourier-analytic tower — multi-month — though mathlib v4.29.1 *already* supplies the historically-hard arithmetic crux `riemannZeta_ne_zero_of_one_le_re` (ζ≠0 on `Re = 1`), so the remaining gap is *only* the tauberian bridge, which mathlib is visibly on-trajectory to land (`LSeries/PrimesInAP.lean`). This is exactly the legitimate **"one narrow cited axiom + a fully-built remainder"** endpoint. See `PENDING_WORK.md` top (`## Reflection — 2026-06-19`).

**Every other headline is axiom-free** — each headline `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]` (kernel-verified this lap across all six complete threads + the NTL audit surface + the unconditional `6/5`/`15/16` rungs), and `grep '^axiom' src/` shows only `weakPNT`. `src/` now carries exactly **one disclosed `sorry`** — `nagura_prime` in `PrimeGap.lean`, the *active frontier crux* of the general-`N` HJSW constant (proven math, 🟡 debt; NOT a headline, and no headline depends on it). All six threads, green. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
- **2026-06-19 (deep-reflection lap — direction confirmed, `weakPNT` feasibility mapped):** Stepped back
  to whole-project altitude. **Re-verified the entire axiom ledger from real `#print axioms`** (build green,
  8286 jobs): all six complete threads + the NTL audit surface (`hjsw_lower_bound`, `..._three_quarters`,
  `..._upper`) + the two unconditional improvements (`..._six_fifths`, `..._fifteen_sixteenths`) are
  `[propext, Classical.choice, Quot.sound]`; `..._three_halves_sub` carries `weakPNT`; `..._five_fourths`
  carries `sorryAx` (nagura_prime). Ledger 100% accurate. **Faithfulness re-audited:** HJSW `3(p−1)` at
  `N=2p` = `3(N−2)/2` ✓; `NoThreeCollinear` = real collinearity over distinct points ✓; the `3/2−ε` headline
  transparently discloses its PNT dependency ✓. **Direction call:** the NTL thread is at its natural valuable
  endpoint — original target COMPLETE, extension built to HJSW-optimal `3/2−o(N)` on one cited deep axiom.
  **Key feasibility finding (de-risks the only debt):** mathlib v4.29.1 *already has* `riemannZeta_ne_zero_of_one_le_re`
  (ζ≠0 on `Re=1`, the hard PNT crux); the gap to `weakPNT` is purely the **Wiener–Ikehara tauberian bridge**,
  absent from mathlib but a ~4000-line Fourier tower in PNTAnd (`Wiener.lean`+`Fourier.lean`+`SmoothExistence.lean`)
  → genuine **🟠** port, OR await mathlib (PrimesInAP shows it on-trajectory). STOP squeezing elementary
  Chebyshev constants (6/5 ceiling, diminishing returns); KEEP the clean architecture (deep axiom isolated to
  `PrimeGap.lean`, audit surface clean). Full synthesis in `PENDING_WORK.md` (`## Reflection — 2026-06-19`).
- **2026-06-19 (PNT lap — FULL HJSW `3N/2 − o(N)` general-`N` constant, frontier CLOSED):** After the
  two-sided refined Chebyshev stack hit its elementary ceiling (`5/4`; the Chebyshev ratio `6/5` is a
  hard wall), broke through to HJSW's **optimal `3/2 − o(1)`** via the Prime Number Theorem. **Key
  discovery:** `~/src/PrimeNumberTheoremAnd` proves `WeakPNT'' : ψ ~[atTop] (·)` and its `ψ` **IS
  mathlib's `Chebyshev.psi`** (proof via `psi_eq_sum_Icc`). Cited it as the single **disclosed deep
  axiom `weakPNT`** (a proven theorem behind a wall mathlib lacks). On top, all in `PrimeGap.lean`:
  `psi_pnt_bounds` (∀ε>0 eventually `(1−ε)x ≤ ψ ≤ (1+ε)x`); `sqrtlog_isLittleO` (`2√x logx = o(x)` via
  `isLittleO_log_rpow_atTop`); **`exists_prime_gap_pnt`** (a prime in `(n,cn]` for *every* `c>1`,
  eventually — shatters every elementary ratio); **`maxNoThreeInLine_ge_three_halves_sub`**
  (`∀ε>0, eventually (3/2−ε)N ≤ maxNoThreeInLine N` — HJSW's optimal constant, matching `hjsw_lower_bound`
  for all large `N`). These depend on `weakPNT` + the standard three; the elementary `6/5`/`15/16`
  headlines remain fully axiom-clean. **Only remaining debt to fully close:** discharge `weakPNT` by
  porting/depending on `PrimeNumberTheoremAnd` (toolchains `v4.29.0` vs `v4.29.1`).
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
    forces it). NB `A ≈ 0.921` and `(6/5)A ≈ 1.106` **are the classical Chebyshev constants** — the
    elementary `T`-method ceiling; ratio `6/5`, so the no-three constant caps strictly below `5/4`.
    Exact `5/4` needs Nagura's sharp finite inequality; **beyond `5/4` toward `3/2` needs PNT-strength**
    (`ψ(x)=x+o(x)`), e.g. porting `~/src/PrimeNumberTheoremAnd` — the real deep wall (see `PENDING_WORK`).
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
- **2026-06-16 (π-transcendence — PROVED end-to-end, axiom deleted; condensed from 4 laps):** the full Lindemann π-transcendence landed across four laps: combinatorial reduction (★) → general non-monic analytic engine (`no_intPoly_exp_relation`) → `hsum` bridge → conjugate-poly descent → fact (a) `sum_aeval_roots_int` (Aristotle `9a19f72e`) → algebraic part `subsetSum_esymm_rational` (Aristotle `b7252abe`, both kernel-verified axiom-clean locally). Result `transcendental_pi_axiomClean` axiom-clean; `squaring_the_circle_impossible_uncond` rewired to it; the `hermite_lindemann` axiom **deleted**.
- **2026-06-16 (review lap):** π-transcendence narrowing shipped: stated **Hermite–Lindemann** (nonzero algebraic α ⟹ `exp α` transcendental) as ONE disclosed `axiom`, machine-checked `Transcendental ℚ π` from it (Euler `exp(iπ) = -1`) → `squaring_the_circle_impossible_uncond`. Then **PROVED transcendence of `e`** end-to-end (`ETranscendental.lean`): algebraic reduction + analytic decay/prime-selection + Hermite-polynomial roots + the full integer-`N`/mod-`p` assembly of `exp_polynomial_approx`. `e_transcendental` is `#print axioms`-clean — the α=1 instance of the cited axiom discharged. New dir `NumberTheory/Transcendence/`.
- **2026-06-15 2358/2343:** Constructible/Wantzel thread COMPLETE — full equivalence `isConstructible_iff_constructiblePoint` both directions (forward = degree obstruction; converse = explicit compass arithmetic). 5 impossibilities (cube, trisection, nonagon, heptagon, + geometric-point versions), pentagon positive. All axiom-clean.

## Outstanding
The mandated NTL target and all six other threads are COMPLETE and axiom-clean. `src/` carries exactly
**one math axiom** (`weakPNT`, 🟠) and **one disclosed `sorry`** (`nagura_prime`, non-blocking).
### Short-term (active frontier — mirror PENDING_WORK top)
- **`weakPNT` (THE single open debt; 🟠).** The flagship `maxNoThreeInLine_ge_three_halves_sub`
  (HJSW-optimal `3/2 − o(N)`) is fully built on it. Discharge options, best-first: **(1)** add PNTAnd as a
  local lake dep — cheap to test, expected to fail on the mathlib-rev pin (v4.29.1 vs PNTAnd's), record the
  exact error; **(2)** await mathlib's native Wiener–Ikehara (it already has the hard crux `riemannZeta_ne_zero_of_one_le_re`;
  `LSeries/PrimesInAP.lean` shows the tauberian bridge is on-trajectory) — lowest effort, just cite when it lands;
  **(3)** port PNTAnd's ~4000-line Wiener tower (`Wiener.lean`+`Fourier.lean`+`SmoothExistence.lean`+Mathlib
  patches) onto v4.29.1 — multi-month, the genuine 🟠 build-plan.
### Long-term
- `nagura_prime` (prime in `(n,6n/5]`, `n≥25`): would raise the **unconditional** axiom-clean constant
  `6/5 → 5/4`. LOW priority — modest gain, and "unreachable from the current elementary stack" (the
  `T`-method ratio is exactly `6/5`, no slack); needs Nagura's sharper finite inequality. Fallback grind only.
- General Hermite–Lindemann for arbitrary algebraic α (π assembly generalizes) — main-branch thread.
- The no-three-in-line **Main Conjecture** (`max N ~ c·N`, `c≈1.87`) — open *mathematics*, not formalizable.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
### To completion
- Curtis ✅ · **Power-tower SHARP iff ✅** · Wantzel iff ✅ · **e-transcendence ✅** ·
  **π-transcendence ✅ (axiom-clean)** · **squaring-the-circle ✅ (unconditional, axiom-clean)** ·
  **no-three-in-line: 2N upper + Erdős Θ(N) + HJSW `3N/2` + general-`N` `3N/4` + unconditional `15/16` & `6/5`
  ✅ all axiom-clean; general-`N` `3/2 − o(N)` ✅ built, on the cited PNT axiom `weakPNT` (🟠).**
  Audit-surface + unconditional math-axiom count: **0**. Extended `3/2` headline: **1** (`weakPNT`).
  Open obligations in `src/`: 1 math axiom (`weakPNT`) + 1 disclosed `sorry` (`nagura_prime`, non-blocking).

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
| `NoThreeInLine.{maxNoThreeInLine_ge_fifteen_sixteenths, ..._ge_six_fifths}` | **UNCONDITIONAL** improvements past Bertrand `3/4`: `15/16` (`N≥2⁴¹`) and `6/5` (`N≥5·2⁴⁰`), via the refined two-sided Chebyshev stack | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **kernel-reverified this lap**; the highest *axiom-clean* general-`N` constants |
| `NoThreeInLine.maxNoThreeInLine_ge_five_fourths` (via `nagura_prime`) | general-`N` `5/4` constant `3⌊5N/12⌋ ≤ max N`, uncond. | `[propext, **sorryAx**, Classical.choice, Quot.sound]` | 🟡 frontier — `sorryAx` via `nagura_prime` (disclosed); NON-blocking, superseded by unconditional `6/5` + PNT `3/2` |
| `NoThreeInLine.maxNoThreeInLine_ge_three_halves_sub` (via `weakPNT`) | **HJSW-optimal `3/2 − o(N)`**: `∀ε>0, ∀ᶠN, (3/2−ε)N ≤ max N`, uncond. (paper's actual claim) | `[propext, Classical.choice, Quot.sound, **weakPNT**]` | **🟠 — 1 math axiom** (`weakPNT` = PNT `ψ∼x`); NOT in audit surface `Statement.lean`; built remainder fully kernel-checked |

**Math-axiom counts (🟢+🟡+🟠), kernel-verified this lap:** audit-surface NTL headlines + all six complete
threads + the unconditional `6/5`/`15/16` rungs = **0**. The single extended flagship
`maxNoThreeInLine_ge_three_halves_sub` = **1** (`weakPNT`, 🟠). **`weakPNT` (🟠, named reason):** it is the
Prime Number Theorem `ψ(x) ∼ x` — a *proven* theorem (170 yrs old; complete Lean proof in PNTAnd via
Wiener–Ikehara), but absent from mathlib and discharged only by porting a ~4000-line Fourier-analytic tower
(or awaiting mathlib's native version). Not 🔴 (it is proven, not conjectural) and not 🟡 (not chippable in
lap-sized pieces). The arithmetic crux (`riemannZeta_ne_zero_of_one_le_re`, ζ≠0 on `Re=1`) is *already* in
our mathlib pin; only the tauberian bridge is missing. **`nagura_prime`** is a separate **disclosed `sorry`**
(NOT a math axiom; non-blocking, low priority — superseded). **No 🔴 anywhere** — no headline depends on an
open conjecture; `weakPNT` is a cited *proven* theorem and is transparently disclosed, off the audit surface.

## Pointers
- Reflection synthesis + open items/attack paths: **`PENDING_WORK.md`** (top = `## Reflection — 2026-06-19`) · resume baton: newest **`HANDOFF-2026-06-19-1018.md`** · online asks: `ON-LINE-REQUEST.md` (all resolved) · frozen plan: `NoThreeInLine/PLAN.md`
- Active frontier file: `Combinatorics/NoThreeInLine/PrimeGap.lean` (the `weakPNT` axiom + the entire `3/2−o(N)` build are at its end; the `Hyperbola.lean`/`Anchors.lean` HJSW construction is complete)

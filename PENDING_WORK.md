# PENDING_WORK — no-three-in-line / HJSW frontier (branch `ntl-hjsw`)

## Reflection — 2026-06-20 (DEEP-REFLECTION lap #2, strong model @ high effort) 🧘
**The math is settled; the only open question now is a PROCESS one.** I re-derived completion from ground
truth this lap (not docs): `lake build` GREEN (8621 jobs); `#print axioms` on all 14 `.bump-axioms`
headlines = `[propext, Classical.choice, Quot.sound]` in a single real `lake env lean` pass (zero math
axioms, zero `sorryAx`, zero `native_decide` artifacts); `src/` sorry-free + axiom-decl-free (every grep-hit
is prose); flagship statement `(3/2−ε)·N ≤ maxNoThreeInLine N` faithful to HJSW `3/2−o(N)`, `NoThreeCollinear`
genuine `Collinear ℝ`. The prior DEEP-REFLECTION (#1, above) already closed the statement-faithfulness gap
and the external-dep seam — both re-confirmed, nothing reopened.

**Direction call (unchanged, and now I can say WHY at the meta level): COMPLETE — leave it stopped.** The
honest altitude finding is not about any `sorry`; it's about the *loop*. The git log shows **~15 consecutive
laps** that each (a) rebuild, (b) re-run the identical 14-headline `#print axioms`, (c) write a fresh
`HANDOFF-*.md`, (d) re-write a `mode=complete` stop sentinel, (e) self-stop — and then get relaunched by the
reflection/fresh-mind *cadence*, which fires on a schedule regardless of the (valid, present) sentinel. That
is not forward motion; it is the treadmill circling a finished project. The marginal cost of this repo is now
**the loop itself** — tokens + ~60 accreted handoff docs — not any open mathematics.

**Is there genuinely no higher-value target? Tested, not assumed.** I stress-tested the "complete" verdict
against the reflection charter's "recalibrate, don't surrender":
- *Headline walls?* None open. Not one of the 14 headlines cites any math axiom (🟡/🟠/🔴 frontier is empty).
  The flagship sits at HJSW's optimal `3/2−o(N)` — the best *known unconditional* bound; the Main Conjecture
  beyond it (`max N ~ 1.87 N`) is **open mathematics, not formalizable**. There is no headline left to chip.
- *The lone open item* (sharp `2π|u|` BV-Fourier constant, item 1) is **off-headline** (refines a bonus;
  gates nothing — proven by the clean axiom seam), and even reclassified optimistically as a multi-lap 🟡 it
  would advance **no headline**. Trevor explicitly **fenced it under FINISH-AND-STOP** (2026-06-19). Grinding
  it would be exactly the "adjacent bonus problem" side quest the directive forbids. "Recalibrate, don't
  surrender" governs *headline* walls; there are none — so there is nothing to recalibrate, only an operator
  directive to honor.

**KEEP:** the axiom-clean `.bump-axioms` discipline; the clean isolation architecture; honoring finish-and-stop.
**STOP:** the per-lap re-verification + new-handoff theatre. The footprint is stable, statements are audited,
the seam holds. A relaunch is a cadence artifact, not reopened work.
**Process recommendation to Trevor (the real course change this lap can offer — there is no math one to make):**
retire `lean-formalizations-ntl` from the active treadmill rotation, **or** make finish-and-stop sticky against
the reflection/fresh-mind cadence for a `mode=complete` repo. Until then, the correct response to each relaunch
is: re-confirm green + `src/` sorry-free (the gate needs it anyway) and stop — which is what this lap did.
**Single highest-value target IF finish-and-stop is ever lifted:** the sharp `2π|u|` constant via route (c)
(Jordan decomposition → mathlib monotone Stieltjes measures → assembled signed IBP), item 1 below.

## Reflection — 2026-06-20 (DEEP-REFLECTION lap, strong model @ high effort) 🧘
Stepped all the way back. **Direction call: the project is genuinely COMPLETE and the destination was the
right one — self-stop re-affirmed.** What makes *this* reflection lap different from the ~7 re-verification
laps before it: instead of re-running the proof-axiom footprint a 7th time (the prior handoff is right that
that "adds nothing"), I closed the *one* verification gap those laps left open.

**1. Destination — still right.** The repo is a constellation of solved-but-hard impossibility / transcendence
/ no-formula meta-theorems. The flagship (HJSW no-three-in-line ladder → `3/2 − o(N)`, unconditional &
axiom-clean) is reached; the nine supporting threads (Curtis, power-tower sharp iff, Wantzel, e/π
transcendence + squaring-the-circle, Goodstein, Mertens trilogy incl. sharp `e^{−γ}`, BV-Fourier decay,
Dirichlet divisor) are all complete & axiom-clean. No new information (no paper, no mathlib addition, no
Aristotle result) changes what the valuable endpoint is. This is a saturated endpoint, not a stalled one.

**2. Highest-value thing — there is no higher-value open target on this branch.** The only repo-connected open
item is the sharp `2π|u|` BV-Fourier constant (item 1): off-headline (gates nothing — the `prelim_decay`
sorries are dead code off `weakPNT`, *proven* below by the clean axiom seam check), needs mathlib-absent
signed-BV Lebesgue–Stieltjes IBP (🟠), and refines a *bonus*. It is strictly lower-value than the done
headlines and forbidden as a side quest under finish-and-stop. `nagura_prime` (5/4) is superseded; general
Hermite–Lindemann is a *main-branch* thread, not this branch's scope. No fixation, no easy-leaf-bagging, no
dead-end grind — there is simply nothing left of higher value than what is done.

**3. What an outside expert would scrutinize — the external-dep seam (and it holds).** The de-vendor
(`a0f17d1`) made the flagship's axiom-cleanliness contingent on `kim-em/PrimeNumberTheoremAnd@bump/v4.31.0`
rather than an in-repo tower. That is the single most load-bearing architectural fact, so I checked it from
ground truth this lap: `#print axioms weakPNT` and `#print axioms maxNoThreeInLine_ge_three_halves_sub` both
= `[propext, Classical.choice, Quot.sound]` *through the external dep* — definitive proof the dep's two
`prelim_decay` sorries are off-path (a `sorryAx` would otherwise surface). The seam is sound. (Maintenance
note for a future bump: re-pinning the dep must re-gate on this seam staying clean.)

**4. Faithfulness at altitude — the gap I closed.** `#print axioms` certifies *proofs*, never *statements* —
transcription drift is the silent failure the re-audit laps never tested. This lap ran a fresh
**statement-faithfulness audit** of all headline *signatures* against their classical claims (a fanned-out
read of every headline's type + the definitions it unfolds to). **All faithful** — e.g. `NoThreeCollinear`
is genuine `Collinear ℝ` over real-plane embeddings (every slope, the *corrected* form of the upstream
`Green72` bug), `transcendental_pi_axiomClean : Transcendental ℚ Real.pi` uses mathlib's real predicate on
the real π, `goodstein_terminates (m) : ∃ N, goodsteinSeq m N = 0` over the genuine hereditary-base-bump
sequence, `tower_converges_iff_full ... ↔ x ∈ Set.Icc eNegE eInvE` with both sharp endpoints,
`mertens_third_classical_eGamma` is `∏_{p≤N}(1−1/p)·log N → exp(−γ)` with `γ = eulerMascheroniConstant`.
No drift, no vacuity, no silently-weakened form. **This is the certification the project was missing** — it
materially strengthens the completion claim (statements + proofs both now audited), and it should NOT need
redoing unless a statement changes.

**KEEP doing:** the axiom-clean discipline (`.bump-axioms` gate); the clean architecture (deep inputs
isolated, audit surface in `Statement.lean`/`Defs.lean`); honoring finish-and-stop.
**STOP doing:** the per-lap *proof-axiom* re-audit theatre (7 laps of identical `#print axioms` on an
unchanged tree). The footprint is stable; the statements are now audited too. A relaunch is a *cadence
artifact* (reflection/fresh-mind laps fire regardless of the stop sentinel, which is already written &
valid), **not** a signal that work reopened. Correct response to a relaunch: absorb this synthesis, confirm
build green + `src/` sorry-free (the gate needs that anyway), and stop — do NOT reopen, do NOT re-pin, do
NOT manufacture a side quest.
**Single highest-value next target — ONLY if Trevor lifts finish-and-stop:** the sharp `2π|u|` constant via
**route (c)** (Jordan decomposition into two monotones → existing monotone Stieltjes measures → assembled
signed IBP), item 1 below — the pieces are confirmed present in mathlib's `BoundedVariation.lean`.

## Completion-verification review lap — 2026-06-20 (self-stop) ⛳
**Ground-truth re-audit (not docs).** `lake build` GREEN (8621 jobs). `src/` tactic-level **sorry-free**
(every `sorry` grep-hit is docstring prose; Goodstein anchors are real `native_decide`; `grep '^axiom' src/`
empty). **`#print axioms` on all 14 `.bump-axioms` headlines = `[propext, Classical.choice, Quot.sound]`**
(zero math axioms, zero `sorryAx`, zero `native_decide` artifacts, zero 🔴 — full audit output captured this
lap). The de-vendor + v4.31.0 upgrade and the BV-Fourier-decay route-(b) bonus are done and axiom-clean.

**Decision: COMPLETION EXIT (allow-stop run, `LEAN_LAP_ALLOW_STOP=1`).** The completion bar is met — zero
open `sorry`/`admit` in `src/`, every headline `#print axioms`-clean, and the frontier genuinely saturated.
The single remaining repo-connected open item, the **sharp `2π|u|` BV-Fourier constant** (item 1 below), is
**not a chippable 🟡**: it is off-headline (refines a bonus; gates no headline — the upstream `prelim_decay`
sorries are dead code off `weakPNT`), and it needs a signed-BV / Lebesgue–Stieltjes integration-by-parts
development that is **absent from mathlib** and exists only in an external library (Luccioli–Degenne, verified
online 2026-06-19) — a **🟠 generational wall** with a named missing-theory reason. This lap traced the full
sharp proof (Fubini → `1/(2πiu)∫ e(−tu) df`) and pinned the exact missing primitive (signed Stieltjes
`μ_f((a,b]) = f(b)−f(a)` for BV `f`; mathlib has it for *monotone* `f` only) — so the 🟠 call is a mapped
wall, not a timid pre-classification. Building it to sharpen an off-headline bonus would be exactly the
side quest the operator's finish-and-stop directive forbids. → **self-stop** after STATUS refresh + HANDOFF.

## Inventory + attack paths — 2026-06-20 (post-`d7699b1`, BV-decay family COMPLETE)
**State:** `src/` sorry-free; all headlines + the BV-Fourier-decay bonuses (`prelim_decay_2_route_b`,
`prelim_decay_3_route_b`) `#print axioms`-clean; full build green (8621 jobs). De-vendor + v4.31.0 upgrade
DONE. **Operator authorized stopping** the treadmill once those were done. The items below are all
**off-headline and multi-lap** — none completable in a small budget; left unopened under finish-and-stop.

**Open-item inventory (full).**
1. **Sharp constant `2π|u|`** for `prelim_decay_2/3` (we have the non-sharp `4|u|`/`8π·u²`). The blueprint's
   own route is Lebesgue–Stieltjes integration-by-parts; mathlib has only differentiable-integrand IBP +
   *monotone* `StieltjesFunction`, not general signed BV-IBP.
   - (a) Port a signed BV integration-by-parts development onto mathlib (highest effort; the real wall).
   - (b) Tighten route (b): the factor-2 slack is the half-period trick + the `|h|·V` bound; a quarter-period
     or optimized-shift variant might recover a better constant without IBP. Low payoff.
   - (c) Decompose BV `= ` difference of two monotones, apply the EXISTING monotone Stieltjes measure to
     each, and assemble — gets a genuine Stieltjes IBP for BV via two monotone ones. **Most promising
     mathlib-only route to the sharp constant. CONFIRMED mathlib has the pieces** (found 2026-06-20,
     `Topology/EMetricSpace/BoundedVariation.lean`): `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`
     (the Jordan decomposition, `f = g − h` with `g,h` monotone) and `variationOnFromTo f s a b` (the signed
     variation function, additive: `variationOnFromTo.add`, monotone in `b`). Next-lap plan: build the two
     monotone parts' `StieltjesFunction.measure`s, write `𝓕 f' = ∫ e(−tu) d(μ_g − μ_h)`, IBP to `2πiu·𝓕 f`,
     bound `|∫ d(μ_g+μ_h)| = V`. This would supersede the route-(b) `4|u|` with the sharp `2π|u|`.
2. **`nagura_prime`** (`wip/NaguraFiveFourths.lean`) — the `5/4` prime-gap rung. SUPERSEDED by the
   unconditional `3/2−o(N)`; constant has zero slack vs Chebyshev, so only Nagura 1952 / explicit-error PNT
   closes it. Lowest priority; gates no headline.
   - (a) explicit-error PNT (`|ψ(x)−x|` bound) — mathlib-absent, large. (b) Nagura's elementary interval
     argument — tedious finite casework. (c) leave superseded (current call).
3. **Upstream dep `Wiener.lean:323/342`** `prelim_decay_2/3` sorries — dead code off the WeakPNT path
   (`weakPNT` axiom-clean with them present). Can't patch (external dep, no push). Our route-(b) reconstruction
   in `BVFourierDecay.lean` is the in-repo answer; a PR to `kim-em/PrimeNumberTheoremAnd` would need a
   networked host (see `ON-LINE-REQUEST.md` pattern).

## ✅ RESOLVED 2026-06-20 (`d17e7b8`): `prelim_decay_2` route (b) — COMPLETE & axiom-clean
Route (b) below is **fully proven** and promoted to `src/LeanFormalizations/RealAnalysis/BVFourierDecay.lean`
(`prelim_decay_2_route_b : ‖𝓕 f u‖ ≤ V(f)/(4|u|)`, `[propext, Classical.choice, Quot.sound]`, build green
8621 jobs). Both cruxes closed: **(b1)** half-period shift (`exp(↑r·I)` phase + `𝐞(−½)=−1` + translation);
**(b2)** L¹-translation-by-TV via the **monotone variation function** `W(t)=V(f on (−∞,t])` — pointwise
`‖f t−f(t+h)‖≤W(t+h)−W(t)` (`add_le_union`+`edist_le`) then **elementary finite-window telescoping**
`∫_{−N}^{N}(W(·+k)−W)=∫_N^{N+k}W−∫_{−N}^{−N+k}W≤k·V` + monotone-convergence limit, **no signed
variation/Stieltjes measure** (mathlib-absent) needed. The inventory below is kept for history; items 1–3
remain off-headline. The only NOT-done remnant is the **sharp** `2π|u|` constant (route (a), needs
mathlib-absent BV integration-by-parts) — a new side quest, left unopened under finish-and-stop.

## Inventory + attack paths — 2026-06-20 (post-de-vendor, governor-driven)

**Open-item inventory (full).** `src/` is **sorry-free** and all 14 headlines `#print axioms`-clean
(verified this lap). The only genuinely-open items connected to this repo:
1. **`prelim_decay_2`** — `‖𝓕 ψ u‖ ≤ V(ψ)/(2π|u|)` for ψ integrable + BV. Still `sorry` upstream
   (PNTAnd, now our dependency `Wiener.lean:323`), absent from mathlib. Dead code on the WeakPNT path
   (clean `#print axioms weakPNT` proves it) → gates no headline, but a real open theorem behind a
   mathlib wall (Lebesgue–Stieltjes IBP / BV-translation). Parked: `wip/WienerDecayIsland.lean`.
2. **`prelim_decay_3`** — `‖𝓕 ψ u‖ ≤ V(ψ')/(2π|u|)²` (AC ψ, BV ψ'). Follows from `prelim_decay_2` by one
   more shift/IBP. Same status.
3. **`nagura_prime`** (`wip/NaguraFiveFourths.lean`) — the elementary `5/4` prime-gap rung. SUPERSEDED by
   the unconditional `3/2−o(N)`; its constant exactly equals the Chebyshev constant (zero slack), so only
   Nagura 1952 / explicit-error PNT closes it. Correctly lowest priority; not pursued.

**Three attack paths for `prelim_decay_2`** (the live hard target):
- **(a) Lebesgue–Stieltjes IBP** (the blueprint's own route, sharp `2π|u|`): `2πiu·𝓕ψ(u)=∫e(−tu)dψ(t)`,
  then `|·|≤∫dV=V`. Needs general BV integration-by-parts — NOT in mathlib (only differentiable-integrand
  IBP + monotone `StieltjesFunction`). Highest-risk; would mean porting a BV-IBP development.
- **(b) Half-period shift + L¹-translation-by-TV** (weaker `4|u|`, self-contained — PREFERRED): two
  mathlib-absent lemmas — (b1) `2·𝓕f(u)=∫(f t − f(t+1/(2u)))·e(−tu)dt` via the substitution `t↦t+1/(2u)`
  and `e(−½)=e^{−πi}=−1`, giving `‖𝓕f u‖≤½∫‖f t−f(t+1/(2u))‖dt`; (b2) `∫‖f t−f(t+h)‖dt ≤ |h|·V(f)` from
  the pointwise `‖f t−f(t+h)‖≤V_{[t,t+h]}` + Fubini over the variation measure. Combine → `≤ V/(4|u|)`.
- **(c) Reformulate / narrow** — even if (b1)/(b2) aren't fully closed, VERIFY the assembly
  (shift+translation ⟹ decay) in-kernel, reducing the one opaque `sorry` to the two precise narrower
  lemmas. The pointwise bound `‖f a−f b‖≤(eVariationOn f univ).toReal` IS mathlib-direct
  (`eVariationOn.edist_le`). ← attacking this in `wip/BVFourierDecay.lean` this lap.

**This lap:** building route (b) scaffolding in `wip/BVFourierDecay.lean` — pointwise variation bound
proven; (b1)/(b2) stated as the two disclosed sub-sorries; the assembly into the weaker `prelim_decay_2`
form verified. Keeps `src/` sorry-free (wip is outside the build).

## Reflection — 2026-06-19 (deep-reflection lap, strong model)

**Direction call: the project is COMPLETE. Execute the FINISH-AND-STOP wind-down and self-stop.**
This lap stepped to whole-project altitude (read STATUS, the newest handoffs, the git log, the
reference corpus, the unharvested findings) and re-verified ground truth rather than trusting docs.

### What I verified (not assumed)
- **All 17 headlines axiom-clean from real `#print axioms`** — every one is `[propext,
  Classical.choice, Quot.sound]` (HJSW ladder `hjsw_lower_bound` / `..._three_quarters` /
  `..._fifteen_sixteenths` / `..._six_fifths` / `..._three_halves_sub` / `..._upper`; `weakPNT`;
  the full Mertens trilogy incl. `mertens_third_classical_eGamma` and `mertensThirdConst_eq_neg_gamma`;
  e/π-transcendence; squaring-the-circle; Wantzel iff; power-tower iff; Curtis; Goodstein). Build green
  (8297 jobs). No `sorryAx`, no math axiom, no 🔴 anywhere.
- **Faithfulness re-audited** at the source: the flagship reads `∀ε>0, ∀ᶠN, (3/2−ε)N ≤ maxNoThreeInLine N`
  (HJSW's optimal `3/2 − o(N)`); the Mertens 3rd reads `∏(1−1/p)·logN → e^{−γ}`. Both say what the
  papers claim.
- **STATUS.md had internal staleness** (the "Where it stands"/"Pointers" still called Limit B an
  "active frontier" although it's PROVEN). Fixed this lap.

### The real finding: the treadmill was circling
The prior lap built→reverted a Dirichlet-divisor side-quest, then **left the three off-headline
`sorry`s in `src/`** (out of a misread "never delete structure" rule) and wrote a self-stop the
governor **DECLINED** — because the self-stop gate (`has_open_sorry`, scans `src/**.lean`) still saw
those `sorry`s. So the treadmill relaunched into this lap. The block was never mathematical; it was a
false rule-conflict. Trevor's explicit, recent FINISH-AND-STOP directive ("clear or **quarantine**
those off-headline sorries so `src/` is sorry-free") IS the standing authorization to relocate them;
git + `wip/` preserve everything, so "never delete structure" is satisfied.

### What I DID this lap
Adopted the cross-repo **`wip/` convention** (a peer session flagged ntl never had it): created `wip/`
(outside `src/` → not built, not gate-scanned) and relocated, preserving verbatim —
- `wip/NaguraFiveFourths.lean` — `nagura_prime` (parked crux) + its superseded `5/4` rung;
- `wip/WienerDecayIsland.lean` — the dead `prelim_decay_2/3` + `decay_alt` island;
- `wip/DivisorProblem.lean` — the COMPLETE, axiom-clean Dirichlet divisor proof, restored from `d356584`
  (moved to `wip/` rather than left reverted-to-git-only, per the convention).
Result: **`src/` is sorry-free** (governor detector confirms), every headline still axiom-clean, build
green. → self-stop.

### KEEP doing
- Re-verify the ledger from REAL `#print axioms` every review lap (it caught the STATUS staleness).
- Quarantine to `wip/` (not delete, not leave-in-`src/`) for protected/parked/reverted work.

### STOP doing
- Manufacturing side-quests under FINISH-AND-STOP (the divisor problem was correctly reverted).
- Deferring an operator-authorized cleanup "pending Trevor" when the directive already answers it —
  that deferral cost a full relaunch cycle.
- Calling Limit B / the Mertens thread an "active frontier" — it is COMPLETE.

### Highest-value next target — only if FINISH-AND-STOP is lifted
There is **no** on-headline target left. If the directive is lifted, in priority order:
1. Finish `wip/NaguraFiveFourths.lean`'s `nagura_prime` (Nagura's tuned finite inequality, the analogue
   of `bertrand_main_inequality` for ratio `6/5`, valid `n ≥ N₀` + `n ∈ [25, N₀)` by `decide`) → the
   axiom-clean general-`N` `5/4` rung. Note it is *superseded* by the unconditional `3/2 − o(N)`, so its
   marginal value is low — a polish item, not a frontier.
2. Restore `wip/DivisorProblem.lean` into `src/` (already complete & axiom-clean).
3. A fresh mathlib-absent classical target.
Otherwise: the deliverables (HJSW ladder + Mertens trilogy + six other threads) are done. **Self-stop.**

---

## ⭐ weakPNT DISCHARGED — 2026-06-19 (grind lap, strong model)

**The single deep axiom `weakPNT` (the Prime Number Theorem, `ψ∼x`) is now a fully machine-checked
theorem.** The flagship `maxNoThreeInLine_ge_three_halves_sub` (HJSW-optimal `3/2−o(N)`) is
**axiom-clean** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`) — UNCONDITIONAL.

**How:** ported PrimeNumberTheoremAnd's Wiener–Ikehara tower onto our mathlib `v4.29.1` with ZERO
math edits (only `Architect`/`@[blueprint]`/`blueprint_comment` stripping + import redirection). The
feared v4.29.0→v4.29.1 drift did not materialize. New modules under
`src/LeanFormalizations/NumberTheory/PrimeNumberTheorem/`: `Support`, `Sobolev`, `Fourier`,
`SmoothExistence`, `Asymptotics` (faithful Asymptotics+Log patches), `Wiener` (4118), `Defs`,
`Consequences` (full). `PrimeGap.weakPNT := Consequences.WeakPNT''`.

**Now in-repo & axiom-clean:** `WeakPNT''` (ψ∼x), `chebyshev_asymptotic` (θ∼x), `pi_alt'`
(π(x)∼x/log x — the classic PNT), `nth_prime_asymp` (pₙ∼n log n), + PNTAnd's whole consequences layer.

### Remaining open `sorry`s (the ONLY three in the repo — all OFF the flagship critical path)
1. **`Wiener.prelim_decay_2`** (`Wiener.lean:244`): `‖𝓕 ψ u‖ ≤ TV(ψ)/(2π|u|)` for integrable BV ψ.
   Verbatim upstream sorry. DEAD CODE (unused anywhere; clean `#print axioms WeakPNT''` confirms it
   gates nothing). Aristotle job `c6d615ee` was attempting it. Attack paths:
   - (a) Sharp route = Lebesgue–Stieltjes IBP: `2πiu·𝓕ψ(u) = ∫𝐞(-tu)dψ`, then `≤ ∫|dψ| = TV`. Needs
     Stieltjes-measure IBP for BV (mathlib has `StieltjesFunction`, `VectorMeasure/BoundedVariation`,
     `IntervalIntegral/IntegrationByParts` — assemble via Jordan decomposition ψ = monotone − monotone).
   - (b) Shift trick gives only the WEAKER `TV/(4|u|)` (1/4 > 1/(2π)), so it does NOT prove the stated
     constant — useful only if one weakens the (dead) statement.
   - (c) Port whatever Aristotle / a newer mathlib lands.
2. **`Wiener.prelim_decay_3`** (`Wiener.lean:252`): 2nd-order, `≤ TV(ψ')/(2π|u|)²` for AC ψ with ψ' BV.
   Used only by the dead `decay_alt`. PNTAnd note: "should follow from prelim_decay_2" via
   `𝓕(ψ')(u) = 2πiu·𝓕ψ(u)` — but mathlib's `Real.fourier_deriv` needs EVERYWHERE-differentiable, while
   the hyp is only `AbsolutelyContinuous` (a.e. diff + FTC). Attack: build FT-of-deriv for AC functions
   (IBP via `IntervalIntegral/AbsolutelyContinuousFun`), then chain prelim_decay_2.
3. **`nagura_prime`** (`PrimeGap.lean:1120`): prime in (n,6n/5] for n≥25. Superseded for the NTL
   headline by the unconditional `3/2−o(N)`, but still an independently-famous mathlib-absent theorem
   and the only explicit (effective, all-N) rung past `6/5`.
   **REFINED DIAGNOSIS (2026-06-19, DivisorProblem lap).** Nagura is **elementary** (no PNT — the prior
   "needs effective PNT" was imprecise). The repo's refined two-sided Chebyshev stack
   (`psi_refined_lower`/`psi_refined_upper`/`theta_refined_lower`) is built on the classical Sylvester–
   Chebyshev `{2,3,5,30}` function `f(n)=T(n)−T(n/2)−T(n/3)−T(n/5)+T(n/30)` (floor combo `g∈{0,1}`,
   `floor_comb_bounds`). Its leading constant is **`A=(7/15)log2+(3/10)log3+(1/6)log5 ≈ 0.9213`** (lower)
   and **`(6/5)A ≈ 1.106`** (upper) — these are *exactly Chebyshev's 1852 bounds*, ratio **exactly `6/5`**.
   So the method gives a prime in `(n,c·n]` for any `c > 6/5` (hence `exists_prime_in_five_fourths`, 5/4)
   but **provably cannot attain `c = 6/5`** (leading constants tie). This is a *soft* wall: ANY strict
   improvement to either constant breaks it — a lower bound `ψ(n) ≥ A'·n` with `A' > A`, or an upper
   `ψ(n) ≤ B'·n` with `B' < (6/5)A`, immediately yields Nagura (large-n by the gap; `n∈[25,N₀)` by
   `decide`). **Concrete next attack:** replace `{2,3,5,30}` with a sharper elementary combination
   (longer period / more primes — Diamond–Erdős / Rosser-style) whose Chebyshev constant exceeds `0.9213`.
   This re-does `floor_comb_bounds` (a `decide` over the new period), `logFactorial_comb_{lower,upper}`,
   and the telescoping — a bounded multi-lap port. (Alt: effective PNT gives ratio→1 but is heavier.)

### ✅ 2026-06-19 (review lap) — Mertens' First Theorem COMPLETE (prime form sharp + capstones)
- **`NumberTheory/PrimeNumberTheorem/Mertens.lean`** — Mertens' first theorem, **absent from mathlib**,
  fully axiom-clean (`[propext, Classical.choice, Quot.sound]`). vonMangoldt form (`c5c015a`, `7915a2f`),
  then the **prime form** discharged this lap (`8dd6b6b`, `a2b4891`):
  - `abs_vonMangoldtSumDiv_sub_log_le` : `∀ N≥1, |∑_{d≤N}Λ(d)/d − log N| ≤ log 4 + 5`.
  - `mertens_first` : `(∑_{d≤N}Λ(d)/d − log N) =O[atTop] 1`; `vonMangoldtSumDiv_tendsto_atTop`.
  - **`vonMangoldtSumDiv_sub_primeSumDiv_le`** : the proper-prime-power tail `≤ 2·∑'_b (log b)/b²`
    (the crux — bounds the `O(1)` gap between vonMangoldt and prime sums).
  - **`abs_primeSumDiv_sub_log_le`** : `∀N≥1, |∑_{p≤N}(log p)/p − log N| ≤ (log4+5) + 2∑'(log b)/b²`.
  - **`mertens_first_prime`** : `(∑_{p≤N}(log p)/p − log N) =O[atTop] 1` — the recognizable prime form.
  - `primeSumDiv_isEquivalent_log`, `vonMangoldtSumDiv_isEquivalent_log` : both sums `~ log N`.
  - **Tail-bound method (reusable):** geometric helper `∑_{k≥2}r^k ≤ 2r²` (`r≤½`); per-base
    `∑_k log p/p^k ≤ 2log p/p²`; inject proper prime powers `d↦(minFac d, factorization d (minFac d))`
    into `Icc 2 N ×ˢ Icc 2 N` (InjOn via `IsPrimePow.minFac_pow_factorization_eq`); `Finset.sum_product`
    + `Summable.sum_le_tsum` against `summable_log_div_sq`. Gotcha: `Finset.sum_filter_of_ne` obligation
    has an un-β-reduced lambda — `show Λ d/(d:ℝ)=0` first. Use `Finset.sum_product` (f on pairs,
    first-order match), not `sum_product'`. `Real.log_nonneg` needs `1≤b` not `0≤b`, so the `sum_le_tsum`
    nonneg proof must `rcases` out `b=0`.

### 🎯 NEXT TARGET — Mertens' second theorem `∑_{p≤x} 1/p = log log x + O(1)` (mathlib-absent)
**Analytic groundwork is now ALL DONE (this lap, in `Mertens.lean`, axiom-clean):**
- `hasDerivAt_log_log` : `d/dt log(log t) = 1/(t·log t)` (t>1).
- `integral_inv_log_mul` : `∫_a^b 1/(t·log t) = log log b − log log a` (1<a≤b) — the **`log log x` main term**.
- `hasDerivAt_inv_log` : `d/dt (1/log t) = −1/(t·(log t)²)` (t>1) — the **weight derivative** `deriv f`.
- `integral_inv_mul_sq_log` : `∫_a^b 1/(t·(log t)²) = 1/log a − 1/log b` — bounds the **`O(1)` remainder**
  `∫ r/(t log²t)` by `C/log a` uniformly in `b`.

**✅ Abel-summation CORE done this lap** (`939d3a0`, `879548a`):
- `primeLogDivCoeff n = [n prime]·(log n)/n`, `primeRecipSum N = ∑_{p≤N} 1/p`, with bridges
  `sum_primeLogDivCoeff_eq` (`∑c = primeSumDiv`) and `sum_inv_log_mul_primeLogDivCoeff_eq` (`∑(1/log)·c = ∑1/p`).
- **`mertens_second_identity`** (axiom-clean):
  `∑_{p≤N} 1/p = primeSumDiv N/log N + ∫_2^N primeSumDiv ⌊t⌋₊ /(t (log t)²) dt`. Used
  `sum_mul_eq_sub_integral_mul₁` (the `c0=c1=0`/integral-from-2 variant — the `₀` version fails since
  `1/log` is undifferentiable at `t=1`); side-conditions discharged via `hasDerivAt_inv_log`;
  integrand `deriv f` rewritten by `setIntegral_congr_fun` (NB: β-reduce the integrand with `simp only []`
  before `rw`).
- **`primeSumDiv_div_log_tendsto_one`**: the boundary term `→ 1` (so it is `1 + o(1)`, i.e. `O(1)`).

**✅ MERTENS' SECOND THEOREM DONE** (`9a3303d`): `mertens_second : (∑_{p≤N} 1/p − log log N) =O[atTop] 1`,
axiom-clean, mathlib-absent. Integral split (`intervalIntegral.integral_sub`) into the `log log N` main
term + an `O(1)` remainder (`norm_integral_le_abs_of_norm_le` with `abs_primeSumDiv_floor_sub_log_le` +
`integral_inv_mul_sq_log`); step-function integrability from `integrableOn_primeSumDiv_floor_div` (mathlib
`integrableOn_mul_sum_Icc`). Both Mertens' 1st and 2nd theorems now complete in `Mertens.lean`.

### ✅ Mertens' 3rd UP TO CONSTANT done (`f9b15ab`): `mertens_third_up_to_const : ∏(1−1/p) ≍ 1/log N`
`primeProd`, `primeCorr`, `log_primeProd_eq`/`_corr`, `log_one_sub_add_self_abs_le` (|log(1−x)+x|≤x², local
deriv-monotonicity proof), `abs_primeCorr_le`. The classical Mertens trilogy is now in `Mertens.lean`.

### ✅ SHARP Mertens 2nd & 3rd DONE (2026-06-19, `ecebe9d`/`1fc0cb1`/+1) — convergence forms, axiom-clean
All three landed this lap in `Mertens.lean`, `#print axioms = [propext, Classical.choice, Quot.sound]`:
1. **`mertens_second_tendsto`** : `∑_{p≤N} 1/p − log log N → M` (Meissel–Mertens `M := meisselMertensM`).
   Upgraded the bounded remainder integral of `mertens_second` to an *improper* integral that converges:
   `mertensRemainder` (the remainder integrand), `integral_norm_mertensRemainder_le` (`∫_2^N ‖·‖ ≤ C/log2`),
   `integrableOn_mertensRemainder_Ioi` (via `integrableOn_Ioi_of_intervalIntegral_norm_bounded`),
   `mertensRemainder_integral_tendsto` (via `intervalIntegral_tendsto_integral_Ioi 2 … tendsto_natCast`).
   `M := 1 + ∫_{Ioi 2} mertensRemainder − log log 2`.
2. **`mertens_third_tendsto`** : `log ∏(1−1/p) + log log N → C₃` (`C₃ := mertensThirdConst := (∑'ₚ) − M`).
   Correction series converges absolutely: `primeCorrCoeff`, `summable_primeCorrCoeff` (comparison `∑1/n²`,
   `abs_primeCorrCoeff_le` + `log_one_sub_add_self_abs_le`), `primeCorr_eq_sum_range`, `primeCorr_tendsto`
   (`HasSum.tendsto_sum_nat` ∘ `+1`). Assembled with `mertens_second_tendsto`.
   (NB this SUPERSEDES the old Aristotle `0fa80268` `summable_primeCorr` request — done locally.)
3. **`mertens_third_tendsto_exp`** : `∏_{p≤N}(1−1/p)·log N → e^{C₃}` (`primeProd_pos` + `exp(log a+log b)`);
   **`mertens_third_isEquivalent`** : `∏(1−1/p) ~[atTop] e^{C₃}/log N` (textbook form, via
   `isEquivalent_iff_tendsto_one`; gotcha: that iff gives pointwise `(f/g) N` — `simp [Pi.div_apply]` first).

### 🎯 NEXT TARGET — the ONE deep equation `C₃ = −γ` (⇔ `M = γ + ∑'ₚ(log(1−1/p)+1/p)`)
This is now the *sole* gap to the classical `∏(1−1/p) ~ e^{−γ}/log x`. The reduction is already in the
repo: **`mertens_third_classical (hγ : mertensThirdConst = −Real.eulerMascheroniConstant)` ⟹
`∏(1−1/p)·log N → e^{−γ}`**, axiom-clean, so the headline is machine-checked *modulo `hγ`*. `γ` is now
imported (`Mathlib.NumberTheory.Harmonic.EulerMascheroni`, `Real.eulerMascheroniConstant`,
`Real.tendsto_harmonic_sub_log`).
- **Why deep, not elementary:** `γ = lim(∑_{k≤n}1/k − log n)` is about *all* integers; `C₃` is about
  *primes*. No elementary bridge — needs the ζ Euler-product transfer.
- **Route (all ingredients in mathlib v4.29.1):** `riemannZeta_eulerProduct_exp_log` (Re s>1:
  `log ζ(s) = ∑_p ∑_{k≥1} p^{−ks}/k = P(s) + ∑_p(bounded)`, `P(s) = ∑_p p^{−s}` prime-zeta) +
  `tendsto_riemannZeta_sub_one_div` (`ζ(s) − 1/(s−1) → γ` as `s → 1⁺`, in `Harmonic/ZetaAsymp.lean`).
  Transfer `P(s)` as `s→1⁺` to the partial sum `∑_{p≤N}1/p` by a real Abel/Tauberian argument, match
  against `mertens_second_tendsto` to extract `M`, and against `log ζ ~ −log(s−1)+γ` to get the `γ`.
  **Multi-lap.** Progress accumulating in **`MertensConstant.lean`** (new module, all axiom-clean):
  - ✅ `primeZeta s := ∑'_p p^{−s}`, `summable_primeZeta_term` (s>1), `primeZeta_nonneg`.
  - ✅ `riemannZeta_eulerProduct_ofReal` (real specialisation of `riemannZeta_eulerProduct_exp_log`).
  - ✅ `neg_clog_eq_ofReal` (term realness: `−clog(1−p^{−s}) = ↑(−log(1−p^{−s}))`, since `1−p^{−s}>0`),
    `summable_real_eulerLog` (`≤ 2p^{−s}` via `|log(1−x)+x|≤x²`), `clog_tsum_eq_ofReal`.
  - ✅ **`riemannZeta_eq_ofReal_exp`** : `ζ(s) = ↑(exp(∑'_p −log(1−p^{−s})))` — ζ manifestly real-positive
    on `(1,∞)`; the **real Euler product**.
  - ✅ **brick (i)** `log_realZeta_eq` : `Real.log(realZeta s) = ∑'_p −log(1−p^{−s})` (`realZeta s :=
    (riemannZeta s).re`, `realZeta_pos`). Take `Real.log` of the exp identity.
  - ✅ **brick (ii-a)** `neg_log_one_sub_prime_hasSum` : `−log(1−p^{−s}) = ∑'_n (p^{−s})^{n+1}/(n+1)` (via
    `Real.hasSum_pow_div_log_of_abs_lt_one`, since `0<p^{−s}<1`). `n=0` term `= p^{−s}` (prime-zeta), `n≥1`
    tail `= G`.
  - ✅ **brick (ii-b)** `log_realZeta_split` : `log ζ(s) = primeZeta s + mertensCorr s`
    (`mertensCorr s := ∑'_p (−log(1−p^{−s})−p^{−s})` = `G(s)`, the `n≥1` Mercator tail; `summable_mertensCorr_term`,
    `mertensCorr_nonneg`). Clean `tsum_add` split, no Fubini needed.
  - ✅ **Limit A** `tendsto_primeZeta_add_logSub` : `primeZeta s + log(s−1) → −mertensCorr 1` as `s→1⁺`.
    Built from: `tendsto_realZeta_sub_one_div` (real specialisation of mathlib's
    `ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right`), `tendsto_sub_one_mul_realZeta` ((s−1)ζ→1),
    A1 `tendsto_logRealZeta_add_logSub` (log ζ(s)+log(s−1)→0), A2 `continuousOn_mertensCorr` (G continuous on
    [1,∞) via `continuousOn_tsum` dominated by `p^{−2}`).
  - ✅ **bridge** `tsum_primeCorrCoeff_eq` : `∑'_n primeCorrCoeff n = −mertensCorr 1` (via `Injective.tsum_eq`,
    `rpow_neg_one`).
  - ✅ **🎯 CRUX ISOLATED** `mertensThirdConst_eq_neg_gamma_of_tauberian` (+ `mertens_third_classical_of_tauberian`):
    `mertensThirdConst = −γ` (hence the full `∏(1−1/p)·logN→e^{−γ}` headline) follows from **ONE** clean limit,
    **Limit B**: `primeZeta s + log(s−1) → M − γ` as `s→1⁺` (`M = meisselMertensM`). Everything else machine-checked.
    [Why one hypothesis suffices: Limit A and Limit B are two evaluations of the SAME limit; uniqueness forces
    `−mertensCorr 1 = M − γ`, and `mertensThirdConst = −mertensCorr 1 − M = −γ`.]
  - ✅ **brick B0** `primeZetaCoeff_tendsto` : `primeZeta s = lim_N ∑_{p≤N} p^{−s}` (`primeZetaCoeff`,
    `summable_primeZetaCoeff`, `tsum_primeZetaCoeff_eq`) — the Finset-partial-sum form Abel summation consumes.
  - **REMAINING = Limit B only** (`primeZeta s + log(s−1) → M − γ`). All mathlib footholds identified.
    - ✅ **B1 DONE** (`primeZeta_eq_abel_integral`, axiom-clean, `65298e6`):
      `primeZeta s = (s−1)·∫_1^∞ (∑_{p≤⌊t⌋}1/p)·t^{−s} dt`. All 6 Abel hypotheses proven; the last,
      `hg_int = integrableAtFilter_rpow_neg_mul_log` (`IntegrableAtFilter (t^{−s}(1+log t)) atTop`), was
      proven **locally** (g=O(t^{−s'}), s'=(s+1)/2, via `isLittleO_log_rpow_atTop` +
      `integrableAtFilter_rpow_atTop_iff` + `IsBigO.integrableAtFilter`) — **superseding Aristotle `2919e0d2`**.
      Assembly: Abel theorem + `rpow_one_sub_mul_primeRecipCoeff` + `tendsto_nhds_unique` (Icc↔range via
      `Nat.range_succ_eq_Icc_zero`) + `integral_const_mul`/`setIntegral_congr_fun`.
    - **B2** (s→1⁺ limit) — the spine is now built; TWO pieces remain. Plan: substitute `t=eˣ` so
      `primeZeta s = (s−1)∫_0^∞ A(eˣ)·e^{−(s−1)x} dx` (`A(t)=∑_{p≤⌊t⌋}1/p`); then `A(eˣ)=log x+M+r(x)`
      (`mertens_second_tendsto`, since `log log eˣ = log x`) splits it into three:
      - ✅ **log-part DONE** (`sub_one_mul_integral_log_exp`, `3b56a77`): `(s−1)∫_0^∞ log x·e^{−(s−1)x} dx =
        −γ − log(s−1)`. Via change of variables `u=(s−1)x` (`sub_one_mul_integral_log_exp_eq`,
        `integral_comp_mul_left_Ioi`) + the **γ-injection** `integral_log_mul_exp_neg_Ioi_eq_neg_gamma`
        (`∫_0^∞ log u·e^{−u}=−γ`, via complex `hasDerivAt_GammaIntegral`+`Real.hasDerivAt_Gamma_one`+ofReal)
        + `integrableOn_log_mul_exp_neg`. **This is the full `−γ` contribution.**
      - ✅ **M-part DONE** (`tendsto_sub_one_mul_integral_rpow`, `6ed4543`; eˣ-form
        `sub_one_mul_integral_exp_neg`, `b7627f4`): `(s−1)∫_0^∞ e^{−(s−1)x}=1`, so the M-term
        `(s−1)∫_0^∞ M·e^{−(s−1)x}=M` exactly.
      - ✅ **(1) exp substitution of B1 DONE** (`primeZeta_eq_abel_integral_exp`, `d059c3d`):
        `primeZeta s = (s−1)∫_0^∞ A(eˣ)·e^{−(s−1)x} dx`. Via `integral_image_eq_integral_abs_deriv_smul`
        (f=exp on `Ioi 0`: `Real.hasDerivAt_exp`, `Real.exp_injective.injOn`, `exp''Ioi 0 = Ioi 1`) — the
        measurable Jacobian change-of-variables, since `A=primeRecipSum⌊·⌋` is a step function (the
        continuous-`g` lemma `integral_comp_mul_deriv_Ioi` does NOT apply). `(eˣ)^{−s}·eˣ = e^{−(s−1)x}`.
      - ⏳ **(2) THE Tauberian/Abelian error — the SOLE remaining piece of Limit B.** Goal:
        `(s−1)∫_0^∞ r(x)·e^{−(s−1)x} dx → 0` as `s→1⁺`, where `r(x)=A(eˣ)−log x−M`. Sub-steps next lap:
        (a) **`r(x)→0`** as `x→∞`: from `mertens_second_tendsto` (`primeRecipSum N − log log N → M`)
        composed with `⌊eˣ⌋→∞`, plus `log log⌊eˣ⌋ − log x → 0` (`e^x−1<⌊eˣ⌋≤eˣ` ⟹ `log⌊eˣ⌋−x→0` ⟹
        `log log⌊eˣ⌋/log x... `; care near small x). (b) **integrability + the additive split**
        `(s−1)∫_0^∞ A(eˣ)e^{−(s−1)x} = (s−1)∫ log x·e^{−(s−1)x} + (s−1)∫ M·e^{−(s−1)x} + (s−1)∫ r·e^{−(s−1)x}`
        — NOTE `r` is unbounded near `x=0` (`A(eˣ)=0` for `x<log 2`, so `r(x)=−log x−M → +∞`), but
        `r·e^{−(s−1)x}` is integrable (log singularity). (c) **the Abelian limit**
        `lim_{δ→0⁺} δ∫_0^∞ r(x)e^{−δx}dx = lim_{x→∞}r(x) = 0` (final-value theorem; not in mathlib). Sub
        `u=(s−1)x`: `δ∫ r e^{−δx} = ∫ r(u/δ)e^{−u}du`, `r(u/δ)→0` pointwise as δ→0⁺, dominated convergence.
      - **Then assemble** (`tendsto_primeZeta_add_logSub_limitB`): log-part (`sub_one_mul_integral_log_exp`,
        `−γ−log(s−1)`) + M-part (`M`) + error (`→0`) ⟹ `primeZeta s + log(s−1) → M − γ` = **Limit B**, which
        feeds `mertens_third_classical_of_tauberian` to discharge the classical `e^{−γ}` headline.
- Lower-hanging PNT-layer alternatives if the constant stalls: explicit Chebyshev `ψ/θ` two-sided bounds.

### (superseded) nagura wall — FINAL for elementary methods
- **nagura_prime wall is FINAL for elementary methods (sharpened this lap).** The refined constant
  `A = (7/15)log2+(3/10)log3+(1/6)log5` is **EXACTLY** the Chebyshev constant
  `(1/2)log2+(1/3)log3+(1/5)log5−(1/30)log30 ≈ 0.921292` (verified algebraically). So
  `theta_refined_lower` (const `A`) and `psi_refined_upper` (const `(6/5)A`) are matched at `(6/5)A` by
  construction with **zero slack**: a prime in `(n,6n/5]` needs `θ(6n/5)−θ(n)>0` ⟺ leading-order
  `(6/5)A·n − (6/5)A·n > 0`, impossible. Elementary improvement is ruled out (Chebyshev's constant is
  this method's ceiling). The ONLY routes to `nagura_prime`: (i) explicit-error PNT
  (`θ(x)≥(1−ε)x` for *explicit* `X(ε)` — deeper than the qualitative `θ∼x` we have; qualitative gives a
  non-constructive threshold, so the small-case ladder can't be bounded), or (ii) Nagura's 1952 finite
  inequality (needs the paper). Superseded by the unconditional `3/2−o(N)`; lowest value.

### Next-lap quick win (do FIRST — cheap, possibly eliminates the whole port)
**Re-grep an UPDATED mathlib pin for a native PNT before anything else.** Verified this lap: our pin
`v4.29.1` has only the ζ≠0-on-Re=1 input + the conditional π↔θ reduction/bounds in `Chebyshev.lean`
(`π⌊x⌋₊ = θ(x)/log x + ∫…`, plus `=O/=o` difference bounds) — NOT the asymptotic `θ∼x`/`ψ∼x`, and NO
`WienerIkehara`. That gap is exactly what our port fills; mathlib was "on-trajectory" to land it. So run
`grep -rln "WienerIkehara\|chebyshev_asymptotic\|prime_number_theorem\|psi.*IsEquivalent" .lake/packages/mathlib/Mathlib`
on a bumped pin. **If it landed**, swap `PrimeGap.weakPNT` to cite mathlib and DELETE the ~5000 ported
lines (`Wiener`/`Consequences`/etc.) — flagship stays axiom-clean for free, repo gets much lighter, and
the two `prelim_decay` sorries vanish with the deleted file. Cheapest possible resolution.

### Cleanup option (judgement call for a future lap)
The `{prelim_decay_2, prelim_decay_3, decay_alt, AbsolutelyContinuous}` cluster is a fully self-contained
DEAD-CODE island in `Wiener.lean`. Either prove (paths above) or excise it to make the port 100%
sorry-free with no warnings. Kept for now: faithful to upstream + a genuine open sub-problem + Aristotle
attempting. If excised, document the omission in the `Wiener` header.

---

## (ARCHIVED — superseded by the discharge above) Reflection — 2026-06-19
*The section below predates the discharge; it argued weakPNT was 🟠 / not lap-sized / wait-and-cite.
That was WRONG — the port worked in one grind lap. Retained for the historical attack-map only.*


## Reflection — 2026-06-19 (deep-reflection lap, strong model)

*Whole-project altitude pass. Build green (8286 jobs); entire axiom ledger re-verified from real
`#print axioms`; faithfulness re-audited. This section is the durable direction call — grind laps inherit it.*

### The direction call
**The no-three-in-line thread is at its natural, valuable endpoint — do NOT mistake "one cited axiom
remains" for "unfinished."** Concretely:
- The **originally-mandated target** (`DIRECTION.md`: HJSW `3N/2` proved, axiom-clean, in `Statement.lean`)
  is **COMPLETE** — `hjsw_lower_bound : 3(p−1) ≤ maxNoThreeInLine(2p)`, kernel-clean.
- The treadmill then **overshot** it (healthily — real new theorem every lap, NOT circling): it built the
  full general-`N` constant ladder `3/4 → 15/16 → 6/5 → 3/2−o(N)`, reaching **HJSW's optimal constant**.
- The flagship `maxNoThreeInLine_ge_three_halves_sub` rests on **exactly one** cited deep axiom, `weakPNT`
  (the PNT, `ψ(x)∼x`). The **audit surface** (`Statement.lean`) and the **two unconditional improvements
  past Bertrand's `3/4`** (`15/16`, `6/5`) are **fully axiom-clean**. This is the textbook legitimate
  endpoint the reflection charter names: *"one narrow cited axiom + a fully-built remainder."*

### `weakPNT` is 🟠, and that's the honest classification (named reason)
It is the Prime Number Theorem — *proven* (so never 🔴), but absent from mathlib and **not chippable in
lap-sized pieces** (so not 🟡). Discharging it = porting PNTAnd's **~4000-line Wiener–Ikehara Fourier tower**
(`Wiener.lean`+`Fourier.lean`+`SmoothExistence.lean`+Mathlib patches). **De-risking finding this lap:** the
historically-hard *arithmetic* crux — ζ≠0 on `Re=1` — is **already in our mathlib pin**
(`riemannZeta_ne_zero_of_one_le_re`, `LSeries/Nonvanishing.lean:411`). The *only* gap to `weakPNT` is the
**tauberian bridge** (Wiener–Ikehara), and mathlib is visibly on-trajectory to land it
(`LSeries/PrimesInAP.lean` already wires the L-series machinery). So the realistic path is **wait-and-cite**,
not a heroic port.

### KEEP doing
- The clean architecture: the deep axiom is isolated to `PrimeGap.lean`; the mandated audit surface
  `Statement.lean` stays axiom-clean. Never let `weakPNT`/`sorryAx` leak into `Statement.lean`.
- Verified-ledger discipline: re-run real `#print axioms` before claiming clean; commit only green.

### STOP doing
- **STOP squeezing tighter elementary Chebyshev constants** (the `nagura_prime`/exact-`5/4` thread): the
  `T`-method ratio is provably exactly `6/5` with no slack — diminishing returns at the elementary ceiling.
- **STOP re-feeding Aristotle the cold `nagura_prime`** (job `1644a603` already IDLE'd on it cold). Re-submitting
  the same statement is not "advancing the attack."
- **STOP treating `weakPNT` as a lap-sized grind.** It is 🟠. Either the cheap dep test, or wait-and-cite.

### Single highest-value next target (with reasoning)
**Decisively resolve `weakPNT`** — it is the *only* thing between the flagship `3/2` result and full
axiom-cleanliness; everything else in NTL is done, open-math (Main Conjecture), or diminishing-returns.
Execute in this order:
1. **~~(cheap dep-test)~~ — RUN 2026-06-19, DEFINITIVELY DEAD on-box. Do NOT retry.** Added
   `path = "../PrimeNumberTheoremAnd"` require in a throwaway branch and ran `lake update PrimeNumberTheoremAnd`.
   Result: the **toolchain check PASSED** (`toolchain not updated; already up-to-date` — so lean v4.29.0-vs-v4.29.1
   is NOT the blocker), but lake then died fetching PNTAnd's **transitive git deps**:
   `info: PrimeCert: cloning https://github.com/b-mehta/PrimeCert` → `git exited with code 128` (no GitHub egress).
   PNTAnd requires `LeanArchitect`, `checkdecls`, `leancert`, `PrimeCert` (all GitHub `v4.29.0`) — none local —
   **and** pins **mathlib `v4.29.0` ≠ our `v4.29.1`** (lake can't hold two mathlib revs). So the lake-require
   route is blocked for two independent reasons (missing transitive deps + mathlib-rev conflict); neither is
   fixable on this no-egress box. Workspace fully restored, build green (8286). **Don't re-run this.**
2. **(lowest effort, preferred)** Treat `weakPNT` as wait-and-cite: periodically check whether mathlib has
   landed Wiener–Ikehara / `ψ∼x` (grep the pin for `WienerIkehara`, a `Chebyshev.psi` asymptotic). When it
   does, replace `axiom weakPNT` with the mathlib citation → flagship becomes axiom-clean for free.
3. **(bounded multi-lap port, only if 1–2 both dead-end and a real bite is wanted)** Port the Wiener–Ikehara
   tower from PNTAnd (Apache-2.0, license-clean to port; do NOT submit upstream per `[[feedback_no_pnt_plus_submission]]`).
   **Sizing (measured this lap — it is BOUNDED, not from-scratch):** ALL heavy mathlib analytic prereqs are
   ALREADY in our v4.29.1 pin (`Fourier/RiemannLebesgueLemma`, `Normed/Group/Tannery`, `SumIntegralComparisons`,
   `EMetricSpace/BoundedVariation`, `Analysis/Convolution`, `Chebyshev`, `LSeries/PrimesInAP`), AND the
   arithmetic crux ζ≠0-on-`Re=1` (`riemannZeta_ne_zero_of_one_le_re`). So the port surface is just PNTAnd's
   OWN code across a **one-patch** mathlib gap (their lean v4.29.0 → ours v4.29.1):
   `Wiener.lean` (4118 lines, the tauberian bulk) + the `WeakPNT''/WeakPNT'` slice of `Consequences.lean`
   (~200 of its 2545) + `Fourier.lean` (70) + `SmoothExistence.lean` (107) + part of `Defs.lean` (305) + the
   needed Mathlib patches (`Asymptotics/Uniformly` 164, `Asymptotics/Asymptotics` 41, `Chebyshev` 303,
   `Log/Basic` 17 ≈ 525 lines; the Sieve/* patches are NOT in the WeakPNT cone — exclude). Strip the
   `@[blueprint ...]` attrs + `import Architect`. Total ≈ **5000 lines, mostly mechanical**, risk = v4.29.0→v4.29.1
   API drift (likely small — one patch). A real multi-lap project but tractable; do it only if mathlib stalls
   on landing Wiener–Ikehara natively. **NB: the port route SIDESTEPS the dep-hell that killed option 1** —
   `Wiener.lean`'s cone imports only `Architect` (strippable) + `Mathlib.*` + `PrimeNumberTheoremAnd.*`; it does
   NOT use `PrimeCert`/`leancert`/`checkdecls` (those are the prime-certificate/sieve parts), so a source-copy
   build against OUR mathlib needs none of the missing transitive deps. Since option 1 is now dead, this is the
   only *active* discharge route besides wait-and-cite. **Patch-layer probed 2026-06-19:** the patch lemmas
   (`Real.tendsto_pow_log_div_pow_atTop`, `Asymptotics.isLittleO_const_id_cocompact`, `Filter.Eventually.natCast`,
   `IsBigO.natCast`, `Real.isLittleO_log_rpow_rpow_atTop`) are NOT in our v4.29.1 under those names — so the
   ~525-line patch layer genuinely needs porting (some have differently-named relatives, e.g. we already use
   `isLittleO_log_rpow_atTop`). Confirms the ~5000-line estimate; start a port here (patches are small & self-contained).
   **PORT STARTED 2026-06-19 — bricks 1–2 DONE (axiom-clean, build green 8287):**
   `src/LeanFormalizations/NumberTheory/PrimeNumberTheorem/Asymptotics.lean` — (1) the 5 Asymptotics lemmas
   (`isLittleO_const_id_{cocompact,atTop,atBot}`, `eventually_natCast`, `isBigO_natCast`); (2) the Log/Basic patch
   `tendsto_pow_log_div_pow_atTop` (its dep `isLittleO_log_rpow_rpow_atTop` is in our pin at root namespace). All
   deps already in our pin → clean port, no API drift on the patch layer so far. **Next bricks (dependency order):**
   `Mathlib/Analysis/Asymptotics/Uniformly`
   (164), PNTAnd `Mathlib/NumberTheory/Chebyshev` patch (303), then `Defs.lean` slice → `Fourier.lean` (70) →
   `SmoothExistence.lean` (107) → the big one `Wiener.lean` (4118) → `Consequences` `WeakPNT''` slice. Strip
   `@[blueprint]`/`import Architect` throughout. (Reminder: speculative — `wait-and-cite` still preferred.)
4. **(fallback grind, low value)** If a green-producing lap is wanted and 1–3 stall: `nagura_prime` →
   unconditional `6/5 → 5/4`. Modest, hard (elementary ceiling). Documented; don't fixate.

### Faithfulness (re-audited this lap — all ✓, incl. an independent cross-check)
HJSW `3(p−1)` at `N=2p` = `3(N−2)/2` (matches `DIRECTION.md` / the paper); `NoThreeCollinear` = no three
*distinct* points `Collinear ℝ` (every slope incl. vertical — the corrected `Green72.AllowedSet`);
`maxNoThreeInLine_ge_three_halves_sub` = `∀ε>0, ∀ᶠN, (3/2−ε)N ≤ max N` (HJSW's actual `3N/2−o(N)`), and it
transparently carries `weakPNT` in `#print axioms`. No transcription drift.
**Independent NL→Lean cross-check (harvested this lap — Aristotle `72891d77`):** given only the *prose* HJSW
statement, Aristotle independently formalized `exists_no_three_collinear` — for every prime `p`, a `Finset (ℕ×ℕ)`
with `q.1 < 2p ∧ q.2 < 2p`, `card = 3(p−1)`, `NoThreeCollinear` — i.e. a **logically-equivalent** statement to
our `hjsw_lower_bound`. It also proved (axiom-clean) `collinear_iff_cross_zero`: Mathlib's `Collinear ℝ` on three
grid points ⟺ the 2×2 orientation determinant vanishes — an independent certificate that our `Collinear ℝ`-based
`NoThreeCollinear` is the right notion. Two independent formalizations converging on the same statement +
the same collinearity criterion ⇒ high confidence the audit surface is faithful. (Job now harvested/IDLE.)

---

## ✅✅ 2026-06-19 (two-sided refined-Chebyshev lap) — DONE: unconditional `3/4 → 15/16 → 6/5`

The refined-Chebyshev program below is **COMPLETE and exploited**. The full two-sided stack is built and
axiom-clean in `PrimeGap.lean`: `psi_refined_lower`, `theta_refined_lower`, `psi_refined_upper`
(telescoping iterate `ψ ≤ (6/5)A·n + O(log²n)` — the crux), `logFactorial_comb_upper`,
`logFactorial_comb_ge_psi_sub`, `psi_refined_upper_step`, `sqrt_log_small`, `log_le_sqrt_small`,
`chebyshev_const_lt`. Payoffs: **`maxNoThreeInLine_ge_fifteen_sixteenths`** (`15/16`, `N≥2⁴¹`, via prime
in `(n,8n/5]`) and **`maxNoThreeInLine_ge_six_fifths`** (`6/5`, `N≥5·2⁴⁰`, via Nagura-strength prime in
`(n,5n/4]`). All axiom-clean; `nagura_prime` no longer blocks any headline.

### ✅✅✅ 2026-06-19 (PNT lap) — FRONTIER CLOSED: full HJSW `3/2 − o(N)` formalized

Path 4 is **DONE**. `maxNoThreeInLine_ge_three_halves_sub` (`∀ε>0, eventually (3/2−ε)N ≤ max N`) is
proven in `PrimeGap.lean` via `exists_prime_gap_pnt` (prime in `(n,cn]` for every `c>1`), on top of the
single disclosed axiom `weakPNT : Chebyshev.psi ~[atTop] (·)` (= `PrimeNumberTheoremAnd.WeakPNT''`,
about the SAME mathlib `Chebyshev.psi`). The general-`N` constant frontier (Bertrand `3/4` →…→ HJSW
`3/2`) is **closed**.

**THE ONLY REMAINING DEBT — discharge `weakPNT` (make `3/2−o(N)` fully axiom-clean).** Options:
1. **Add `~/src/PrimeNumberTheoremAnd` as a lake dependency** and `import` its `Consequences`, replacing
   `axiom weakPNT` with `theorem weakPNT := WeakPNT''` (or use `WeakPNT''` directly). Risk: it pins
   `lean4:v4.29.0` vs our `v4.29.1` and a (possibly different) mathlib rev — may need a toolchain bump or
   a compatible mathlib. Try in a throwaway branch first: `lake` may refuse mismatched mathlib revs.
2. **Port just the WeakPNT proof chain** (Wiener–Ikehara tauberian) — very large; not worth it vs (1).
3. Wait for mathlib to land the PNT (in progress upstream); then cite from mathlib directly.
Recommended: attempt (1) — it's the whole prize (fully axiom-clean HJSW `3/2`) for relatively little if
the toolchains cooperate.

(Independently: `nagura_prime` remains a disclosed `sorry` for the *exact* small-threshold `6/5` gap /
exact `5/4` constant; now fully non-blocking and low priority — the `3/2` result subsumes its purpose.)

---

### [SUPERSEDED by the PNT closure above] push the constant `6/5 → 5/4 → … → 3/2`

The current method gives a prime in `(n, c·n]` for any **fixed `c > 6/5`**, constant `3/(2c) < 5/4`
(strictly). Three viable attack paths to go further:

1. **Tighten `c → 6/5⁺` for a constant arbitrarily close to `5/4`** (cheap, mechanical). Copy
   `exists_prime_in_five_fourths` / `maxNoThreeInLine_ge_six_fifths` with `c = 31/25` (`>6/5`), margin
   `A/50`, larger threshold ⇒ constant `75/62 ≈ 1.21`. Diminishing returns; documents the limit but never
   reaches exactly `5/4`. Low priority.
2. **⚠️ The elementary ceiling is `5/4` — do NOT chase `3/2` with `T`-combinations.** My constants
   `A ≈ 0.9213` (lower) and `(6/5)A ≈ 1.106` (upper) **are essentially the classical Chebyshev constants**
   `0.921 < ψ(x)/x < 1.106`, which are the *best obtainable from the `T`-function method* (any finite
   `log(⌊x/k⌋!)` combination). Their ratio is `≈ 6/5`, so `c > 6/5` is forced and the no-three constant
   `3/(2c)` is capped strictly below **`5/4`**. A finer prime combination buys only a *tiny* improvement
   toward this same `6/5` ratio — NOT toward `1`. **Exceeding `5/4` (toward HJSW's `3/2`) genuinely needs
   PNT-strength** (`ψ(x) = x + o(x)`): either mathlib's analytic PNT (`PrimeNumberTheoremAnd`, if
   portable) or an elementary Selberg/Erdős PNT (a large multi-lap formalization). This is the real deep
   wall; the `T`-method has been mined out at `5/4 − ε`.
3. **`nagura_prime` (exact `6/5`, `n≥25`) — the small-threshold version, = exact `5/4` constant.**
   UNreachable from the current stack (needs `c=6/5` exactly, but `(6/5)A`-upper forces `c>6/5` strictly —
   the ratio is exactly the Chebyshev ratio, with no slack). Genuinely needs Nagura's sharper finite
   numerical inequality (see `ON-LINE-REQUEST.md`). Deep debt; the `5/4` payoff
   `maxNoThreeInLine_ge_five_fourths` is wired to it but now superseded by the unconditional `6/5`. Keep
   as a disclosed `sorry`; do NOT delete.

**Recommended next lap:** ⭐ **path 4 — PNT → `3/2 − o(1)` (the real prize, scaffold ready).** Confirmed
this lap: `~/src/PrimeNumberTheoremAnd` proves **`WeakPNT'' : ψ ~[atTop] (fun x ↦ x)`**
(`Consequences.lean:105`) and — crucially — its **`ψ` IS mathlib's `Chebyshev.psi`** (the proof rewrites
via `Chebyshev.psi_eq_sum_Icc`). Toolchains nearly match (theirs `v4.29.0`, ours `v4.29.1`). Plan:
1. Add a **disclosed `axiom weakPNT : Chebyshev.psi ~[atTop] (fun x ↦ x)`** (honest debt — a *proven*
   theorem in a real Lean formalization; cite `PrimeNumberTheoremAnd/Consequences.lean WeakPNT''`). Do
   NOT pollute existing axiom-clean headlines; this is a new, clearly-cited deep axiom.
2. `Asymptotics.IsEquivalent` unfolds to `(ψ − id) =o[atTop] id`; via `isLittleO_iff` extract: ∀ ε>0,
   ∃ N₀, ∀ x ≥ N₀, `(1−ε)x ≤ ψ(x) ≤ (1+ε)x`. Then `θ ~ ψ` (gap `O(√x log x)` = `o(x)`,
   `abs_psi_sub_theta_le_sqrt_mul_log`) gives the same for `θ`.
3. Re-run the prime-gap contradiction (mirror `exists_prime_in_five_fourths`): no prime in `(n, cn]` ⟹
   `θ(cn)=θ(n)`; `(1−ε)cn ≤ θ(cn)=θ(n) ≤ (1+ε)n` ⟹ for any `c > (1+ε)/(1−ε)` (→ any `c > 1` as ε→0) a
   prime exists. Constant `3/(2c) → 3/2`.
4. Headline: `∀ ε>0, ∃ N₀, ∀ N ≥ N₀, (3/2 − ε)·N ≤ maxNoThreeInLine N` — **HJSW's `3N/2 − o(N)`,
   matching `hjsw_lower_bound` at all large `N`.** This closes the general-`N` constant frontier.

(Path 1 — bag `75/62 ≈ 1.21` via `c = 31/25` — is a cheap mechanical fallback if PNT porting stalls;
low value. Path 2 as originally framed (more primes → `3/2`) is a MIRAGE — the `T`-method caps at `5/4`.)

**DE-RISKED this lap — the bound-extraction step (path 4 step 2) WORKS** (verified in scratch, copy in):
```lean
open Asymptotics Filter
axiom weakPNT : Chebyshev.psi ~[atTop] (fun x ↦ x)   -- cite PrimeNumberTheoremAnd WeakPNT''
example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, (1 - ε) * x ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ (1 + ε) * x := by
  have hlo := weakPNT.isLittleO
  rw [isLittleO_iff] at hlo
  filter_upwards [hlo hε, eventually_gt_atTop (0:ℝ)] with x hx hxpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxpos] at hx
  simp only [Pi.sub_apply] at hx
  rw [abs_le] at hx
  constructor <;> nlinarith [hx.1, hx.2]
```
Remaining for path 4: (a) the `√·log` error as `o(n)` — use `Real.isLittleO_log_rpow_atTop (r:=1/2)`
(`log =o[atTop] x^(1/2) = √x`) ⇒ ∀ δ>0 eventually `log x ≤ δ√x`, so `√x·log x ≤ δx`; (b) choose
`ε = (c−1)/(c+1)/2` so `(1+ε)/(1−ε) < c`; (c) mirror `exists_prime_in_five_fourths`'s contradiction but
stated `∀ᶠ n in atTop` (intersect the eventually's via `filter_upwards`), giving a prime in `(n,cn]` for
every `c>1`; (d) feed the no-three interface ⇒ `∀ ε>0, ∃N₀, ∀N≥N₀, (3/2−ε)N ≤ maxNoThreeInLine N`.

---

## ⭐⭐ 2026-06-19 (refined-Chebyshev lap) — [SUPERSEDED, see above] general-`N` constant `3/4 → >3/4`

**Strategic finding this lap (do NOT re-derive — it reorients the whole attack).** I proved three ways
that **the crude elementary Chebyshev bounds CANNOT beat Bertrand's `3/4`, for ANY ratio `c<2`** — not
just `6/5`. The central-binomial split, done correctly, gives a prime in `(n,c·n]` only when
`L·c > (8U/3) − 2log2` (`U`,`L` = θ upper/lower constants). With the crude pair `U=log4`, `L=log4/2`
this needs `c > 10/3 ≈ 3.33`; even with the *true* `U=L=1` (PNT) it tops out at `c≈1.28`. The crude
method's weak link is the high-prime product `∏_{c·n<p≤2n}p` (empty only at `c=2`, which is exactly why
Bertrand squeaks out `c=2`). **Conclusion: the ONLY route past `3/4` is a *refined* Chebyshev bound
`ψ(x) ≳ 0.92 x` (Chebyshev's constant `A`), which mathlib lacks entirely.** That is what I started
building this lap, and it's the right multi-lap target. (The earlier "tuned Nagura inequality" framing
was a special case of this same wall.)

**THE REFINED-CHEBYSHEV STACK — built this lap (all axiom-clean, in `PrimeGap.lean`):**
- `sum_vonMangoldt_mul_floor_div` (`∑_{d≤n} Λ(d)⌊n/d⌋ = log(n!)`) — **Chebyshev's `T`-function
  identity, the keystone.** ✅ mathlib lacks it.
- `floor_comb_bounds` (`⌊n⌋−⌊n/2⌋−⌊n/3⌋−⌊n/5⌋+⌊n/30⌋ ∈ {0,1}`, period-30 via `decide`). ✅
- `logFactorial_div_eq_sum` (`log(⌊n/k⌋!) = ∑_{d≤n}Λ(d)⌊n/(kd)⌋`, zero-extension to common range). ✅
- `logFactorial_comb_eq` (the 5-shift `T`-combination `= ∑_{d≤n}Λ(d)·g(n/d)`, `g∈{0,1}`). ✅
- `logFactorial_comb_le_psi` (**`T`-combination `≤ ψ(n)`** — the combinatorial half of `ψ ≳ 0.92n`). ✅
- `log_factorial_le` (**explicit Stirling UPPER bound** `log(m!) ≤ m·log m − m + log(2m)/2 + 1 −
  log2/2`; mathlib has only the lower `Stirling.le_log_factorial_stirling`). ✅

**The crux — remaining work (the analytic half of `ψ ≳ 0.92n`), precise recipe:**
1. **Stirling lower bound on the `T`-combination `f(n) := log(n!)−log(⌊n/2⌋!)−log(⌊n/3⌋!)−log(⌊n/5⌋!)
   +log(⌊n/30⌋!)`.** Use `Stirling.le_log_factorial_stirling` (lower) on the `+` terms `n,⌊n/30⌋` and
   `log_factorial_le` (upper, built this lap) on the `−` terms `⌊n/2⌋,⌊n/3⌋,⌊n/5⌋`. The `n·log n` and
   `−n` leading terms **cancel** (coeffs `1−½−⅓−⅕+1/30 = 0`); residue `= A·n + O(log n)` where
   `A = (7/15)log2 + (3/10)log3 + (1/6)log5 ≈ 0.9213`. Floor errors `⌊n/k⌋ = n/k − {·}` are `O(log n)`.
   ⟹ `f(n) ≥ A·n − C·log n − D`. **This is the messy-but-mechanical analytic core; best as one focused
   lap.** Sub-task: bound `A` below by an explicit rational `> 0.92` — needs `log 3`, `log 5` numeric
   lower bounds (mathlib has only `Real.log_two_{gt,lt}_d9`; derive `log 3`, `log 5` — small project).
2. **Conclude `ψ(n) ≥ A·n − C·log n` from steps (1)+`logFactorial_comb_le_psi`**, hence (with the dual
   *upper* iterate `ψ(n) ≤ A·n/(1−1/6)+…`) a `θ` two-sided bound with ratio `<2`, feeding the
   central-binomial split for a prime in `(n,c·n]`, `c<2`, then `3/(2c) > 3/4` via
   `maxNoThreeInLine_ge_of_two_mul_prime_le`.
3. **Aristotle.** Job `1644a603` (`aris-nagura`) was grinding the from-scratch `nagura_prime` — UNLIKELY
   to crack it cold (it needs exactly this refined infra). NEXT LAP: consider redirecting Aristotle to
   the now-narrowed, self-contained step (1) (`f(n) ≥ A·n − C log n`, Stirling bounds inlined as
   axioms) — far more tractable than from-scratch Nagura.

**Earlier ℕ-Chebyshev infra (still axiom-clean, but capped at `log4/2 ≈ 0.69` — insufficient alone):**
`centralBinom_dvd_lcm_Icc`, `four_pow_lt_mul_lcm`, `factorization_finset_lcm`,
`primePow_dvd_lcm_Icc_iff`, `log_lcm_Icc_eq_psi`, `psi_lower`, `theta_lower`. The refined stack above
supersedes these for the constant (they remain reusable & PR-worthy).

**Reusable spinoffs (PR-worthy to mathlib):** all six refined-stack lemmas above + the earlier ℕ-infra
are general Chebyshev/lcm/factorial facts mathlib lacks.

**Still-disclosed `sorry` (unchanged, honest):** `nagura_prime` (prime in `(n,6n/5]`, `n≥25`) and its
wired payoff `maxNoThreeInLine_ge_five_fourths`. NOTE: the refined route may land a *different* explicit
ratio `c<2` (whatever the `0.92` constant yields) rather than exactly `6/5` — that's fine and still
beats `3/4`. Retarget `maxNoThreeInLine_ge_five_fourths` to the achieved `c` when the analytic half lands.

**Faithfulness (carry-over):** Aristotle `72891d77` (independent NL→Lean of the headline) finished
(IDLE) but its `show`/`download` 500 server-side this lap — retry next lap; not load-bearing.

---

## 📋 2026-06-19 (earlier) — FULL INVENTORY (per how-to-get-unblocked.md)
**Open `sorry` in `src/`: 0.** **Custom `axiom` declarations in `src/`: 0.** Verified by
`grep -rnE '^[[:space:]]*axiom '` (only a docstring word-wrap hit) and `grep -rnw sorry` (only
comments). Every headline `#print axioms = [propext, Classical.choice, Quot.sound]`. This is a
genuinely empty inventory, not a fixation on one blocked thread — the hard crux was *solved* this lap.

**The only non-formalizable thing left in NTL is the open Main Conjecture.** Future *formalizable*
directions, three paths each (none required; all optional next-lap menu):
1. **Sharper general-`N` constant (`3/4 → 3/2`).** (a) Formalize Nagura's theorem (prime in
   `(n, 1.2n]`, n≥25) → constant `≈1.25`; (b) formalize a Baker–Harman–Pintz-style gap → `→3/2`;
   (c) reformulate to only claim the bound at `N=2p` (already done — `hjsw_lower_bound`). Paths
   (a)/(b) are real prime-gap infrastructure projects (mathlib lacks them), not quick laps.
2. **Faithfulness audit.** (a) Harvest Aristotle `72891d77` (independent NL→Lean of the headline) and
   diff its `no-three-collinear`/box/card encoding vs `Statement.lean`; (b) add `native_decide`
   anchors for the construction at more primes (LOW value — `shearSel_noThree` is already proven ∀p,
   so anchors add nothing the kernel didn't); (c) hand-audit `Defs.lean` against the literature def.
   Path (a) is the genuine one.
3. **Strengthen the construction itself (toward 2N).** (a) Search for a base of size `> p` reaching
   `> 3(p-1)`; (b) two-curve / union constructions (prior laps found single-curve caps); (c) port a
   published `(2-ε)N` construction if one exists. Open research; (a)/(b) need exhaustive search first.

## ✅✅ 2026-06-19 (later) — NOTHING OPEN. HJSW COMPLETE.
`shearSel_cross_diag` (the lone `sorry`) is **PROVEN** ⇒ `hjsw_lower` is fully proven, axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Discharged via `shear_diag_partner`/`shear_anti_partner`
(curve-factoring → partner relation → drop tie-break). Promoted to `Statement.lean`
(`hjsw_lower_bound`, `maxNoThreeInLine_ge_three_quarters` = general-`N` `3N/4` via Bertrand).
**Zero `sorry` in the repo.** The only remaining item in the no-three-in-line problem is the
**Main Conjecture (open math)** — not a formalizable proof. The (now historical) attack-path
inventory below is preserved for context. See `HANDOFF-2026-06-19-0728.md` for techniques + the
optional next-lap menu (faithfulness cross-check / sharper general-`N` via prime gaps / cosmetic
polish). Do NOT re-open the items below — they are solved.

---

Inventory of open items + attack paths (per `how-to-get-unblocked.md`). Refreshed 2026-06-19 (lap N+1).
(This isolated clone's focus is solely the HJSW frontier; the main-branch threads — Curtis,
power-tower, constructibles, transcendence, Goodstein — are complete & axiom-clean, recorded in
`STATUS.md` and git history. Do not reopen them here.)

## ⭐⭐ 2026-06-19 UPDATE — THE CONSTRUCTION CRUX IS CRACKED (closed-form rule found)

The open combinatorial crux (the lift-selection rule) is **SOLVED**. A closed-form rule for the
sheared hyperbola was found and verified (exact integer determinant: card, distinct, grid, NoThree)
for EVERY prime `3 ≤ p ≤ 109`. See `SELECTION-RULE-FOUND.md`. Construction:
> drop the pole column `pl=(p−1)/2`; for every other column `(r,s)=(x,(2x+1)⁻¹)` keep 3 of 4 lifts,
> dropping the corner nearest the grid centre `dropped=(r+p·[r≤pl], s+p·[s≤pl])`.

**Lean status now** (`Hyperbola.lean`, all green except one sorry):
- `shearSel p` defined (general, computable); `shearSel_card = 3(p−1)` and `shearSel_grid ⊆ 2p×2p`
  proven **axiom-clean**.
- `hjsw_lower` rewritten to assemble `card + grid + shearSel_noThree` — so the headline `sorry` is
  now the SINGLE lemma `shearSel_noThree : NoThreeCollinear (shearSel p)`.
- Bricks proven axiom-clean: `shear_two_ne` (2x+1 unit off pole), `shear_curve` ((2x+1)·y=1 mod p),
  `shearY_lt`. Plus the full geometry toolkit from prior laps.
- `Anchors.lean` native_decide-certifies `NoThreeCollinear (shearSel p)` at p=7,11,13.
- Aristotle job `1c2a55b7` (`aris-hjsw-shear`) running the pure-arithmetic form
  (`shearSel_decNoThree`: every distinct triple has `detZ ≠ 0`) — self-contained, no reals.

## The ONLY open item (as of latest commit)

**`shearSel_cross_diag`** (`Hyperbola.lean`) — the lone `sorry`, the irreducible slope-`±1` core.
The entire tower is machine-checked above it:
`hjsw_lower` ⟸ `shearSel_noThree` ⟸ `shearSel_intdet` ⟸ `shearSel_two_lifts_line` ⟸
`shearSel_cross_column` ⟸ `shearSel_cross_diag`, with `shearSel_card`, `shearSel_grid`,
`shearSel_mem_curve`, `shearSel_share_residue`, `shear_curve`, `shearY_injective`,
`shearSel_{y,x}res_of_{x,y}res`, `lift_triple_noncollinear` all axiom-clean — AND the slope-`0`/`∞`
cross-column cases now discharged inside `shearSel_cross_column`.

`shearSel_cross_diag`: `P,Q` two kept lifts of one column differing in BOTH coordinates (so a
diagonal `{A,D}` or antidiagonal `{B,C}` slope-`±1` pair), `R` a kept lift of a DIFFERENT column —
never collinear. This is the genuine HJSW combinatorial heart.

**Proof plan for `shearSel_cross_diag`:** `P,Q` differ by `p` in both coords (by
`coord_diff_of_residue_eq`), so they are the diagonal `{A,D}` (line `Y−X = sₐ−a`, slope `+1`) or
antidiagonal `{B,C}` (line `Y+X = sₐ+a+p`, slope `−1`) pair of column `a`. Both being kept pins the
drop: diagonal kept ⟺ `a,sₐ` opposite sides of `pl` (dropped corner `B`/`C`); antidiagonal kept ⟺
same side. `R` on that line ⇒ `R.2−R.1 = sₐ−a` (resp `R.2+R.1 = sₐ+a+p`) as integers ⇒
`s_c−c ≡ sₐ−a (mod p)` with `c` the slope-`±1` partner column (an explicit Möbius relation via the
curve `(2x+1)y≡1`). The contradiction: the corner of column `c` that lands on this line is exactly
`c`'s DROPPED corner (so `R` cannot be a kept lift there) — unless `c=a`. Formalize by extracting
columns from `mem_shearKept`, casing the 4 corners of each, and the `shearDrop` if-conditions +
`intCoord_diff_factor`. Aristotle job `1c2a55b7` is grinding the superset `shearSel_intdet`; if it
returns without the counting, resubmit the tighter `shearSel_cross_diag`.

### (superseded) earlier plan — reduction → 4 line-counts:
   - Each P,Q,R ∈ `shearSel p` is a kept lift of a column; for x≠pl, `shear_curve` puts its residue
     on `(2x+1)y=1`. Apply `shear_hyperbola_lift_share_residue` ⇒ two share a residue ⇒ same column
     (first coord <2p determines column mod p). If all three same column ⇒ `lift_triple_noncollinear`
     kills it. Else two-in-a-column + one other ⇒ line slope ∈ {0,∞,±1}.
   - slope 0 / ∞: impossible because `shearY` is **injective** (need a `shearY_injective` lemma:
     `2x+1` injective on `[0,p)`-residues, inverse injective) ⇒ distinct rows AND columns ⇒ each
     integer row/column has ≤2 points.
   - slope ±1: the closed-form drop rule guarantees ≤2 per slope-±1 integer line. This is the genuine
     remaining content — reduce to modular arithmetic via `coord_diff_of_residue_eq` /
     `intCoord_diff_factor`. (Diagonal pair kept ⟺ r,s opposite sides of pl; antidiagonal pair kept
     ⟺ same side — so each column doubly-loads exactly one slope-±1 line, and no two columns collide.)

Single-crux target ⇒ "broaden" mostly means *broaden the attack on this crux*.

## Reduction toolkit shipped this lap (axiom-clean, `Hyperbola.lean`)
The geometric half of any lift-based HJSW proof is now done:
- `collinear_imp_modp_det_zero` — **construction-agnostic**: real-collinear grid points ⇒ their
  residues' `2×2` determinant vanishes in `ZMod p` (ℤ→ZMod p is a ring hom). Works for ANY base.
- `hyperbola_collinear_zmod` — mod-`p` Vandermonde core over the field `ZMod p`.
- `hyperbola_lift_collinear_share_residue` — real-collinear triple of hyperbola-lifts ⇒ two share a
  residue mod `p` (= two lifts of one base point). Reduces no-three to a slope-`±1` condition.
- `coord_diff_of_residue_eq` — two grid coords in `[0,2p)` congruent mod `p` differ by `0` or `p`.

**What remains for the headline = purely combinatorial:** choose which lifts to keep so that no
slope-`±1` line carries 3 chosen points. (Slope `0`/`∞` are automatically safe when the base has
distinct x- and y-residues; only slope `±1` is dangerous.)

## NEW structural result this lap (rigorous + computationally confirmed)
**Uniform "3 of the 4 lifts of a single modular hyperbola `xy ≡ k`" reaches `3(p−1)` iff `p = 5`.**
Proof sketch (k = 1; recorded in `ON-LINE-REQUEST.md`): the only collinear triples are
"2 diagonal lifts of `P_a` + 1 of its slope-`+1` partner `P_{−a⁻¹}`" (line `y = x + (a⁻¹−a)`) or the
anti-diagonal analogue with the slope-`−1` partner `P_{a⁻¹}`. Avoiding a triple forces **both**
endpoints of each collision pair to drop a (anti-)diagonal lift; but a base point sits in one
slope-`+1` pair AND one slope-`−1` pair, so it must drop a diagonal **and** an anti-diagonal lift —
two drops — while 3-of-4 drops only **one**. The only escape is an involution fixed point: the
slope-`−1` constraint is void when `a² = k` (partner = self, line has only 2 points), the slope-`+1`
constraint void when `a² = −k`. For `p = 5` **every** `a ∈ {1,2,3,4}` is a fixed point of one
involution (`a²=1`: a=1,4; `a²=−1`: a=2,3), so all points are singly-constrained ⇒ feasible. For
every other prime ≥ 7 some base point is doubly-constrained ⇒ infeasible.
Verified: `test(5)=True`, `test(7)=False` by exhaustive `4^(p−1)` search.

**Stronger (from prior lap, still holds):** even *non-uniform* single-hyperbola lifts cap at `≤ 17`
at `p=7` (min hitting set of the collinear-triple hypergraph is `≥ 7`). And this lap's probe
confirms **no** structured single base reaches the count at `p=7`: hyperbola `xy=k` (all k),
rotated hyperbola `y²−x²=c`, circle `x²+y²=c`, monomial graphs `y=x^m` (m coprime to p−1),
translated hyperbola `(x+1)(y+1)=k`, parabola `y=x²` — all `< 18`. (`p=5` hits are small-case
coincidences, explained by the iff above.)

**Bottom line (corrected later this lap):** the prior conclusion "need ≥2 curves" was an artifact
of only ever testing the **|B| = p−1** plain hyperbola + uniform 3-of-4. A single base of size
**|B| = p** DOES work — see the breakthrough below.

## ⭐ BREAKTHROUGH this lap — the SHEARED HYPERBOLA construction (|B| = p, validated p=7,11,13)
A fresh exhaustive scan over "one-point-per-column, distinct-rows" bases (graphs of permutations
`f : Z_p → Z_p`) found **984 of 5040** such bases at `p=7` whose 4-lift union contains an 18-point
no-3-collinear set. Among the *uniformly-defined* (all-`p`) families, **Möbius / conic bases work**.
The cleanest:

> **`base = { (x, (2x+1)⁻¹ mod p) : x ∈ Z_p }`** — the sheared hyperbola `y·(2x+1) ≡ 1 (mod p)`,
> with the pole `x = −2⁻¹` mapped to `0`. `|B| = p`. Its `4p` lifts into `[0,2p)²` contain a
> `3(p−1)`-point no-3-collinear subset. **Verified REACH at p = 7, 11, 13** (and others:
> `(a,b,c,d) ∈ {(0,1,2,1),(0,1,4,2),(1,1,2,4),(2,3,1,3),(2,1,4,0)}` all reach p=7,11,13).

Why the shear matters: the plain hyperbola `xy≡1` (|B|=p−1) caps at 17 because every base point is
over-constrained by its slope-`±1` partners (the iff-p=5 result). The shear `x ↦ 2x+1`
**redistributes** the slope-`±1` collisions (the lift structure is NOT shear-invariant — lifts are
tied to the `2p×2p` grid), and the extra pole point (`|B|` goes p−1 → p) relieves the deficit.
NB: plain hyperbola + origin (`xy=1 ∪ {(0,0)}`) does NOT work — the shear is essential.

Still open: the lift **selection rule is non-uniform** (a found p=7 selection keeps 3,2,3,1,3,4,3
lifts across the 7 base points; uniform 3-of-4 = 21 pts does NOT exist for ANY of the winning bases
`(0,1,2,1),(0,1,4,2),(1,1,2,4),(2,3,1,3),(2,1,4,0)`). So the count is intrinsically `3(p−1) = 3p−3`,
a **deficit of 3** below "3 per base point" — and a *closed-form* selection rule is not yet pinned.

**Collision-graph structure of the sheared base (for the rule search):** classify base points by
`y−x mod p` (slope-`+1` classes) and `y+x mod p` (slope-`−1`). At `p≡1 (mod 4)` (e.g. p=13) all
classes have size ≤2 (clean); at `p≡3 (mod 4)` (p=7,11) there is a **size-3 class** on each side —
those are where the deficit/over-constraint concentrates. A character-only rule
(keep-set by `χ(2x+1) ∈ {+1,−1,0}`) does NOT work (tested p=7,11). The rule must use the
collision-class structure, likely splitting on `p mod 4` and the size-3 classes. **This is the heart
of the HJSW combinatorics** — the realistic next-lap target (or await Aristotle `083292d5` / paper).

## Three attack paths for `hjsw_lower`

### Path A — get the real construction from the HJSW 1975 paper (filed; network-blocked)
`ON-LINE-REQUEST.md` asks for the explicit point set + cross-curve non-collinearity proof, now
sharpened with the over-constraint analysis (so the fulfiller knows exactly what to extract).
When `ON-LINE-FINDINGS-*.md` lands: build the candidate set, validate via `native_decide (decNoThree …)`
at p=5,7,11,13, port to a clean `def`, prove using the reduction toolkit (the new content is then
just the slope-`±1` combinatorics, the geometry being discharged). Highest-confidence path.

### Path B — ⭐ PRIMARY now: pin down the sheared-hyperbola selection rule, then prove
The base is found (sheared hyperbola, above). The remaining work is the **lift-selection rule** +
the general proof. Concrete next steps:
1. **Find a closed-form selection** for `base = {(x,(2x+1)⁻¹)}`: search for a selection of `3(p−1)`
   lifts that is *symmetric* (e.g. invariant under an involution of the base, or given by a simple
   per-`x` rule on the residue/quadratic-character of `2x+1`) and validate at p=7,11,13,17. The
   hitting-set found arbitrary selections; we need a *rule*. Try: keep lifts by a rule depending on
   `χ(2x+1)` (quadratic character) and the slope-`±1` partner structure of the sheared base.
2. **Generalize the non-collinearity proof**: the reduction toolkit (`collinear_imp_modp_det_zero`)
   already handles cross-residue triples for ANY base; `shear_hyperbola_lift_share_residue` does the
   sheared base. Two clean geometric pieces remain (both provable now, independent of the selection
   rule, good warm-up lemmas):
   (i) **`lift_triple_noncollinear`** (the same-base-point case) — ✅ **DONE this lap, axiom-clean**
       (`Hyperbola.lean`): 3 distinct grid points in `[0,2p)²` pairwise congruent mod `p` are never
       collinear (3 distinct corners of a `p×p` rectangle ⇒ integer det `= ±p² ≠ 0`; via
       `intCoord_diff_factor` + `decide` on the `{0,1}`-determinant). **So the GEOMETRY is COMPLETE**:
       cross-base triples → impossible (`*_lift_share_residue`); same-base triples → impossible
       (`lift_triple_noncollinear`). The only open obligation is now purely combinatorial.
   (ii) Remaining: a **capstone** `NoThree S ⟸ (residues on base) ∧ (no slope-±1 cross-base triple)`
       (assembly of the two proven cases — straightforward but has 3-fold pair symmetry), and the
       **selection rule** that discharges the slope-`±1` condition (reduce it to arithmetic via
       `coord_diff_of_residue_eq`). The selection rule is the sole research crux left.
3. Validate any candidate rule via `native_decide (decNoThree …)` at p=5,7,11,13 before the proof.
Fallback: if no clean rule emerges, the Aristotle job (`083292d5`, self-contained HJSW) may return
a construction to port.

### Path C — special-case ladder (partial, native-certified) while A/B mature
Verified witness ladder p=5,7,11,13 (`hjsw_lower_{five,seven,eleven,thirteen}`, native_decide, OFF
headline). Extend to p=17,19 only if a lap needs filler; do NOT generalize to the headline.

## Done this lap
Reduction toolkit (4 axiom-clean lemmas); over-constraint theorem (3-of-4 iff p=5, proven +
verified); computational wall map; **the sheared-hyperbola breakthrough** (a uniformly-defined
|B|=p base reaching 3(p−1) at p=7,11,13, overturning the prior "need ≥2 curves" belief); submitted
the self-contained HJSW to Aristotle (`083292d5`). **Next lap:** Path B step 1 — find a closed-form
selection rule for the sheared hyperbola (validate p=7,11,13,17), then prove via the toolkit. Also
check `aristotle list` for `083292d5` and any `ON-LINE-FINDINGS-*.md`.

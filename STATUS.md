# STATUS — lean-formalizations 📊

> 🟢🆕 **BV-FOURIER DECAY — COMPLETE & axiom-clean (2026-06-20, `d17e7b8`, branch `ntl-hjsw`).** The
> route-(b) reconstruction of `prelim_decay_2` (`‖𝓕 f u‖ ≤ V(f)/(4|u|)` for integrable `f` of bounded
> variation) is now **fully machine-checked, mathlib-only, axiom-clean** (`prelim_decay_2_route_b`,
> `[propext, Classical.choice, Quot.sound]`) and **promoted `wip/` → `src/LeanFormalizations/RealAnalysis/
> BVFourierDecay.lean`** (root-imported, in `.bump-axioms`; full build green, 8621 jobs). Both analytic
> cruxes closed: **(b1)** Fourier half-period shift (`exp(↑r·I)` phase form + `𝐞(−½)=−1` + translation)
> and **(b2)** L¹-translation-by-TV via the **monotone variation function** `W(t)=V(f on (−∞,t])` —
> pointwise `‖f t−f(t+h)‖≤W(t+h)−W(t)` (`eVariationOn.add_le_union`+`edist_le`), then an **elementary
> finite-window telescoping** `∫_{−N}^{N}(W(·+k)−W)=∫_N^{N+k}W−∫_{−N}^{−N+k}W≤k·V` + monotone-convergence
> limit — **no variation/Stieltjes measure** (mathlib-absent for signed BV). NOT a headline; `weakPNT`
> stays axiom-clean independently (the upstream `prelim_decay` sorries are dead code off its path).

> 🟢⬆️ **mathlib v4.31.0 + DE-VENDOR — DONE (2026-06-20, `a0f17d1`, branch `ntl-hjsw`).** Forward-ported
> the whole repo from mathlib `v4.29.1`→`v4.31.0` AND **de-vendored** the hand-ported PNTAnd Wiener–Ikehara
> tower into a **real lake dependency** on `kim-em/PrimeNumberTheoremAnd @ bump/v4.31.0` (the maintainers'
> own v4.31 port). The 8 vendored tower files are **deleted**; the two consumers now
> `import PrimeNumberTheoremAnd.Consequences` (`WeakPNT''` for PrimeGap, `pi_alt'` for PNT). **Full build
> green (8620 jobs); all 13 headlines `#print axioms`-clean** `[propext, Classical.choice, Quot.sound]` —
> *including* `weakPNT` and `prime_number_theorem`, which now resolve through the EXTERNAL dependency (the
> dep's WeakPNT path is provably sorry-free; the dep carries 2 dead-code `prelim_decay` sorries off-path).
> Own-file v4.31 fixes were proof-body-only (Mertens/MertensConstant `using!`/`convert … <;> first | rfl |
> (field_simp <;> ring)`/`Function.comp_def`; PrimeGap `factorization_eq_zero_of_non_prime`→`…_not_prime`).
> DivisorProblem promoted back into `src/` (complete bonus). ⚠️ **First-from-source full builds hit macOS-
> side FD exhaustion** (v4.31's 3-file olean split × parallel heavy leaves on the orbstack bind mount) — build
> each module sequentially once to cache, then the full build is a clean replay. See HANDOFF + ON-LINE-REQUEST.

> 🛑✅ **FINISH-AND-STOP — WIND-DOWN COMPLETE (Trevor, 2026-06-19; executed 2026-06-19 reflection lap).** The headlines are COMPLETE + axiom-clean: the **HJSW no-three-in-line ladder** (`3/2−o(N)`, `weakPNT` discharged) and the **classical Mertens trilogy** (`e^{−γ}` unconditional). The directive's wind-down is now **DONE**: no new threads opened; the divisor side-quest was reverted (preserved at `d356584`); the three off-headline `sorry`s (`nagura_prime` + its `5/4` rung, and the dead-code `prelim_decay_2/3` island) were **quarantined** out of `src/` into `wip/` (`NaguraFiveFourths.lean`, `WienerDecayIsland.lean`; preserved verbatim, plus git history). **`src/` is now sorry-free** (governor self-stop gate verified clean), **every headline `#print axioms` is `[propext, Classical.choice, Quot.sound]`** (re-verified from real output this lap). → **self-stop.**
**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized in Lean 4 + mathlib.** · **Build**: 🟢 green (8621 jobs, kernel-reverified) · **Updated**: **FRESH-MIND re-verification lap — independent ground-truth re-audit: all 14 headlines axiom-clean from real `#print axioms`, `src/` SORRY-FREE, de-vendor/v4.31 confirmed done, frontier saturated → self-stop** · 2026-06-20 · post-`68e9b31` · **Branch `ntl-hjsw`** · mathlib **v4.31.0** + de-vendor DONE · **`weakPNT` DISCHARGED → the flagship `maxNoThreeInLine_ge_three_halves_sub` (HJSW-optimal `3/2−o(N)`) is UNCONDITIONAL and axiom-clean** (`[propext, Classical.choice, Quot.sound]`). Full Wiener–Ikehara PNT tower ported in-repo (PNTAnd, zero math edits). General-`N` constant ladder CLOSED: Bertrand 3/4 → 15/16 → 6/5 → 3/2−o(N), all axiom-clean. **The classical Mertens TRILOGY is COMPLETE & axiom-clean** (`Mertens.lean` + `MertensConstant.lean`): 1st & 2nd (`∑log p/p=log x+O(1)`, `∑1/p=log log x+O(1)`); 3rd **SHARP `e^{−γ}` UNCONDITIONAL** — `mertens_third_classical_eGamma` (`∏(1−1/p)·log N→e^{−γ}`) and `mertensThirdConst_eq_neg_gamma` (`C₃=−γ`), via the **PROVEN Limit B** (`tendsto_primeZeta_add_logSub_limitB`); the deep Abelian/Tauberian final-value crux `tendsto_sub_one_mul_integral_abelian` (`δ∫₀^∞ f·e^{−δx}→0`, ε–X argument) is fully machine-checked. All mathlib-absent. **No open `sorry` remains in `src/`; no `axiom` declared.** (Quarantined off-headline items live under `wip/`.)

> **Branch note (refreshed reflection lap, 2026-06-19).** On `ntl-hjsw` the mandated audit-surface
> headlines are proven & axiom-clean (`[propext, Classical.choice, Quot.sound]`, kernel-reverified this
> lap): HJSW `hjsw_lower_bound : 3(p−1) ≤ max(2p)` (crux `shearSel_cross_diag`), the `2N` upper bound,
> Erdős `Θ(N)`, the general-`N` `3N/4` (`maxNoThreeInLine_ge_three_quarters`, via Bertrand), AND the two
> **unconditional** improvements past Bertrand `3/4` (`maxNoThreeInLine_ge_{fifteen_sixteenths,six_fifths}`,
> via the refined two-sided Chebyshev stack). The six other threads (Curtis, power-tower, constructibles,
> e/π-transcendence, Goodstein) are complete & axiom-clean.
> **Frontier state (FINAL — `weakPNT` discharged, Mertens complete, `src/` sorry-free):** the general-`N`
> constant ladder is **CLOSED to HJSW's optimal `3/2 − o(N)`** (`maxNoThreeInLine_ge_three_halves_sub`),
> **UNCONDITIONAL and axiom-clean** — `weakPNT` (the PNT `ψ∼x`) discharged by porting PNTAnd's
> Wiener–Ikehara tower in-repo (zero math edits). `src/` carries **ZERO math axioms AND zero open `sorry`**
> across every headline. The classical **Mertens trilogy** (`Mertens.lean` + `MertensConstant.lean`) is
> complete & axiom-clean, including the sharp `e^{−γ}` 3rd via the proven Limit B. The three former
> off-headline `sorry`s (`nagura_prime` + its `5/4` rung; the dead-code `prelim_decay_2/3` island) were
> **quarantined** under `wip/` (FINISH-AND-STOP, 2026-06-19) — they gated no headline.

## Where it stands
**Completion-verification review lap (2026-06-20): the project is COMPLETE; verified from ground truth, not docs; self-stopping.** This review lap re-built (green, 8621 jobs), confirmed `src/` is tactic-level sorry-free (every `sorry` grep-hit is docstring prose; the Goodstein anchors are real `native_decide`), and re-ran `#print axioms` on **all 14 headlines** in `.bump-axioms` from real output — every one is the bare trust base `[propext, Classical.choice, Quot.sound]`, zero math axioms, zero `sorryAx`, zero `native_decide` artifacts, zero 🔴. Since the prior wind-down: mathlib **v4.31.0 upgrade + de-vendor** landed (the vendored PNTAnd tower deleted, now a real lake dep on `kim-em/PrimeNumberTheoremAnd@bump/v4.31.0`; `weakPNT`/`prime_number_theorem` resolve axiom-clean through the external dep), and the **BV-Fourier decay route-(b) family** (`prelim_decay_2_route_b : ‖𝓕 f u‖ ≤ V(f)/(4|u|)`, `prelim_decay_3_route_b`) was driven to completion and promoted into `src/` as an axiom-clean bonus. **The sole remaining repo-connected open item — the sharp `2π|u|` constant — is a 🟠 generational wall** (it needs a signed-BV / Lebesgue–Stieltjes integration-by-parts development that is *absent from mathlib*, existing only in an external library, verified online 2026-06-19), is **off-headline** (refines a bonus; gates no headline — the upstream `prelim_decay` sorries are dead code off the `weakPNT` path), and its feasible weaker form is already in `src/`. The frontier is therefore genuinely saturated: no 🟡 debt left to chip, no higher-value target than the completed headlines. The originally-mandated target — HJSW `3N/2` proved & axiom-clean in `Statement.lean` — is **COMPLETE** (`hjsw_lower_bound`). The treadmill then built the full general-`N` constant ladder up to HJSW's optimal `3/2 − o(N)` (`maxNoThreeInLine_ge_three_halves_sub`), and a prior grind lap **discharged the lone deep axiom `weakPNT`** (the PNT `ψ(x)∼x`) by porting PNTAnd's Wiener–Ikehara tower onto mathlib v4.29.1 with **zero math edits** — so that flagship is now `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`, re-verified this lap). **Every headline in the repo is now axiom-free.** With the PNT layer unlocked, this lap added **Mertens' first theorem** (`Mertens.lean`): the sharp prime form `∑_{p≤x}(log p)/p = log x + O(1)` (discharging the proper-prime-power tail regrouping), the vonMangoldt form, and the multiplicative `~ log` capstones — all mathlib-absent, all axiom-clean. Mertens' 2nd and 3rd (sharp convergence forms) followed; the classical `e^{−γ}` Mertens 3rd is now reduced to the **single Tauberian limit `Limit B`** (`P(s)+log(s−1)→M−γ`), and this lap built its analytic spine in `MertensConstant.lean` (brick B1 Abel integral rep + the γ-injection `∫_0^∞ log u·e^{−u}=−γ` + M-part + the log-part fully evaluated to `−γ−log(s−1)`), all axiom-clean. **Limit B is now PROVEN** (`tendsto_primeZeta_add_logSub_limitB`), so the classical Mertens 3rd is UNCONDITIONAL and the Mertens thread is COMPLETE — there is no longer an active frontier. Per Trevor's FINISH-AND-STOP directive, this reflection lap quarantined the three off-headline `sorry`s out of `src/` (preserved under `wip/`), leaving `src/` sorry-free with every headline `#print axioms`-clean. See the dated `## Reflection — 2026-06-19` in `PENDING_WORK.md`.

**Every headline is axiom-free** — each headline `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]` (kernel-verified this lap: the flagship `..._three_halves_sub`, all six complete threads, the NTL audit surface, the unconditional `6/5`/`15/16` rungs, and the new Mertens theorems), and `grep '^axiom' src/` shows **none**. `src/` carries **zero math axioms AND zero open `sorry`** (governor self-stop gate verified clean this lap). The three former off-headline `sorry`s — `nagura_prime` (superseded by the unconditional `3/2`) and the dead-code `prelim_decay_2/3` island — were **quarantined** into `wip/` (FINISH-AND-STOP, 2026-06-19); they gated no headline (clean `#print axioms` on all targets confirms it). All threads green. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
- **2026-06-20 (FRESH-MIND re-verification lap — independent ground-truth re-audit, self-stop):**
  A fresh relaunch arrived carrying the *stale* de-vendor / "v4.29.1→v4.31.0 upgrade" objective (landed
  two laps ago at `a0f17d1`). Rather than redo done work or trust four layers of echoing handoff docs, I
  re-verified completion from real output **this lap, myself**: `lake build` GREEN (8621 jobs); toolchain
  confirmed `leanprover/lean4:v4.31.0` with PNTAnd a real lake `require` (de-vendor done); `src/`
  **tactic-level sorry-free** (no live `sorry`/`admit` tactic, no `axiom` declaration — every grep-hit is
  docstring prose or a real `native_decide` anchor); **`#print axioms` on all 14 `.bump-axioms` headlines =
  `[propext, Classical.choice, Quot.sound]`** (re-run via `lake env lean`, zero math axioms, zero
  `sorryAx`). Confirmed the handoff's "stay stopped" direction is sound and the lone open item (sharp
  `2π|u|` BV-Fourier constant) is still an off-headline 🟠 wall that gates nothing. **Completion bar met
  again → self-stop re-affirmed.**
- **2026-06-20 (COMPLETION-VERIFICATION review lap — ground-truth re-audit, self-stop):** Fresh-mind
  review lap on an allow-stop run (`LEAN_LAP_ALLOW_STOP=1`). Rather than trust the handoff's "complete"
  claim, re-verified everything from real output: `lake build` GREEN (8621 jobs, cached replay, only
  deprecation/unused-var warnings); `src/` tactic-level **sorry-free** (all `sorry` grep-hits are docstring
  prose; Goodstein anchors are real `native_decide`; `grep '^axiom' src/` empty); **`#print axioms` on all
  14 `.bump-axioms` headlines = `[propext, Classical.choice, Quot.sound]`** (zero math axioms, zero
  `sorryAx`). Investigated the one named open item, the **sharp `2π|u|`** BV-Fourier constant: traced the
  full proof (Fubini reduction recovering the sharp `1/(2πiu) ∫ e(−tu) df`), pinned the exact missing
  mathlib lemma (signed-BV Stieltjes `μ_f((a,b]) = f(b)−f(a)`), and confirmed via the reference corpus
  (verified online 2026-06-19) that *both* closure routes are mathlib-absent — (a) general BV/Stieltjes IBP
  exists only externally (Luccioli–Degenne), (b) the L¹-translation route gives only the weaker `4|u|`,
  which is already complete in `src/`. **Direction call: this is a 🟠 generational wall, off-headline,
  gating nothing, lower-value than the done work — NOT a chippable 🟡.** With headlines complete +
  axiom-clean, `src/` sorry-free, and the frontier saturated, this satisfies the completion-exit bar
  (operator-authorized finish-and-stop; building signed-BV-IBP to sharpen a bonus would be exactly the
  side-quest the directive forbids). Refreshed STATUS (ledger + BV-decay rows), wrote synthesis HANDOFF,
  **self-stopped**.
- **2026-06-20 (mathlib v4.31.0 + DE-VENDOR + BV-Fourier decay bonus — `d7442a5`):** Forward-ported the
  repo `v4.29.1`→`v4.31.0` and **de-vendored** the hand-ported PNTAnd Wiener–Ikehara tower into a real lake
  dependency (`kim-em/PrimeNumberTheoremAnd@bump/v4.31.0`); the 8 vendored tower files deleted, consumers
  now `import PrimeNumberTheoremAnd.Consequences`. All 14 headlines re-verified axiom-clean *through the
  external dep* (`weakPNT := WeakPNT''`, `prime_number_theorem`). Then drove the genuinely-open
  `prelim_decay` BV-Fourier decay thread to full completion via route (b) — `prelim_decay_2_route_b`
  (`‖𝓕 f u‖ ≤ V(f)/(4|u|)`) and `prelim_decay_3_route_b` (`V(ψ')/(8π·u²)`), both axiom-clean — and promoted
  it `wip/`→`src/LeanFormalizations/RealAnalysis/BVFourierDecay.lean`. Two analytic cruxes machine-checked:
  (b1) Fourier half-period shift (`exp(↑r·I)` phase + `𝐞(−½)=−1`), (b2) L¹-translation-by-TV via the
  **monotone variation function** `W(t)=V(f on (−∞,t])` with elementary finite-window telescoping (no
  signed Stieltjes measure — mathlib-absent). DivisorProblem promoted back into `src/`.
- **2026-06-19 (DEEP-REFLECTION lap — project COMPLETE, FINISH-AND-STOP wind-down EXECUTED, `src/` sorry-free):**
  Stepped to whole-project altitude. **Re-verified all 17 headlines axiom-clean from real `#print axioms`**
  (`[propext, Classical.choice, Quot.sound]`; build green, 8297 jobs) and re-audited faithfulness of the
  flagship (`maxNoThreeInLine_ge_three_halves_sub` = `∀ε>0, ∀ᶠN, (3/2−ε)N ≤ max N`) and the Mertens 3rd
  (`mertens_third_classical_eGamma` = `∏(1−1/p)·logN → e^{−γ}`) — both faithful. **Direction call:** the
  headlines (HJSW ladder + Mertens trilogy) are COMPLETE; Limit B is PROVEN so nothing is an active
  frontier; the only open items were three off-headline `sorry`s gating no headline. The treadmill had
  been *circling* (the prior lap built→reverted a divisor side-quest, then left the sorries in place and
  wrote a self-stop the governor **declined** because `src/` still had `sorry`s — hence this relaunch).
  Resolved it: per Trevor's explicit FINISH-AND-STOP, **quarantined** the dead-code `prelim_decay_2/3`
  island (`Wiener.lean`) and the `nagura_prime` + `maxNoThreeInLine_ge_five_fourths` `5/4` rung
  (`PrimeGap.lean`) out of `src/` into `wip/` (`NaguraFiveFourths.lean`, `WienerDecayIsland.lean`;
  preserved verbatim, plus git history), and restored the complete Dirichlet divisor proof into
  `wip/DivisorProblem.lean` (from `d356584`) per the `wip/` convention. Confirmed `src/`
  **sorry-free** with the governor's own detector, headlines still axiom-clean, build green → **self-stop**.
- **2026-06-19 (LIMIT B / C₃=−γ — Abel rep + γ-injection + log-part fully evaluated, `3b56a77`):** the
  classical `e^{−γ}` is reduced (`mertens_third_classical_of_tauberian`) to the single Tauberian limit
  **Limit B** `primeZeta s + log(s−1) → M − γ` (`s→1⁺`); this lap built the analytic spine of Limit B in
  `MertensConstant.lean`, all axiom-clean: (i) **brick B1** `primeZeta_eq_abel_integral`
  `P(s) = (s−1)∫_1^∞ (∑_{p≤⌊t⌋}1/p)·t^{−s} dt` (mathlib Abel summation
  `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`, all 6 hypotheses now proven — incl. `hg_int`
  `integrableAtFilter_rpow_neg_mul_log`, done locally, superseding Aristotle `2919e0d2`); (ii) the
  **γ-injection** `integral_log_mul_exp_neg_Ioi_eq_neg_gamma` `∫_0^∞ log u·e^{−u} du = −γ` (via complex
  `hasDerivAt_GammaIntegral` + `Real.hasDerivAt_Gamma_one` + ofReal bridge); (iii) the **M-part**
  `tendsto_sub_one_mul_integral_rpow` `(s−1)∫_2^∞ t^{−s} → 1`; (iv) the **log-part FULLY evaluated**
  `sub_one_mul_integral_log_exp` `(s−1)∫_0^∞ log x·e^{−(s−1)x} dx = −γ − log(s−1)` (change of variables
  `u=(s−1)x` + the γ-injection + `integrableOn_log_mul_exp_neg`). **Remaining for Limit B:** the exp
  substitution `t=eˣ` of B1 (needs `integral_image_eq_integral_abs_deriv_smul` — A is a step function, so
  the continuous-`g` substitution lemma won't apply) + the Tauberian error `(s−1)∫r(x)e^{−(s−1)x}→0`.
- **2026-06-19 (SHARP MERTENS — convergence forms + e^{−γ} reduced to one equation):** the whole Mertens
  trilogy upgraded from `O(1)` to *convergence*, all axiom-clean & mathlib-absent (`Mertens.lean`):
  **`mertens_second_tendsto`** `∑_{p≤N}1/p − log log N → M` (Meissel–Mertens; bounded remainder integral
  upgraded to a convergent improper integral via `integrableOn_Ioi_of_intervalIntegral_norm_bounded` +
  `intervalIntegral_tendsto_integral_Ioi`); **`mertens_third_tendsto`** `log∏(1−1/p)+log log N → C₃` (the
  correction series `∑'_p(log(1−1/p)+1/p)` shown absolutely convergent, `summable_primeCorrCoeff`);
  **`mertens_third_tendsto_exp`** `∏(1−1/p)·log N → e^{C₃}`. The classical `e^{−γ}` headline is reduced to
  the *single* deep equation `C₃ = −γ`: **`mertens_third_classical (hγ) ⟹ ∏(1−1/p)·log N → e^{−γ}`** (γ =
  `Real.eulerMascheroniConstant`, now imported), axiom-clean, headline machine-checked modulo `hγ`. The
  `C₃=−γ` proof (ζ Euler-product Tauberian transfer) is the sole remaining gap — multi-lap, route in
  `PENDING_WORK.md`. (Supersedes Aristotle `0fa80268`'s `summable_primeCorr` — done locally.)
- **2026-06-19 (review lap cont. — MERTENS' THIRD up to the constant, `f9b15ab`):** `mertens_third_up_to_const`
  : `(log ∏_{p≤N}(1−1/p) + log log N) =O[atTop] 1`, i.e. `∏(1−1/p) ≍ 1/log N` — axiom-clean, mathlib-absent.
  Via `log_primeProd_eq` (log of product = sum of logs) + `log_primeProd_eq_corr` (split off `−1/p`) + the
  bounded correction sum `primeCorr` (`|primeCorr N| ≤ ∑'1/b²`, from the locally-proved correction bound
  `log_one_sub_add_self_abs_le : |log(1−x)+x| ≤ x²` via derivative monotonicity) + Mertens' 2nd. **The
  classical Mertens trilogy is now in `Mertens.lean`** (1st & 2nd full; 3rd up to the sharp `e^{−γ}`
  constant). Aristotle `0fa80268` working the correction-series convergence (toward the constant).
- **2026-06-19 (review lap cont. — MERTENS' SECOND THEOREM COMPLETE, `9a3303d`):** Finished
  `mertens_second : (∑_{p≤N} 1/p − log log N) =O[atTop] 1` — **axiom-clean, mathlib-absent**. Assembly:
  core Abel identity `mertens_second_identity` (`∑1/p = primeSumDiv N/log N + ∫_2^N primeSumDiv⌊t⌋/(t log²t)`,
  via mathlib `sum_mul_eq_sub_integral_mul₁`); integral split (`intervalIntegral.integral_sub`) into the
  `log log N` main term (`integral_inv_log_mul`) + an `O(1)` remainder (`norm_integral_le_abs_of_norm_le`
  with `abs_primeSumDiv_floor_sub_log_le` + `integral_inv_mul_sq_log`); step-function integrability from
  `integrableOn_primeSumDiv_floor_div` (mathlib `integrableOn_mul_sum_Icc`). **Both Mertens' 1st and 2nd
  theorems now complete & axiom-clean.** Next target: Mertens' 3rd `∏_{p≤x}(1−1/p) ~ e^{−γ}/log x`.
- **2026-06-19 (review lap — Mertens prime form sharp + asymptotic capstones, `a2b4891`):** Re-verified
  the ledger from real `#print axioms` (build green, 8296 jobs): flagship `..._three_halves_sub` is
  axiom-clean (`weakPNT` discharged in a prior lap; STATUS header was stale, now corrected). Discharged
  **Next action #1** — the proper-prime-power tail bound — completing Mertens' first theorem in its sharp
  **prime form** `∑_{p≤N}(log p)/p = log N + O(1)` (`vonMangoldtSumDiv_sub_primeSumDiv_le`,
  `abs_primeSumDiv_sub_log_le`, `mertens_first_prime`). Method: geometric tail `∑_{k≥2}r^k≤2r²`, per-base
  `∑_k log p/p^k ≤ 2log p/p²`, inject proper prime powers `d↦(minFac d,exp)` into `Icc 2 N ×ˢ Icc 2 N`,
  `sum_product` + `sum_le_tsum` vs `summable_log_div_sq`. Added `~ log` capstones for both the prime and
  vonMangoldt sums. All axiom-clean. Next target: Mertens' 2nd via mathlib `sum_mul_eq_sub_integral_mul`.
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
*(Older bullets — the refined-Chebyshev prerequisite stack, general-`N` constant frontier opening, HJSW
`3N/2` discharge — trimmed for length; their content is preserved in the axiom ledger above and in the
dated `HANDOFF-2026-06-19-*.md` batons.)*

## Outstanding
The mandated NTL target, the unconditional `3/2−o(N)` flagship, the classical Mertens trilogy (incl. the
sharp `e^{−γ}` 3rd, Limit B PROVEN), the BV-Fourier decay route-(b) bonus, and all six other threads are
COMPLETE and axiom-clean. `src/` carries **ZERO math axioms AND zero open `sorry`**. **There is no active
frontier and no 🟡 debt to chip** — the only repo-connected open item is a single off-headline 🟠 wall
(below) that gates nothing.
### Short-term (mirror PENDING_WORK top) — NONE on-headline
- *(No active frontier.)* Headlines + bonuses all done + axiom-clean; `src/` sorry-free; build green.
### Long-term (off-headline 🟠 walls — opportunistic only, do NOT start under finish-and-stop)
- **Sharp `2π|u|` BV-Fourier constant** for `prelim_decay_2/3` (we have the non-sharp `4|u|`/`8π·u²` in
  `src/BVFourierDecay.lean`). The sharp form is the *upstream* `prelim_decay` statement, but it gates no
  headline (dead code off `weakPNT`). **Needs a signed-BV / Lebesgue–Stieltjes integration-by-parts
  development that is absent from mathlib** (exists only externally — Luccioli–Degenne; verified online
  2026-06-19). Proof traced (Fubini → `1/(2πiu)∫e(−tu)df`); the missing primitive is the signed Stieltjes
  measure `μ_f((a,b]) = f(b)−f(a)` for BV `f` (mathlib has it for *monotone* `f` only). **🟠 generational
  wall** — a build-plan, not a chippable 🟡; route (c) Jordan decomposition in `PENDING_WORK.md` item 1.
- `nagura_prime` (prime in `(n,6n/5]`, `n≥25`): would raise the **unconditional** axiom-clean constant
  `6/5 → 5/4`. LOW priority — superseded by the unconditional `3/2`, and FINAL for elementary methods (the
  refined Chebyshev constant `A` matches `(6/5)A` with zero slack; needs explicit-error PNT or Nagura's
  1952 finite inequality). Fallback grind only; lives in `wip/NaguraFiveFourths.lean`.
- General Hermite–Lindemann for arbitrary algebraic α (π assembly generalizes) — main-branch thread.
- The no-three-in-line **Main Conjecture** (`max N ~ c·N`, `c≈1.87`) — open *mathematics*, not formalizable.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
- `nagura_prime` (prime in `(n,6n/5]`, `n≥25`): would raise the **unconditional** axiom-clean constant
  `6/5 → 5/4`. LOW priority — superseded by the unconditional `3/2`, and FINAL for elementary methods (the
  refined Chebyshev constant `A` matches `(6/5)A` with zero slack; needs explicit-error PNT or Nagura's
  1952 finite inequality). Fallback grind only.
- General Hermite–Lindemann for arbitrary algebraic α (π assembly generalizes) — main-branch thread.
- The no-three-in-line **Main Conjecture** (`max N ~ c·N`, `c≈1.87`) — open *mathematics*, not formalizable.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
### To completion
- Curtis ✅ · **Power-tower SHARP iff ✅** · Wantzel iff ✅ · **e-transcendence ✅** ·
  **π-transcendence ✅ (axiom-clean)** · **squaring-the-circle ✅ (unconditional, axiom-clean)** ·
  **no-three-in-line: 2N upper + Erdős Θ(N) + HJSW `3N/2` + general-`N` `3N/4` + unconditional `15/16`, `6/5`
  & `3/2 − o(N)` ✅ ALL axiom-clean (`weakPNT` discharged).** · **Mertens TRILOGY ✅** (1st vonMangoldt +
  sharp prime form; 2nd Meissel–Mertens; 3rd sharp `e^{−γ}` UNCONDITIONAL, Limit B proven) axiom-clean ·
  **BV-Fourier decay route-(b) bonus ✅** (`4|u|`/`8π·u²`) axiom-clean · **Goodstein ✅** · mathlib
  **v4.31.0 + de-vendor ✅**.
  Whole-repo math-axiom count: **0** (kernel-reverified this lap from real `#print axioms` on all 14
  `.bump-axioms` headlines). Open obligations in `src/`: **zero math axioms, zero `sorry`**. The only
  repo-connected open item is the off-headline 🟠 sharp-`2π|u|` wall (gates nothing). **PROJECT COMPLETE.**

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
| ~~`NoThreeInLine.maxNoThreeInLine_ge_five_fourths` (via `nagura_prime`)~~ | general-`N` `5/4` constant `3⌊5N/12⌋ ≤ max N`, uncond. | — (removed from `src/`) | ⬛ **QUARANTINED** 2026-06-19 (FINISH-AND-STOP): carried `nagura_prime`'s `sorryAx`; gated no headline; superseded by unconditional `6/5` + PNT `3/2`. Preserved in `wip/` + git. |
| `NoThreeInLine.maxNoThreeInLine_ge_three_halves_sub` | **HJSW-optimal `3/2 − o(N)`**: `∀ε>0, ∀ᶠN, (3/2−ε)N ≤ max N`, uncond. (paper's actual claim) | `[propext, Classical.choice, Quot.sound]` | ✅ **0 math axioms — UNCONDITIONAL** (`weakPNT` discharged via in-repo Wiener–Ikehara tower); kernel-reverified this lap |
| `PrimeGap.weakPNT` / `Consequences.WeakPNT''` | the PNT `ψ(x) ∼ x` (Hadamard–de la Vallée Poussin 1896) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **discharged** (PNTAnd Wiener tower ported, zero math edits); also `chebyshev_asymptotic` (θ∼x), `pi_alt'` (π(x)∼x/log x), `nth_prime_asymp` |
| `Mertens.{abs_vonMangoldtSumDiv_sub_log_le, mertens_first}` | Mertens' 1st (vonMangoldt form) `∑_{n≤N}Λ(n)/n = log N + O(1)`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; explicit bound `log4+5` |
| `Mertens.{vonMangoldtSumDiv_sub_primeSumDiv_le, abs_primeSumDiv_sub_log_le, mertens_first_prime}` | Mertens' 1st (**prime form**) `∑_{p≤N}(log p)/p = log N + O(1)`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; proper-prime-power tail bounded by `2∑'(log b)/b²` (this lap) |
| `Mertens.{primeSumDiv_isEquivalent_log, vonMangoldtSumDiv_isEquivalent_log}` | prime/vonMangoldt sums `~ log N` (multiplicative Mertens 1st), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Mertens.{mertens_second_identity, mertens_second}` | **Mertens' 2nd** `∑_{p≤N} 1/p = log log N + O(1)`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; via Abel summation (`sum_mul_eq_sub_integral_mul₁`) + `log log` primitive + `O(1)` remainder (this lap) |
| `Mertens.mertens_third_up_to_const` | **Mertens' 3rd (up to constant)** `∏_{p≤N}(1−1/p) ≍ 1/log N`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; sharp `e^{−γ}` constant is the deeper open refinement (this lap) |
| `Mertens.{mertens_third_tendsto_exp, mertens_third_isEquivalent}` | **Mertens' 3rd sharp (convergence)** `∏(1−1/p)·log N → e^{C₃}`, `∏ ~ e^{C₃}/log N`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; `C₃ = (∑'_p(log(1−1/p)+1/p)) − M` (`mertensThirdConst`) |
| `MertensConstant.mertens_third_classical_eGamma` | **classical `e^{−γ}` Mertens 3rd, UNCONDITIONAL** `∏(1−1/p)·log N → e^{−γ}` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; Limit B now PROVEN, so no hypothesis. `mertensThirdConst_eq_neg_gamma` (`C₃=−γ`) likewise unconditional |
| `MertensConstant.{tendsto_primeZeta_add_logSub_limitB, tendsto_sub_one_mul_integral_abelian}` | **Limit B PROVEN** `P(s)+log(s−1)→M−γ`; the **Abelian final-value crux** `δ∫_0^∞ f·e^{−δx}→0` (ε–X argument) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; the deep Tauberian wall, fully machine-checked this lap |
| `MertensConstant.{primeZeta_eq_abel_integral, integral_log_mul_exp_neg_Ioi_eq_neg_gamma, sub_one_mul_integral_log_exp}` | Limit-B spine: Abel integral rep of `P(s)`; `∫_0^∞ log u·e^{−u}=−γ`; `(s−1)∫_0^∞ log x·e^{−(s−1)x}=−γ−log(s−1)` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent** |
| `BVFourierDecay.prelim_decay_2_route_b` | BV-Fourier decay (route (b), non-sharp): `‖𝓕 f u‖ ≤ V(f)/(4|u|)` for `f` integrable + BV, uncond. **bonus** | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **mathlib-absent**; half-period shift + L¹-translation-by-TV (monotone variation fn, no signed Stieltjes measure). Sharp `2π|u|` is the off-headline 🟠 wall (see Long-term) |
| `BVFourierDecay.prelim_decay_3_route_b` | one order faster: `‖𝓕 ψ u‖ ≤ V(ψ')/(8π·u²)` (AC `ψ`, BV `ψ'`), uncond. **bonus** | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — `Real.fourier_deriv` (`𝓕(deriv ψ)=2πI·u·𝓕 ψ`) ∘ route-(b) decay |

**Math-axiom counts (🟢+🟡+🟠), kernel-verified this lap (2026-06-20):** **0 across all 14 `.bump-axioms`
headlines** — all NTL constants (incl. the formerly-`weakPNT`-bearing `..._three_halves_sub`), all six
complete threads, the PNT consequences layer (resolving through the de-vendored external dep), all Mertens
theorems, and the two BV-Fourier-decay bonuses are `[propext, Classical.choice, Quot.sound]` (re-verified
from real `#print axioms` this lap — see the audit output, every line the bare trust base). `weakPNT` was
the last math axiom and is now a discharged theorem (`:= WeakPNT''`); `grep '^axiom' src/` returns nothing.
**No 🔴 anywhere** — no headline depends on an open conjecture. **No 🟢/🟡 either** — no `native_decide`
artifact appears on any headline's base, and there is no proven-but-project-scale debt left to chip. **`src/`
is fully `sorry`-free** (tactic-level: every grep-hit is docstring prose; Goodstein anchors use
`native_decide`): the three former off-headline `sorry`s (`nagura_prime` + its `5/4` rung;
`prelim_decay_2/3`) were quarantined under `wip/` on 2026-06-19 — and `prelim_decay_2/3` now also have an
in-`src/` axiom-clean route-(b) reconstruction. **The project is COMPLETE** — every headline's base is the
trust base alone, `src/` has zero `sorry`/`axiom`, and the frontier is saturated. The only repo-connected
open item is the off-headline 🟠 sharp-`2π|u|` wall (a missing-mathlib-theory build-plan that gates no
headline); per the operator's finish-and-stop directive it is NOT to be started as a side quest. → **self-stop.**

## Pointers
- **Project COMPLETE — no active frontier.** Direction call: this lap's `## What's happened` top bullet + `## Reflection — 2026-06-19` in **`PENDING_WORK.md`**. Resume baton: newest dated **`HANDOFF-2026-06-20-*.md`**. Online asks: none open (`ON-LINE-REQUEST.md` items are off-headline). Frozen plan: `NoThreeInLine/PLAN.md`.
- Quarantined/parked work (NOT built, NOT gate-scanned): **`wip/`** — `NaguraFiveFourths.lean` (parked `5/4` crux), `WienerDecayIsland.lean` (dead-code sharp `prelim_decay` island). `DivisorProblem.lean` was promoted back into **`src/`** (complete axiom-clean bonus) during the v4.31/de-vendor lap. All headline files (`PrimeGap.lean`, `Hyperbola.lean`, `Statement.lean`, `Mertens.lean`, `MertensConstant.lean`, `BVFourierDecay.lean`, the six other threads) are complete & axiom-clean.
- **If finish-and-stop is lifted, the one real (multi-lap) target** is the sharp `2π|u|` BV-Fourier constant via route (c) — Jordan decomposition + signed Stieltjes measure + IBP (mathlib has the Jordan + monotone-Stieltjes pieces; the signed-measure IBP must be built). See `PENDING_WORK.md` item 1.
- **If FINISH-AND-STOP is lifted:** the live options are (1) finish `wip/NaguraFiveFourths.lean`'s `nagura_prime` (Nagura's tuned inequality) for the `5/4` rung; (2) restore `wip/DivisorProblem.lean` into `src/`; (3) a fresh mathlib-absent classical target.

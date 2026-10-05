# STATUS — lean-formalizations 📊

> 🧮 **ACTIVE THREAD (2026-10-05 review lap 3): Mills phase 62** (branch `mills-eplus`): Theorem E+ on
> classical inputs (`BakerHarmanPintz2001` + `Dubickas2022`), Baker-free via the records competitor
> (`Mills/SaitoTypeBRecords.lean`).  `#print axioms SaitoTypeB.xi_shift_transcendental_classical` =
> trust base + 🟢 `cm3_check`, `E1Cert.cert_all` + **sorryAx** from three leaves: `finite_e2_zero_orbit`
> (Skolem at an odd prime `p ∤ N(β)`), `card_le_two_of_records` and `conjPowSum_lower_of_recurrence`
> (Mignotte-lite + dominant-pair dynamics).  Plan: `PENDING_WORK.md` top; directive: `DIRECTION.md`.
> Phase 61 (E+ from `Saito2025TypeBTrace`) is DONE.

> 🧮 **ACTIVE THREAD (2026-10-05 review lap): Mills phase 61, Theorem E+** (branch `mills-eplus`):
> `ξ(3^k + s)` transcendental for every `s ≠ 0`, conditional on `Saito2025TypeBTrace` only.
> Edges A, B and node C (`ShiftRigidity.not_primeTraces`, all shifts `s ≠ 0`) are proved; axioms of C =
> trust base + two `native_decide` certificates (🟢 `cm3_check`, `E1Cert.cert_all`).  One open node:
> **D `halfShiftTraceRigidity_holds`** (odd `s`, `β = ξ²`), decomposed in `Mills/HalfShiftRigidity.lean`.
> `xi_shifted_transcendental_saito` (Theorem E, `s = −2`) already routes through C only.

> 📈 **ACTIVE THREAD (2026-10-01): Erdős #385 phase E9b — Theorem A with a power saving** (branch
> `erdos-385-c`).  `almost_all_F385_powerSaving` / `badCount_powerSaving` (`#{bad n ≤ X} ≪ X^{1−c}`,
> from `RichertZetaGrowth`, `NearOneZeroDensity`, `ShortIntervalPrimesLower`) are wired end to end;
> `#print axioms` shows `sorryAx` from exactly two headline-path leaves: **`localZeroDetect_of_richert`**
> (the crux: large VK deviation ⇒ nearby zero near σ = 1; contour + Landau's local lemma, 75%) and
> `largeValueCount_of_zeroDetect` (counting transport, 85%).  Review lap 2026-10-01 found the old
> leaf `nearOneLargeValues_of_density` not derivable for general `C^∞` weights (Maze row,
> anchor `SlowMellinWeight`); it is now off the headline path (disclosed, ~10%).
> Hyperbola.lean (E9a) is sorry-free and axiom-clean.
>
> | headline (E9) | claim | `#print axioms` | math inputs |
> |---|---|---|---|
> | `almost_all_F385_powerSaving` | cond. on 3 lit Props | propext, choice, Quot.sound, **sorryAx** | 3 cited Props (🟡 Richert, 🟡 zero density, 🟡 Ingham–Huxley) + 2 open leaves |
> | `badCount_powerSaving` | cond. on 3 lit Props | same | same |
> | `erdos430_of_hyperbolaPrimePairs` | cond. (open conj. Prop) | propext, choice, Quot.sound | 🔴 `HyperbolaPrimePairs` (stated as hypothesis) |

**Umbrella for solved-but-hard impossibility / transcendence / no-formula meta-theorems, formalized
in Lean 4 + mathlib.** · **Build**: 🟢 green (**8789 jobs**, branch `erdos-385`, 2026-10-01, `e819725`) · `src/`: **3 disclosed crux `sorry`s**
(all in `DubickasNoSubspace.lean`, the phase-9 probe; every *headline* is clean) ·
**MATH AXIOMS: 0** · **Updated**: review lap #2 · 2026-09-28 · phase 9 probe · `6577c47`

> 🏁 **2026-09-28 — the frontier is HYPOTHESES + one named literature wall.** `src/` contains no
> `admit` and no declared `axiom`; every headline in the ledger below is `[propext, Classical.choice,
> Quot.sound]`.  It does carry **three disclosed `sorry`s**, all in the phase-9 probe file
> `NumberTheory/Transcendence/DubickasNoSubspace.lean` — the deliberate decomposition of the
> Corvaja–Zannier crux (`corvajaZannier_dichotomy` = the `p`-adic Subspace Theorem,
> `corvajaZannier_lemma4`, `valuation_sum_unit_pow_nondegenerate`).  No headline routes through them.  The remaining fidelity debt is entirely the *literature hypotheses* carried by the
> conditional headlines (`Dubickas2022`, `BakerHarmanPintz2001`, `Matomaki2007`,
> `PrimeBetweenCubesFrom`, `Ridout1957/58`) — see `PENDING_WORK.md` for the ranked table and
> `DIRECTION.md` → CURRENT DIRECTIVE for which one the next phase attacks.
> **Dubickas Theorem 1 (OEIS A076949 / A077124 / A076393-Vardi) is now conditional on ONE input**:
> `Dubickas2022` (his Lemma 6).  His Lemma 8 was dropped this lap — `c_eq_zero_or_two_noGap`
> reaches `c ∈ {0,2}` for every degree without it (`PROBE-DUBICKAS-NOGAP.md`).

> 🔢 **ACTIVE THREAD (2026-09-04): the Catalan salvage — `NumberTheory/Catalan/`, branch `catalan`.**
> Zhi-Wei Sun's arXiv:2609.04176v1 claims Catalan's constant is irrational; **the proof is wrong**
> (2-adic bookkeeping, `papers/sun-2026-catalan-irrationality.md`).  This thread formalises what
> survives — **Theorem 2.1** (full column rank of the weighted residual matrix, `residual_rank`) —
> and the refutation as a kernel-checked no-go (`sun_ledger_impossible`: the paper's own integer
> `N_B` is divisible by `2^{v₂(F_B)}`, `v₂(F_B) ≈ 2B²`).  ⚠️ Nothing in the repo claims `G ∉ ℚ`.
> **Phase 1 GREEN (2026-09-04, same day):** all four modules sorry-free; `residual_rank`,
> `sun_ledger_impossible` and every other headline are `[propext, Classical.choice, Quot.sound]`.
> **Phase 4 GREEN (2026-09-04):** `NumberTheory/DirichletBeta/` proves **at least one of β(2),…,β(20) is
> irrational** (Rivoal–Zudilin), `exists_even_beta_irrational` / `catalan_or_higher_beta_irrational`
> both `[propext, Classical.choice, Quot.sound]`, directory sorry-free.  Objective + frozen names: `DIRECTION.md`.  _(The banner below describes the integrated trunk as of June.)_

> 🔀 **INTEGRATED TRUNK (2026-06-21).** Three parallel expedition clones merged back into `main`:
> **goodstein** (Goodstein/Kirby–Paris growth theory + Curtis/power-tower/constructibles/e,π-transcendence
> + the `hyperbolaWide`/arc no-three-in-line construction), **kakeya** (Davies planar Kakeya `dimH = 2`,
> `Kakeya2D.davies_kakeya_2d`), and **ntl** (PNT / Mertens / Dirichlet divisor / BV-Fourier decay + a second,
> independent **sheared-hyperbola (HJSW)** no-three-in-line construction).
> · **Build**: 🟢 green (**8656 jobs**, `src/` **sorry-free**, **0 custom axioms**). Every headline is
> `[propext, Classical.choice, Quot.sound]` **except** the Goodstein growth closures, which additionally
> carry `Lean.ofReduceBool` from their finite base-case `native_decide` (see the ledger).
> · **No-three-in-line — BOTH constructions kept** (Trevor's call): goodstein's `hyperbolaWide`/arc lives in
> `Combinatorics.NoThreeInLine.*`; ntl's shear construction (+ its prime-gap general-`N` extension) lives in
> the sibling sub-namespace `Combinatorics.NoThreeInLine.Shear.*`, reusing the shared core
> (`Defs`/`UpperBound`/`Parabola`/`Collinearity`). Both reach the `3(p−1)` lower bound.
> · **Off-headline:** `wip/` is built as the non-default `DaviesWip` lean_lib (jvn 2nd-route GMT files sorry-free;
> FastGrowing `Bachmann` sorry-free; `Basic` carries the single disclosed A3 sorry). The PNT work now uses a
> real `PrimeNumberTheoremAnd` git dependency (de-vendored).
> · Pre-merge branch tips preserved as `premerge/{goodstein-no-three-in-line,kakeya-davies,ntl-hjsw}` tags.
> _Refreshed 2026-06-21 to cover all threads — see the at-a-glance map + full axiom ledger below._

## Threads at a glance 🗺️
- 🧊 **Foundational (frozen, all ✅ axiom-clean):** Curtis 1990 no-Frobenius-formula (`Curtis.no_polynomial_relation`) · power-tower **sharp iff** `x ∈ [e^-e, e^1/e]` (`PowerTower.tower_converges_iff_full`) · Wantzel/constructibles (iff + 5 classical impossibilities) · transcendence of **e** (Hermite) & **π** (Lindemann) ⇒ squaring-the-circle impossible.
- ♾️ **Goodstein / Kirby–Paris:** `goodstein_terminates` ✅ + the full growth story — FastGrowing/Hardy theory (A1–A4), the **Cichoń identity** (`goodsteinLength_eq_hardy`), and **"`goodsteinLength` grows like `f_{ε₀}`" two-sided** ✅. By far the densest thread; detailed banners + lap log below.
- 📐 **No-three-in-line (Green's #72) — TWO independent constructions, both reach `3(p−1)`:** goodstein's `hyperbolaWide`/arc in `Combinatorics.NoThreeInLine.*` (`three_mul_pred_le_maxNoThreeInLine`, odd `p`) + ntl's **sheared-hyperbola (HJSW)** in `Combinatorics.NoThreeInLine.Shear.*` (`hjsw_lower_bound`, all primes). The all-`N` `(3/2−ε)N` frontier is **proved** (`maxNoThreeInLine_ge_three_halves_sub`, via the PNT prime gap).
- 🔦 **Davies planar Kakeya:** `Kakeya2D.davies_kakeya_2d` — a planar Kakeya set has Hausdorff dim 2 ✅ axiom-clean (Córdoba L²/net-thinning; carries a machine-checked DeepMind-target faithfulness bridge).
- 🔢 **Analytic number theory (ntl):** Mertens' first theorem (`Mertens.mertens_first`) · Dirichlet divisor `O(√N)` error (`DirichletDivisor.sum_sigma0_isBigO_sqrt`) · BV ⇒ Fourier decay (`RealAnalysis.BVFourierDecay`). Builds on the de-vendored `PrimeNumberTheoremAnd` git dep.
- 🚧 **Off-headline (`wip/`, non-default `DaviesWip` lean_lib):** jvn 2nd-route GMT (`Capacitability`/`VonNeumannSelection`, sorry-free) + FastGrowing `Bachmann` (sorry-free); `Basic` carries the single disclosed A3 sorry. Excluded from the default `lake build`.

## Build & fidelity 🟢
`lake build` green (**8707 jobs**, 2026-09-28) · `src/` **sorry-free** · **0 custom axioms** (`grep '^axiom' src/` empty) · every headline `#print axioms = [propext, Classical.choice, Quot.sound]`, **except** the Goodstein growth closures, which additionally carry `Lean.ofReduceBool` (finite base-case `native_decide`, `DominationBaseCases.lean`). Per-headline ledger near the bottom.

## Goodstein / Kirby–Paris thread — detailed history
_The banners + lap log that follow are the goodstein expedition's internal record (the densest thread). The kakeya + ntl threads' blow-by-blow lives in their `premerge/{kakeya-davies,ntl-hjsw}`-tagged commit history; their current state is the at-a-glance map above + the full ledger + each area's `Statement.lean`/`README.md`._

> 🛑 **FINISH-AND-STOP (per charter — Trevor, 2026-06-19).** All umbrella headlines are COMPLETE + axiom-clean (Goodstein grows-like-`f_{ε₀}`, Curtis, power-tower, constructibles, e/π transcendence). **Do NOT start new side quests.** ONE correctness item to finish first: the **no-three-in-line pinwheel faithfulness repair** — you caught + are replacing a FALSE construction (`Pinwheel.lean:376`); that is a headline *correctness fix*, so close it (don't leave a known-false construction half-replaced). Then wind down: clear/quarantine the off-headline scratch sorries so `src/` is sorry-free, confirm headline `#print axioms` clean, and **self-stop.** Do not open new threads.
>
> ✅ **DONE (lap 14, 2026-06-19, `cd5a8ce`→`2b6c9a2`).** The pinwheel faithfulness repair is COMPLETE: the FALSE `{0,p}²`-corner construction was replaced by the genuine HJSW **half-band** pinwheel, and `pinwheel_noThree` / `three_mul_pred_le_maxNoThreeInLine` are FULLY PROVED and axiom-clean (trust base only). `src/` is **sorry-free** (`grep` confirms no `sorry`/`admit`/custom `axiom`), every headline `#print axioms` is the bare trust base. No new threads opened. **The ONLY thing gating the self-stop is `LEAN_LAP_ALLOW_STOP` — still `0` this lap, and the charter forbids writing the stop sentinel unless it is `1`. To finish the treadmill: set `LEAN_LAP_ALLOW_STOP=1` and the next lap will write the sentinel.** (All required work is done; remaining no-three frontier — all-`N` `(3/2−ε)N` — is blocked on PNT-grade primes and is NOT a wind-down item.)
_(historical header of the goodstein expedition: lap 14 review, 2026-06-19, `cd5a8ce`, 8299 jobs. The live header is at the top of this file.)_

> 🎉🎉🎉 **lap 11 — "goodsteinLength GROWS LIKE f_{ε₀}" IS COMPLETE, TWO-SIDED.** Both directions
> machine-checked (charter headline **C3 done**, ladder A–C complete):
> • **LOWER (Cichoń's lower bound, every `o < ε₀`):** `goodsteinLength_dominates_fastGrowing` —
>   for any `o.NF`, `∃ N, ∀ m ≥ N, f_o(m) ≤ goodsteinLength m + 2`. The whole ω-power tower generalized
>   in one stroke (`fastGrowing_towerO_le_goodsteinLength`, every `ω↑↑k`) then lifted to all ε₀ via tower
>   cofinality (`exists_repr_lt_omegaTower`). The lap-10 "needs `f_{ω^ω}`-strength deep-seed bound" worry
>   was FALSE — the `o=ω` domination suffices at every depth (`towerN_le_fastGrowing`).
> • **UPPER:** `goodsteinLength_le_fastGrowing_ordinal` — `goodsteinLength m + 2 ≤ f_{o_m}(2)`
>   (`o_m =` base-2 ordinal of `m`), from the Cichoń identity + the new `hardy_le_fastGrowing`
>   (Hardy ≤ fast-growing at the same index). **Fully axiom-clean** (no `native_decide`).
> New files: `Logic/Goodstein/{TowerDomination,GrowthStatement}.lean` (audit surface).
> • **B4 `H_{ω^α}=f_α` — DONE at finite levels:** `hardy_omega_pow_ofNat` (`H_{ω^k}(n)+1 = f_k(n+1)`,
>   the `ω[n]=n+1` offset made precise), via the new Hardy additive law `hardy_oadd_tail` + coefficient
>   lemma `hardy_oadd_coeff`. (Limit-α shown to need a different formulation — `H_{ω^ω}(1)+1≠f_ω(2)`.)
> **The entire charter ladder A1–A4, B1–B4(finite), C1–C3 is now complete.**

> ♾️ **ACTIVE EXPEDITION (2026-06-19): Goodstein-independence growth theory.** Read
> `DIRECTION.md`. Unbounded run building the mathlib-only "Goodstein grows like `f_{ε₀}`"
> content of Kirby–Paris: growth theory of `ONote.fastGrowing`, the Hardy hierarchy, and
> `goodsteinLength` → `fastGrowingε₀`. **Section A (growth theory of `fastGrowing`) is now
> COMPLETE and axiom-clean — A1/A2/A3/A4 all proved**, incl. the headline domination crux
> `fastGrowing_lt_fastGrowingε₀` (every fixed `f_o` is eventually `< f_{ε₀}`). Modules
> `Logic/FastGrowing/{Basic,Hardy,Domination}.lean` are **`sorry`-free**. **C2 (the
> `toOrdinal` ↔ `ONote.repr` bridge) is done**, and **C3 — the Cichoń identity
> `goodsteinLength m = H_{seqONote m 0}(2) − 2` — is now FULLY PROVED and axiom-clean**
> (`Logic/Goodstein/Growth.lean`); `src/` is **sorry-free**. The borrowing crux
> `hstep_oadd_one_zero` (the heart of Cichoń's theorem) was discharged via the `Good`/`Canon`
> frontier invariant + `hstep_pred_pow`. **The domination headline is now (lap 6) a machine-checked
> reduction to ONE deep fact** (`Logic/Goodstein/Domination.lean`): `goodstein_dominates_of_index`
> + the unconditional dichotomy `goodstein_dominates_or_hardy_bound` reduce "`goodsteinLength`
> dominates every `f_o`" to sub-fact (ii) — the Goodstein descent stays above `ω^o` for ≥ `m`
> steps (the Cichoń lower-bound, the genuine remaining content). The norm-budget obstruction is
> resolved (`norm_seqONote_le`: budget is free on the descent). The five threads below are frozen.

## Where it stands
**As of 2026-10-01 (branch `erdos-385`, phase E3 review lap).**  Erdős #385 phases E1–E3 are done:
`Erdos385.almost_all_F385` (`F(n) ≥ n + (1 − δ)√n` for almost all `n`, every `δ ∈ (0, 1/4)`) is
proved from four literature Props (`MR16Lemma14`, `MontgomeryVaughanMVT`, `VKZeroFreeLogDeriv`,
`MediumPNTStatement`) with `#print axioms` = trust base.  The whole analytic chain (smoothed
Chebyshev/Perron at `Re s = 2`, the VK contour shift, MVT leaves, the variance-to-density covering)
is machine-checked.  Open in the Erdős files: only the five known-false Literature controls
(`not_MR16Lemma14OneSided`, `not_MR16Lemma14NoH2Bound`, `not_MVTNoLengthTerm`,
`not_VKZeroFreeAnyWidth`, `not_VKLogDerivNoPole`), outside the E3 scope.

**As of 2026-09-28 (phase 9 probe, review lap #2).**  Phase 9's *probe* objective is MET: Dubickas's
Lemma 6 is dissected in `PROBE-DUBICKAS-NOSUBSPACE.md` into (a) fully-formalized elementary steps,
(b) `Ridout1957` for the rational-power case, (c) Corvaja–Zannier's Lemma 4 — reduced to one local
statement about power sums of `v`-units — and (d) **Corvaja–Zannier's main theorem, which IS the
`p`-adic Subspace Theorem and stays a disclosed leaf**.  The review lap re-confirmed (d)
independently: the object to bound is a linear form in the `d` monomials `σ(α)^N`, so the
one-dimensional Roth/Ridout route only re-derives the vacuous `M(α) ≥ α`.  The live objective is now
*three disclosed leaves → one citable published theorem*; the new handle is the **upper** bound
`den(Tr α^N) ∣ D^N` (from `Dα` integral), which pairs with the proved `tracePowSum_near_int` to make
the exact-integrality exponent set cofinite whenever `D · max(α⁻¹, ρ) < 1`.

**As of 2026-09-28 (phase 8 close).** `src/` is sorry-free with zero declared axioms, so *every*
theorem in `src/` is on the bare trust base; the ledger below samples the headlines.  What is left
is not proof work but **hypothesis discharge**: five conditional headline families still carry a
frozen `Literature/` `Prop` (`Dubickas2022`, `BakerHarmanPintz2001`, `Matomaki2007`,
`PrimeBetweenCubesFrom`, `Ridout1957/58`), and phase 5 showed those edges *can* be chipped
(`Ridout1957 ⇒ Mahler1957` is now a theorem).  This lap removed one outright: Dubickas's Lemma 8
(`Dubickas2022PisotGap`) no longer appears under Theorem 1 — `c_eq_zero_or_two_noGap` proves
`c ∈ {0,2}` uniformly in `deg β` from Lemma 6 alone, by recognising the exact recursion identity as
"`E₂` is constant along the Graeffe tower" and running a parity-weight induction to a
finite-support `b`-recursion.  Nine threads are complete and axiom-clean (see the glance map).

The repo declares **no custom axioms** (`grep '^axiom' src/` is empty), and every headline `#print axioms` is the bare trust base `[propext, Classical.choice, Quot.sound]` - with one disclosed exception: the Goodstein growth closures additionally carry `Lean.ofReduceBool` from their finite base-case `native_decide` (`DominationBaseCases.lean`). Three independent threads, all green and `src/` **sorry-free**. **Curtis 1990** (no polynomial formula for the Frobenius number of a triple), the **power-tower** theorem — now the **SHARP iff** (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`; both endpoints, both divergence directions) — and the **constructible-numbers / Wantzel** thread (full algebra⇔geometry iff, five classical impossibilities + two positive constructions) are complete and axiom-clean. **Transcendence of `e`** (Hermite 1873) and **transcendence of `π`** (Lindemann 1882) are now **both fully proved and axiom-clean**: `e` from the analytic part of Lindemann–Weierstrass (`exp_polynomial_approx`); `π` from the FULL Lindemann assembly — analytic engine over an arbitrary conjugate polynomial + the algebraic part (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Consequently **squaring the circle is now unconditional AND axiom-clean** (`squaring_the_circle_impossible_uncond`). The previously cited `hermite_lindemann` axiom has been **discharged and deleted**.

## What's happened (newest first)
- **2026-10-01 review lap (phase E3 CLOSED, branch `erdos-385`):** the last `AlmostAll.lean` sorry,
  V4 `smoothTwist_sub_main_eq`, fell in one pass: per-`n` Mellin inversion (`twist_inversion`), Fubini
  of `∑' n` against `∫ dy` dominated by `Λ(n) n^{-2} · P² ∫|F|` (`smoothTwist_eq_vertical`), then
  `L(Λ, w) = −ζ'/ζ(w)` on `Re w = 2` minus `mainTerm_eq_vertical`.  `almost_all_F385` is now
  `[propext, Classical.choice, Quot.sound]` + 4 literature hypotheses.
- **2026-09-28 review lap #2 (phase 9 probe: the wall is NAMED, and the residual sparsity becomes an
  inequality):** seven grind laps dissected Dubickas's Lemma 6.  Verdict recorded in `DIRECTION.md` →
  CURRENT DIRECTIVE: `corvajaZannier_dichotomy` = Corvaja–Zannier 2004's main theorem = the `p`-adic
  Subspace Theorem, and it stays a **disclosed leaf** (structural reason, not effort: the quantity to
  bound is a linear form in the `d` monomials `σ(α)^N`).  Everything else in Lemma 6 is either proved
  (`isPisot_of_pseudoPisotMul`, Lemma 5 both branches, `exists_tie_of_bounded_den`,
  `false_of_bounded_den_of_nondegenerate`, `tracePowSum_near_int`, the `k = 2` Graeffe collapse) or
  routed through `Ridout1957` (`exists_pisot_pow_of_pow_rat`).  **New this lap:** the missing *upper*
  bound `den(Tr α^N) ∣ D^N`, which converts the seventh lap's vague "the exponent set may be sparse"
  into the concrete inequality `D ≥ min(α, ρ⁻¹)`.  Objective reset to *three leaves → one*.
- **2026-09-28 review lap (🎉 Dubickas Theorem 1 loses Lemma 8; `src/` fully sorry-free):**
  `c_eq_zero_or_two_noGap` is PROVED for **every** degree from `Dubickas2022` alone, and
  `hG : Dubickas2022PisotGap` is dropped from `transcendental_growth_of_monic_quadratic`,
  `theorem1`, `oeis_constants` and from `Comparator/Dubickas/Challenge.lean`
  (`scripts/comparator-probe Dubickas` → identical).  The whole `deg β ≤ 5` case analysis — and its
  one disclosed `deg β ≥ 6` `sorry`, the last `sorry` anywhere in `src/` — is **deleted**, replaced
  by the degree-uniform route of `PROBE-DUBICKAS-NOGAP.md`.  **The reframing that did it:** the
  identity `c = 2 βᴺ S_N + S_N² − S_(2N)` is literally `E₂(βᴺ's conjugate multiset) = c/2`, i.e.
  `E₂` is *eventually constant* along the Graeffe tower `N = 2^j`; and eventual constancy alone
  forces `c/2 ∈ {0,1}`.  Lemma 8 was only ever supplying a **lower** bound on `|S_N|`, which the new
  route never wants.  Glue = two Newton identities at `k = 1, 2` (`eSmall_one`;
  `two_mul_eSmall_two`, proved by multiset induction off `esymm_cons`) plus one
  `linear_combination`.  Eight supporting files (multiset Newton, multiset Graeffe, the
  parity-weight induction, the `b`-recursion with finite support) all sorry-free and axiom-clean.
  Headlines: `[propext, Classical.choice, Quot.sound]`; `Dubickas2022` (Lemma 6, Corvaja–Zannier
  subspace theorem) is the sole remaining hypothesis under the OEIS-linked constants.
- **2026-06-19 lap 14 (🎉🎉🎉 HJSW `3(p−1)` no-three-in-line — COMPLETE & axiom-clean):** The best
  *proven* density constant (`3/2`) for the no-three-in-line problem (Hall–Jackson–Sudbery–Wild 1975,
  unimproved; to my knowledge never before formalized) is now fully machine-checked.
  `three_mul_pred_le_maxNoThreeInLine : 3(p−1) ≤ maxNoThreeInLine(2p)` (odd prime `p`), axioms =
  trust base only. **Lap-14 turning point:** the lap-13 `pinwheel` construction (single hyperbola,
  four `{0,p}²` translates per class, drop one corner) was brute-force **FALSE** — no-three for NO
  drop rule (infeasible at `p=7` ∀`k`). Replaced with the genuine HJSW **half-band** construction
  (x-translate direction depends on the left/right half), brute-verified no-three for all `p≤17`.
  The crux `pinwheel_diagonal_false` (cross-class slope-`±1` incidence): the σ-reflection pins the
  partner class (`c=b, bc=a` slope `−1`; `c=p−b, bc=p−a` slope `+1`) and the drop rule puts its three
  kept points on lines offset by exactly `±p` from the diagonal — proved over the 4 families via
  `det3` collapse → line invariant (ℝ) → mod-`p` reflection → `omega`.
  Files: `Combinatorics/NoThreeInLine/{Pinwheel,HyperbolaLine,Hyperbola}.lean`.
- **2026-06-19 lap 11 (🎉🎉🎉 "goodsteinLength GROWS LIKE f_{ε₀}" — TWO-SIDED, charter C3 DONE):**
  Both directions of the headline are now machine-checked.
  **LOWER (Cichoń's lower bound, every `o < ε₀`):** `goodsteinLength_dominates_fastGrowing`
  (`o.NF → ∃ N, ∀ m ≥ N, f_o(m) ≤ goodsteinLength m + 2`). New file `TowerDomination.lean`, two general
  engines subsuming lap-10's per-level closures: (1) the **general length bootstrap**
  `two_mul_le_goodsteinLength_iter` (`goodsteinLength((log₂)^[k] m) ≥ 2m` for all `k`) — the lap-10 fear
  that this "needs an `f_{ω^ω}`-strength deep-seed bound" was FALSE; the already-proved `o=ω` domination
  suffices at every depth, carried by the clean finite tower bound `towerN_le_fastGrowing`; (2) the
  **general ordinal bridge** `omegaTower_succ_le_seqONote_repr` (pure `toOrdinal` induction). Lifted to
  all ε₀ via tower cofinality `exists_repr_lt_omegaTower` (axiom-clean).
  **UPPER:** `goodsteinLength_le_fastGrowing_ordinal` (`goodsteinLength m + 2 ≤ f_{o_m}(2)`), from the
  Cichoń identity + the new `hardy_le_fastGrowing` (`hardy o n ≤ fastGrowing o n`, n≥2) — **fully
  axiom-clean** (no `native_decide`). C3 stated thinly in audit surface `GrowthStatement.lean`, with the
  faithfulness anchor `fastGrowingε₀_eq_towerO` (our tower IS mathlib's ε₀ fundamental sequence).
  Lower closures carry the documented finite-base-case `native_decide` (engines clean).
  **Also B4 at finite levels:** `hardy_omega_pow_ofNat` (`H_{ω^k}(n)+1 = f_k(n+1)`, axiom-clean) — the
  classical `H_{ω^α}=f_α` with the `ω[n]=n+1` offset, via the new Hardy additive law `hardy_oadd_tail`
  + coefficient lemma `hardy_oadd_coeff`; the limit-α case provably needs a different formulation
  (`H_{ω^ω}(1)+1=8 ≠ f_ω(2)=2048`). Charter ladder A–C + B4(finite) now complete. Build 🟢 (8295 jobs);
  commits `4856b9a` (tower spine) → `9b1e779` (full ε₀) → `08afea0` (audit surface) →
  `9f8cb56` (`hardy_le_fastGrowing`) → `904f5ea` (upper bound) → `5bf832f`/`6a63e12` (additive law + B4).
- **2026-06-19 lap 10 (CLIMBED to `o=ω^ω`):** diagonal domination closed at the individual limit
  levels `o=ω`, `o=ω^j` (finite `j`), `o=ω^ω` (`DominationOmega.lean`) via the self-similarity TOWER
  (`GoodsteinLike.lean`) + the doubly-iterated length bootstrap. Superseded this lap by the general
  `TowerDomination.lean` engines (which subsume all of it), but the per-level closures remain as
  anti-vacuity witnesses. Build 🟢 (8293 jobs).
- **2026-06-19 lap 9 (🎉 DIAGONAL DOMINATION CLOSED for all finite levels — the 8-lap crux):**
  The headline open problem — `f_o(m) ≤ goodsteinLength m + 2` (sub-fact (ii), **Cichoń's lower
  bound**) — is now PROVED for every finite level, machine-checked:
  `fastGrowing_ofNat_le_goodsteinLength : 16 ≤ m → n+1 ≤ log₂ m → fastGrowing (ofNat n) m ≤
  goodsteinLength m + 2`. So `goodsteinLength` **diagonally dominates the entire finite fast-growing
  hierarchy** `f_0, f_1, f_2, …`. The mechanism (axiom-clean engine): **self-similarity**
  (`leadExp_ge_goodsteinSeq_log` — the leading-exponent sequence dominates the Goodstein sequence one
  scale down, via the per-step floor `leadExp_step_ge` + `bump_mono` through the `toOrdinal` bridge),
  a **strong induction** making the exponential length bound `goodsteinLength m ≥ 2^{m+1}+m` reproduce
  itself one scale up (`goodsteinLength_exp_lower` / `exp_le_goodsteinLength_step`), and the
  **small-regime termination law** (`goodsteinLength_le_of_small` → `n_le_goodsteinSeq`) lifting `o=2`
  to all finite `o`. The induction bottoms out at finitely many computational base cases
  `goodsteinLength M ≥ 2^{M+1}+M` (`4≤M<16`), discharged by a tail-recursive forward evaluator
  (`gpos`) under `native_decide` (heaviest: `M=15`, a 65551-step run), isolated in
  `DominationBaseCases.lean`. The unconditional closures carry `Lean.ofReduceBool` (finite base-case
  computation); the math engine + all conditional reductions stay `[propext, Classical.choice,
  Quot.sound]`. **Next frontier = transfinite `o` (start `o=ω`) toward `f_{ε₀}`.** Build 🟢 (8290 jobs).
- **2026-06-19 lap 8 (DEEP-REFLECTION lap — altitude audit, no proof churn):** full read-down of
  STATUS/HANDOFF/PENDING/DIRECTION + git log; re-ran `#print axioms` on all 12 headlines (every one
  = bare trust base `[propext, Classical.choice, Quot.sound]`, **0 math axioms**) and re-audited the
  growth-theory statements against the math — all faithful, the `NON-ELEMENTARY` docstring honest
  about not being the diagonal. **Direction call: SOUND, KEEP.** Real lap-over-lap motion (C3 closed
  lap 5 · headline reduced to sub-fact (ii) lap 6 · `o=1` + machinery lap 7), not circling. The
  Cichoń identity `goodsteinLength m = H_{seqONote m 0}(2) − 2` (C2+C3, axiom-clean) is a genuine
  capstone. **STOP: chasing further *non-diagonal* lower-bound refinements as headline output** —
  super-linear→non-elementary is a complete, bankable result that does NOT advance sub-fact (ii);
  iterating it would simulate progress. **Highest-value next target: the `o=2` diagonal
  `f_2(m) ≤ goodsteinLength m + 2`** — the smallest open instance of Cichoń's lower bound, forcing
  the steps-between-drops *base case* (leadExp `≥ 2` sustained for `≥ m` steps ⟺ `goodsteinSeq m j ≥
  (j+2)²` for `j ≤ ~m`). Fixed two stale docstrings (`hstep_oadd_one_zero`/`hstep_toONote` still said
  "disclosed sorry"; both are PROVED). Full reasoning in `PENDING_WORK.md` → `## Reflection 2026-06-19`.
- **2026-06-19 lap 7 (`f_1` DOMINATED unconditionally + recursion skeleton; 6 commits, all
  axiom-clean, `src/` sorry-free):** broke the deadlock on sub-fact (ii) at level `o = 1`.
  `bump_gt` (one bump strictly grows a value above its base) ⟹ `goodsteinSeq_ge_init` (value stays
  `≥ m` for the first `m` steps) ⟹ `omega_le_seqONote_repr` (descent ordinal stays `≥ ω`) =
  **sub-fact (ii) at `o = 1`**; with the generalized reduction `goodstein_dominates_of_index_le`,
  this gives `fastGrowing_one_le_goodsteinLength` — `goodsteinLength` dominates `f_1` for every
  `m ≥ 2`, via the full Cichoń pipeline (not `native_decide`). Plus `goodsteinLength m ≥ 2m − 1`
  (`two_mul_sub_one_le_goodsteinLength`). And the recursion skeleton toward `o ≥ 2`: `log_bump`
  (the leading exponent bumps itself), `leadExp_drop_le_one` (leading CNF exponent drops `≤ 1`/step),
  `leadExp_ge_of_base_le` (non-decreasing while `≥ base`). Telescoped (`leadExp_ge_sub`) +
  ordinal bridge (`opow_toOrdinal_log_le`, `opow_le_seqONote_repr`, `omega_opow_le_seqONote_repr`):
  the descent stays `≥ ω^k` for the first `log₂ m − k` steps. **Capstone — `goodsteinLength` is
  NON-ELEMENTARY:** `fastGrowing_two_log_le_goodsteinLength` (`f_2(log₂ m) ≤ goodsteinLength m + 2`)
  and its generalization `fastGrowing_ofNat_log_le_goodsteinLength` (`f_n(log₂ m − n + 2) ≤
  goodsteinLength m + 2`, every finite `n`) via the non-diagonal reduction
  `fastGrowing_step_le_goodsteinLength` — at `n ≈ (log₂ m)/2` a tower of height `~log₂ m`, so
  `goodsteinLength` outgrows **every elementary function**. Remaining deep crux sharpened to:
  **steps-between-leading-exponent-drops is itself a Goodstein length** (upgrades the budget
  `log₂ m → m`, the only gap to the diagonal `f_n(m)`; see `PENDING_WORK.md`).
- **2026-06-19 lap 6 (DOMINATION HEADLINE REDUCED to one descent-count fact; norm obstruction
  RESOLVED; 4 commits, all axiom-clean, `src/` still sorry-free):** turned lap-5's negative
  finding into a clean reduction. (1) `goodstein_dominates_of_index` — the full Cichoń assembly
  `o.NF → norm o ≤ m → oadd o 1 0 < seqONote m m → fastGrowing o m ≤ goodsteinLength m + 2`,
  machine-checked end-to-end (telescope at `j=m` + bridge + `hardy_le_of_lt` + monotone); the ONLY
  open input is the index hypothesis. (2) `norm_toONote_lt`/`norm_seqONote_le` — `norm (seqONote
  m j) ≤ j+1`, so the **Hardy budget is AUTOMATIC at the telescope step `j+2`** (lap-5's "norm
  obstruction" only ever bit at the *fixed* arg 2; on the descent it is free, both directions).
  (3) `goodstein_dominates_or_hardy_bound` — the unconditional **dichotomy**: for `norm o ≤ m`,
  EITHER `fastGrowing o m ≤ goodsteinLength m + 2` OR `goodsteinLength m + 2 ≤ hardy (oadd o 1 0)
  (m+2)`. ⟹ **the whole headline ⟺ "the second branch is eventually empty" = sub-fact (ii), the
  descent stays above `ω^o` for ≥ `m` steps (Cichoń lower bound).** Established (with proof) that
  (ii) is irreducible: leading-exponent antitone is a free corollary of the descent (no count);
  the dichotomy can't be bootstrapped from the linear bound; `j*(m)→∞` is provable but only gives
  `goodsteinLength → ∞`. Also added Hardy growth theory: `hardy_ofNat` (`H_k(x)=x+k`),
  `hardy_omega` (`H_ω(n)=2n+1`), `two_mul_le_hardy_pow` (`2n ≤ H_{ω^e}(n)`, e≠0) — first
  super-linear Hardy lower bound, a building block toward the count. native_decide anchors lock
  every new theorem. **Next:** the deep count (super-linear lower bound on `goodsteinLength`).
- **2026-06-19 lap 5 (C3 BORROWING CRUX PROVED — Cichoń identity fully axiom-clean; 2 commits):**
  discharged the lone disclosed `sorry` `hstep_oadd_one_zero` (the genuine borrowing predecessor
  of `ω^E`, the heart of Cichoń's theorem). The whole C3 chain — `hstep_toONote`,
  `goodsteinLength_eq_hardy` — is now machine-checked with `#print axioms = [propext,
  Classical.choice, Quot.sound]`. New machinery in `Growth.lean` (all axiom-clean): the ordinal
  constructor twins `toOrdinal_pow`/`toOrdinal_oadd`; the frontier invariant `Canon`/`Good`
  (base-`(b+1)` canonical with ≤1 coeff `=b+1` parked at the active descent frontier);
  `canon_repr` + `canon_round_trip` (a `Canon` NF notation round-trips through `evalNat`, via the
  engine's `toOrdinal` strict monotonicity — no separate `evalNat` mono+bound recursion needed);
  `Canon_pred` (a `Good` successor's predecessor is fully `Canon`); `Good_fundSeq` (`Good`
  preserved by the limit descent); and the general `hstep_pred_pow` (predecessor of `ω^E` for
  every NF `E` with `Good b E`, by WF recursion on `repr E`). `src/` is now **0 sorries, 0 math
  axioms**. The parallel Aristotle job on the general goal was cancelled (subsumed). **Same lap,
  also proved the Hardy↔fastGrowing BRIDGE** (`Logic/Goodstein/Domination.lean`, all axiom-clean):
  `fastGrowing_le_hardy_pow : f_α ≤ H_{ω^α}` (matching args) via `hardy_split`
  (`H_{ω^e·c+R}=H_{ω^e·c}∘H_R` — NF gives the no-absorption condition, sidestepping general
  `ONote.add` additivity), the iteration law `hardy_oadd_iter` (`H_{ω^e·k}=(H_{ω^e})^[k]`), and
  `toOrdinal_two_cofinal` (Goodstein ordinals cofinal in ε₀). **Negative finding** for the final
  domination headline: `hardy_le_of_lt`'s `norm α ≤ x` budget makes Hardy index-monotonicity FAIL
  at fixed small arg (`H_ω(2)=5 < H_5(2)=7`), so the diagonal `H_{toONote 2 m}(2)` needs a
  budget-aware argument. Banked the telescope enabler (`goodsteinLength m + 2 = H_{seqONote m j}(j+2)`
  for all `j`) and **a linear length lower bound `le_goodsteinLength : m ≤ goodsteinLength m`**
  (via `le_bump`; axiom-clean). Remaining: a super-exponential Goodstein-term lower bound for the
  index sweet-spot (the genuine deep crux; multi-lap).
- **2026-06-19 lap 4 (C3 borrowing crux — massively narrowed; 6 commits, all axiom-clean):**
  the `r=0 ∧ L≥1` borrowing case of `hstep_toONote` is now FULLY PROVED modulo a single
  isolated lemma `hstep_oadd_one_zero` (the `c=1` predecessor of `ω^E`). Proved this lap, all
  in `Logic/Goodstein/Growth.lean`: **Lemma A (coefficient peel)** `hstep_oadd_coeff`
  (+`fundSeq_oadd_coeff`) reducing general `c` to `c=1`; **finite base case**
  `hstep_oadd_one_zero_finite` (the engine end-to-end); **recursion primitives**
  `hstep_oadd_one_of_succ`/`_of_limit`, `fundSeq_oadd_one_of_succ`/`_of_limit`,
  `hstep_finite_pred`, `fundSeq_finite_succ`; the **answer characterization** `evalNat` +
  `evalNat_toONote : evalNat b (toONote b L) = bump b L`; and **both descent identities**
  `evalNat_succ` and `evalNat_fundSeq`. The only thing left to close `hstep_oadd_one_zero` is
  one coefficient-bound invariant (`Good b E`) for the successor-case reconstruction — the
  limit case already closes via `evalNat_fundSeq`. See `hstep_oadd_one_zero`'s docstring +
  `PENDING_WORK.md` for the full close-out plan. Aristotle job `77c99f0e` grinds the (pre-
  narrowing) general goal in parallel.
- **2026-06-19 lap 2b (C2 bridge built — axiom-clean):** new `Logic/Goodstein/Growth.lean`
  crosses `Engine.toOrdinal` ↔ `ONote.repr`: `toONote b n` (computable notation),
  `repr_toONote : repr (toONote b n) = toOrdinal b n`, `toONote_NF`, and the Goodstein
  descent on `ONote` — `seqONote m k := toONote (k+2) (goodsteinSeq m k)` with
  `seqONote_lt` (`G_k ≠ 0 ⟹ seqONote m (k+1) < seqONote m k`), transported from
  `Engine.seqOrd_step`. The termination descent now lives on the same `ONote` as the A4
  growth theory. 5 `native_decide` anchors; all `#print axioms`-clean. **Remaining: C3**
  (`goodsteinLength` tracks `f_{ε₀}` — the Hardy-counts-steps identity).
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
- **2026-06-16 (π/e transcendence COMPLETE — `hermite_lindemann` axiom deleted; condensed, was 4
  bullets):** the full Lindemann assembly for `π` landed and the cited axiom was discharged + deleted
  → repo math-axiom count **0**. Chain (all axiom-clean): `e_transcendental` (Hermite 1873, the
  integer-`N`/mod-`p` engine of `exp_polynomial_approx`) → `PiLindemann` (combinatorial reduction
  `e^{iπ}=−1 ⟹ K+∑e^{σ_t}=0` + non-monic analytic engine) → fact (a) `sum_aeval_roots_int`
  (Aristotle `9a19f72e`) → fact (b) `subsetSum_esymm_rational` (fundamental theorem of symmetric
  polynomials, Aristotle `b7252abe`) → `transcendental_pi_axiomClean`; `squaring_the_circle_impossible_uncond`
  rewired to it, now fully axiom-clean. Both Aristotle proofs independently kernel-verified.
- **2026-06-14/15 (Curtis · power-tower convergence · Wantzel/constructible — condensed, was 3
  bullets):** the three foundational frozen threads, all axiom-clean. Curtis 1990 no-Frobenius-formula
  (`no_polynomial_relation`; crux `substCurve_eq_zero`, Lemma 2 Brauer–Shockley Aristotle-verified);
  power-tower convergence on `[e^(-e), e^(1/e)]`; constructible numbers / Wantzel — full
  `isConstructible_iff_constructiblePoint` (both directions) + 5 classical impossibilities (cube,
  trisection, nonagon, heptagon, geometric-point versions), pentagon positive.

## Outstanding
The five completed threads (transcendence/squaring-the-circle, power-tower sharp `iff`,
Wantzel, Curtis, Goodstein termination) are **COMPLETE and axiom-free**. In the ACTIVE
expedition, **Section A (A1–A4), C1, C2, C3 (the Cichoń identity), AND the diagonal lower bound
`f_o(m) ≤ goodsteinLength m + 2` for every `o < ε₀` are all DONE.** The lower-bound headline — the
genuine Cichoń growth content, the 8-lap-then-3-lap crux — is now complete:
`goodsteinLength_eventually_dominates_fastGrowing`. The diagonal closures carry the finite-base-case
`native_decide` artifacts (excluded from the math-axiom count per the doctrine; the engines are
trust-base-clean).
### Short-term (mirror PENDING_WORK top — the live frontier)
**2026-09-28 (review lap #2): the live frontier is the phase-9 Dubickas probe**, whose three
disclosed `sorry`s are the only open obligations anywhere in `src/`.  Ordered work items (mirroring
`PENDING_WORK.md` top, binding via `DIRECTION.md` → CURRENT DIRECTIVE): (0a) the general-`k` Newton
collapse `valuation_sum_unit_pow_mulClosed`; (0b) `tracePowSum_den_dvd` (`den(U_N) ∣ D^N`);
(0c) the cofiniteness dichotomy; (0d) re-route `corvajaZannier_lemma4` + the degenerate descent.
Then, as before: (1) 🟠 `Dubickas2022` = his Lemma 6 ⇒ Corvaja–Zannier ⇒ the `p`-adic Subspace
Theorem — the ONLY hypothesis under the OEIS-linked Dubickas headlines; mathlib has nothing, so the
chip is a *prerequisite* (heights / places of a number field), not the theorem. (2) 🟡 Saito
Remark 4.4 (degree-3 Pisot, `Mills/`). (3) 🟡 Catalan phase 2 (probe-first; never claim `G ∉ ℚ`).
(4) 🟡 `PrimeBetweenCubesFrom` / `BakerHarmanPintz2001` / `Matomaki2007` — primes in short intervals,
the bedrock under Mills.  **CLOSED, do not reopen:** Dubickas phases 7 + 8 (Theorem 1 + Lemma-8
removal), Mills phases 2–6, Diophantine phase 5 (the three Ridout edges), Catalan phases 1/3,
DirichletBeta phase 4.

_(older, still valid)_
**No-three-in-line HJSW `3(p−1)` is COMPLETE (lap 14).** The natural next frontier is the **all-`N`
`(3/2−ε)N` corollary**: from the per-prime `3(p−1) ≤ maxNoThreeInLine(2p)`, lift to every large `N`
by choosing a prime `p ≈ N/2`. Bertrand only gives `p > N/4` (ratio `3/4` — *weaker* than the existing
parabola's ratio `1`), so reaching `3/2` genuinely needs a prime in `[(1−ε)N/2, N/2]` — i.e. PNT-grade
prime distribution (a separate, likely multi-lap, mathlib-availability question). Until then the
headline stands at `N = 2p`. (Also minor: extend the headline to `p = 2` via an explicit 3-point
witness so it holds for *all* primes, not just odd.)

For the Goodstein thread, the charter ladder is COMPLETE (A1–A4, B1–B4-finite, C1–C3 + two-sided
"grows like `f_{ε₀}`"). Only genuine *extensions* remain:
- **B4 at LIMIT levels** — the clean `H_{ω^α}(n)+1=f_α(n+1)` is FALSE at limit α under `ω[n]=n+1`
  (`H_{ω^ω}(1)+1=8≠f_ω(2)=2048`). A correct limit-α statement (inequality sandwich, or along the
  successor-cofinal subsequence) is the open refinement. Genuinely subtle; not clearly high-value.
- **Optional sharpenings:** strict domination (remove the `+2`, needs general index-monotonicity =
  A3-hard); a tighter `f_{ε₀}` upper bound; a single ε₀ capstone via `ε₀ = sup_o repr o` (presentation).
- **DONE (do not re-iterate):** two-sided "grows like `f_{ε₀}`" — lower bound every `o < ε₀`
  (`goodsteinLength_dominates_fastGrowing`) + upper bound (`goodsteinLength_le_fastGrowing_ordinal`);
  **B4 at finite levels** (`hardy_omega_pow_ofNat`); the Hardy additive law (`hardy_oadd_tail`) +
  coefficient lemma (`hardy_oadd_coeff`); `hardy_le_fastGrowing`. All complete and bankable.
### Long-term
- **B4** (`H_{ω^α}=f_α`) — long-horizon trap under mathlib's `ω[n]=n+1` (measured: not a constant
  shift); needs a reformulated statement. Lower value than the diagonal headline.
- General Hermite–Lindemann for arbitrary algebraic α — bounded extension of the π assembly.
- PARKED P2/P3 (Curtis mathlib upstream; not-algebraic framing) — web/CLA-gated.
### To completion
- Curtis ✅ · Power-tower SHARP iff ✅ · Wantzel iff ✅ · e/π-transcendence ✅ ·
  squaring-the-circle ✅ · Goodstein termination ✅ · **fast-growing growth theory A1–A4 ✅** ·
  **Cichoń identity C1/C2/C3 ✅** · **"goodsteinLength GROWS LIKE `f_{ε₀}`" — TWO-SIDED ✅**: lower
  bound `f_o(m) ≤ goodsteinLength m + 2` every `o < ε₀` (`goodsteinLength_dominates_fastGrowing`) +
  upper bound `goodsteinLength m + 2 ≤ f_{o_m}(2)` (`goodsteinLength_le_fastGrowing_ordinal`). Repo
  math-axiom count: **0** (lower closures carry finite-base-case `native_decide` artifacts only).
  **B4 (finite) `H_{ω^k}(n)+1=f_k(n+1)` ✅** (`hardy_omega_pow_ofNat`). **Charter ladder A1–A4,
  B1–B4(finite), C1–C3 COMPLETE.** Only extensions remain (B4 at limit α; optional sharpenings).

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Erdos385.almost_all_F385` | **Erdős #385, almost all**: `#{n ≤ X : F(n) < n + (1−δ)√n} = o(X)` for `δ ∈ (0,1/4)` (new; sharper than Tao 2024), **cond.** on `MR16Lemma14`, `MontgomeryVaughanMVT`, `VKZeroFreeLogDeriv`, `MediumPNTStatement` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms; 4 hypotheses, all 🟡 published (Matomäki–Radziwiłł 2016 / Teräväinen, Montgomery–Vaughan 1974, Vinogradov–Korobov + Titchmarsh 3.11, PNT+ `MediumPNT`) |
| `Transcendence.Dubickas.theorem1` | **Dubickas 2022, Theorem 1**: κ, ζ, Sylvester γ, η, τ are transcendental; **cond.** on `Dubickas2022` (his Lemma 6) — his Lemma 8 is NO LONGER needed | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms; 1 hypothesis (🟠 `Dubickas2022` = Corvaja–Zannier ⇒ `p`-adic Subspace Theorem; current chip = a heights/places prerequisite) |
| `Transcendence.Dubickas.oeis_constants` | **OEIS A076949, A077124, A076393 (Vardi's constant) are transcendental**; same single hypothesis | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — ⚓ OEIS-linked file; comparator challenge matches (`comparator-probe Dubickas` identical) |
| `Transcendence.Dubickas.transcendental_growth_of_monic_quadratic` | **Theorem 2 for monic quadratics**: `α = lim x_n^(1/2ⁿ)` transcendental unless `a₁²−2a₁−4a₂ ∈ {0,8}` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — `hG` dropped 2026-09-28 |
| `Transcendence.Dubickas.c_eq_zero_or_two_noGap` | the Lemma-8-free core: Dubickas's (17)/(18) for **every** `deg β`, from Lemma 6 alone | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **the phase-8 result**; route in `PROBE-DUBICKAS-NOGAP.md` |
| `Transcendence.Dubickas.exists_pisot_pow_noD` | the **phase-9 probe** target: Dubickas's Lemma 6 without `Dubickas2022`, from `Ridout1957` | `[propext, sorryAx, Classical.choice, Quot.sound]` | 🚧 **NOT a headline and no headline depends on it.** 3 disclosed `sorry`s: `corvajaZannier_dichotomy` (🟠 = the `p`-adic Subspace Theorem — the named wall), `corvajaZannier_lemma4` (🟡 degenerate branch), `valuation_sum_unit_pow_nondegenerate` (🟡 local leaf, proved for `card U = 2`) |
| `Mills.wright` | **Wright 1951**: `∃ ω, ⌊tower ω n⌋ prime ∀ n ≥ 1`, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **unconditional** |
| `Mills.exists_least_of_primeBetweenCubes` | **Mills 1947** (least Mills constant), **cond.** on `PrimeBetweenCubesFrom` (Ingham) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms; 1 hypothesis (🟡 `PrimeBetweenCubesFrom`) |
| `Mills.transcendental_of_four_le` | **Saito, Thm 1.1**: `ξ_c` transcendental for `c ≥ 4`, **cond.** on `BakerHarmanPintz2001` + `Matomaki2007` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms; 2 hypotheses (🟡 primes in short intervals) |
| `Mills.transcendental_or_pisot` | **Saito, Thm 1.2**: `ξ₃` transcendental, or `ξ₃^(3^m)` a degree-3 Pisot | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — Remark 4.4 (degree-3 refinement) is the registered next step |
| `Mills.irrational_of_ridout` | Saito irrationality with `Mahler1957` **discharged into** `Ridout1957` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — bedrock is BHP + Matomäki + Ridout (one fewer hypothesis than the paper) |
| `Diophantine.{mahler_of_ridout1957, ridoutSUnitDen_of_ridout1957, roth_of_ridout1958}` | the three Diophantine wiring edges (Mahler 1957 / S-unit denominators / Roth 1955 from Ridout) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — phase 5; turns three cited hypotheses into consequences of Ridout |
| `Catalan.residual_rank` | **Sun arXiv:2609.04176 Theorem 2.1**: full column rank of the weighted residual matrix | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — the salvageable part of a paper whose main claim is WRONG |
| `Catalan.sun_ledger_impossible` | kernel-checked **no-go**: Sun's own integer `N_B` is divisible by `2^{v₂(F_B)}`, `v₂(F_B) ≈ 2B²` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — ⚠️ nothing in the repo claims `Irrational catalanConst` |
| `DirichletBeta.exists_even_beta_irrational` | **Rivoal–Zudilin**: at least one of `β(2), …, β(20)` is irrational | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `DirichletBeta.catalan_or_higher_beta_irrational` | Catalan's constant `β(2)` or some higher even `β` is irrational | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `NoThreeInLine.three_mul_pred_le_maxNoThreeInLine` | **HJSW `3/2` density (arc construction)**: `3(p−1) ≤ maxNoThreeInLine(2p)` (odd prime `p`); best PROVEN no-three-in-line constant (HJSW 1975) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — half-band pinwheel + slope-`±1` σ-reflection crux fully proved (lap 14) |
| `NoThreeInLine.Shear.hjsw_lower_bound` | **HJSW `3/2` density (shear construction)**: `3(p−1) ≤ maxNoThreeInLine(2p)` (**all** primes `p`) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — ntl's independent sheared-hyperbola dev, kept alongside the arc one (keep-both, `NoThreeInLine.Shear.*`) |
| `NoThreeInLine.Shear.maxNoThreeInLine_bounds` | general-`N` two-sided `maxNoThreeInLine` bounds (shear + prime-gap extension) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Kakeya2D.davies_kakeya_2d` | **Davies' theorem**: a planar Kakeya set has Hausdorff dimension 2 | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — Córdoba L²/net-thinning; machine-checked DeepMind-target faithfulness bridge |
| `Mertens.mertens_first` | **Mertens' first theorem** `∑_{d≤N} Λ(d)/d = log N + O(1)` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — via the ψ/θ Chebyshev machinery in `Shear.PrimeGap`; uses de-vendored PNTAnd |
| `DirichletDivisor.sum_sigma0_isBigO_sqrt` | **Dirichlet divisor problem (asymptotic)** — error term `O(√N)` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `RealAnalysis.BVFourierDecay.norm_fourierIntegral_le_half_integral_norm_sub_shift` | **BV ⇒ Fourier decay** (half-period reflection bound; the BV-Fourier decay family) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `FastGrowing.fastGrowing_lt_fastGrowingε₀` | `f_{ε₀}` dominates every fixed `f_o` (A4; Kirby–Paris growth gap), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — A4 |
| `Logic.Goodstein.goodsteinLength_eq_hardy` | **Cichoń identity** `goodsteinLength m = H_{seqONote m 0}(2) − 2`, uncond. (C2+C3 crown) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — borrowing crux `hstep_oadd_one_zero` discharged (lap 5) |
| `Logic.Goodstein.goodsteinLength_grows_like_fastGrowingε₀` | **THE HEADLINE (C3), two-sided**: lower (∀ `o<ε₀`, eventually `f_o(m) ≤ goodsteinLength m + 2`) ∧ upper (`goodsteinLength m + 2 ≤ f_{o_m}(2)`) | `[propext, Classical.choice, Quot.sound]` + finite-base-case `native_decide` artifacts | ✅ 0 math axioms — the definitive "Goodstein grows like `f_{ε₀}`" audit surface (lap 11) |
| `Logic.Goodstein.goodsteinLength_dominates_fastGrowing` | **Cichoń lower bound, complete to ε₀**: `∀ o.NF, ∃ N, ∀ m≥N, f_o(m) ≤ goodsteinLength m + 2` (every `o < ε₀`) | `[propext, Classical.choice, Quot.sound]` + finite-base-case `native_decide` artifacts | ✅ 0 math axioms — diagonal lower bound DONE up to ε₀ (lap 11); `native_decide` = finite Goodstein base-case lengths, excluded per doctrine |
| `Logic.Goodstein.goodsteinLength_le_fastGrowing_ordinal` | **upper bound** (two-sided "grows like `f_{ε₀}`"): `goodsteinLength m + 2 ≤ f_{o_m}(2)`, `o_m =` base-2 ordinal of `m` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **fully axiom-clean** (no `native_decide`); via Cichoń identity + `hardy_le_fastGrowing` |
| `FastGrowing.hardy_omega_pow_ofNat` | **B4 (finite)**: `H_{ω^k}(n)+1 = f_k(n+1)` (classical `H_{ω^α}=f_α` with the `ω[n]=n+1` offset) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **fully axiom-clean**; via Hardy additive law `hardy_oadd_tail` + coefficient lemma. Limit-α needs a different formulation (documented) |
| `Logic.Goodstein.fastGrowing_one_le_goodsteinLength` | `f_1(m) ≤ goodsteinLength m + 2` (sub-fact (ii) at `o=1`), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Logic.Goodstein.fastGrowing_{two_log,ofNat_log}_le_goodsteinLength` | `goodsteinLength` super-linear / **non-elementary** (`f_n(log₂ m − n + 2) ≤ goodsteinLength m + 2`) | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — NON-diagonal (argument `~log m`, not `m`); diagonal still open |
| `Logic.Goodstein.goodstein_terminates` | Goodstein's theorem (termination), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Curtis.no_polynomial_relation` | Curtis 1990, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `PowerTower.tower_converges_iff_full` | converges **iff** `x ∈ [e^-e, e^1/e]` (sharp), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.isConstructible_iff_constructiblePoint` | Wantzel iff, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.cbrt2_not_constructible` (+ trisection/nonagon/heptagon) | classical impossibilities, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |
| `Constructible.squaring_the_circle_impossible` | impossibility, **cond.** on `Transcendental ℚ π` | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms (hypothesis explicit) |
| `Constructible.squaring_the_circle_impossible_uncond` | impossibility, uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **axiom-clean** (uses `transcendental_pi_axiomClean`) |
| `Transcendence.transcendental_pi_axiomClean` | `π` transcendental (Lindemann 1882), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms — **fully proved (axiom deleted)** |
| `Transcendence.e_transcendental` (+ `transcendental_exp_{nat,int,rat}`) | `e`, `eⁿ`, `eᵃ`, `e^q` transcendental (Hermite 1873; rational-exponent Hermite–Lindemann), uncond. | `[propext, Classical.choice, Quot.sound]` | ✅ 0 math axioms |

**Math-axiom count (🟢+🟡+🟠): 0** (2026-09-28, re-run from real `#print axioms` this lap).
**Conditional headlines and their hypotheses** (hypotheses are explicit `Prop` arguments, never
axioms, so they do not show in `#print axioms` — this row is the honest accounting):
🟠 `Dubickas2022` (Lemma 6 ⇒ Corvaja–Zannier ⇒ `p`-adic Subspace Theorem) under the three Dubickas
headlines; 🟡 `BakerHarmanPintz2001` + `Matomaki2007` under the Saito/Mills transcendence and
irrationality theorems; 🟡 `PrimeBetweenCubesFrom` (Ingham) under least-Mills; 🟡 `Ridout1957/58`
under the Diophantine edges.  **No 🔴 anywhere**, and no unconditional theorem depends on an open
conjecture.  Dubickas's Lemma 8 (`Dubickas2022PisotGap`) was eliminated 2026-09-28.

**Math-axiom count (🟢+🟡+🟠): 0.** `grep '^axiom' src/` is empty and there is **no `sorry` in `src/`**. Every non-Goodstein-diagonal headline is the bare trust base `[propext, Classical.choice, Quot.sound]` — this includes all three merged threads (the kakeya `davies_kakeya_2d`, the shear no-three `hjsw_lower_bound`/`maxNoThreeInLine_bounds`, and the NT `mertens_first`/`sum_sigma0_isBigO_sqrt`/BV-Fourier headlines). Because `src/` is sorry-free with zero custom axioms, *every* `src/` theorem is necessarily trust-base — the table samples the headlines. The Goodstein diagonal-domination closures (`goodsteinLength_eventually_dominates_fastGrowing` and the per-level/tower variants) additionally carry **finite-base-case `native_decide` artifacts** (`goodsteinLength_base_cases._native.*`) — the computed lengths of the finitely many small Goodstein runs `4≤M<16`, a 🟢 finite/computational dependency excluded from the math-axiom count per the discharge doctrine. The proof *engines* (`towerN_le_fastGrowing`, `omegaTower_le_toOrdinal`, `exists_repr_lt_omegaTower`, …) are trust-base-clean. No 🟡/🟠/🔴 anywhere.

## Pointers
- Binding orders: **`DIRECTION.md` → CURRENT DIRECTIVE** (outranks every handoff) · open items / attack paths: **`PENDING_WORK.md`** · resume baton: newest `HANDOFF-*.md` (glob: `ls HANDOFF-*.md | sort -t p -k2 -n | tail -1`)
- Dubickas route write-up: **`PROBE-DUBICKAS-NOGAP.md`** (the readable form of the phase-8 proof)
- Frontier files (2026-09): `NumberTheory/Transcendence/Dubickas*.lean` (phase 7+8 ✅) · `NumberTheory/Mills/` (Saito Thm 1.1/1.2 ✅, Remark 4.4 open) · `NumberTheory/Diophantine/Edges.lean` (three edges ✅) · `NumberTheory/Catalan/` (phase 2 probe-first) · `Literature/Pisot.lean`, `Literature/Diophantine*.lean` (FROZEN hypothesis statements — never edit)
- Frontier files (Goodstein, complete): `Logic/FastGrowing/{Basic,Domination,Hardy}.lean` · `Logic/Goodstein/{Growth,Engine}.lean`
- Comparator pre-flight: `scripts/comparator-probe [Dubickas|Transcendence]`
- No `ON-LINE-REQUEST.md` open.

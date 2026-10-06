> 🎯 **CURRENT DIRECTIVE (2026-10-05): phase LF1, lacunary-Fibonacci bedrock.**  Branch `lacfib`, worktree `~/src/lean-formalizations-eplus`.  See the LF1 entry below.

## (phase LF1, PLANTED 2026-10-05, BEDROCK): **lacunary Fibonacci sums at the ratio-two boundary** - targets `NumberTheory/LacunaryFib/Basic.lean`, then `Boundary.lean`

Trevor 2026-10-05: "build some bedrock".  Context: Erdős #267 (irrationality for every `c > 1`) is Snyder 2026, kernel-checked here (`ErdosDyadic.Snyder2026Erdos267`).  Transcendence is Nguyen 2022 for `c > 2`, sharp at `c = 2` because `∑ 1/F_(2^k) = (7 − √5)/2`.  The new question is ours: **algebraic only by tiling** (`Boundary.RatioTwoRigidity`, `LacunaryFibAlgebraicIffDoubling`).

**Lap objective: make `Basic.lean` sorry-free, then the four wiring theorems in `Boundary.lean`.**  Each docstring carries its route.
- `Basic.lean`: `fib_inv_eq_tsum_of_even` (Binet), `fib_two_mul_inv` (Millin step, d'Ocagne), `millin` (telescoping, the control), `doubling_tail_algebraic`, `vTwo_eventuallyPeriodic_iff` (pure combinatorics), `restricted_sum_eq_tiling` (regroup by `m = 2^(v₂ m)·odd`).
- `Boundary.lean` wiring: `algebraic_of_eventually_doubling`, `transcendental_of_eventually_ratio`, `restricted_transcendental_of_sparse`, `restrictedRigidity_of_ratioTwoRigidity`.
- **Do not attack** `RatioTwoRigidity`, `RestrictedRigidity`, `MahlerPeriodicRestricted` or `LacunaryFibAlgebraicIffDoubling`.  They are frozen open nodes.  Statements frozen.  Mathlib has Binet (`Real.coe_fib_eq`), `Nat.fib_add_two_sub_fib_add_one`, `Nat.fib_dvd`, `goldenRatio`/`goldenConj` lemmas.

Difficulty check (crux, for later): proved, Nguyen `c > 2` (cited) plus the doubling direction (this phase).  Unproved, ratio-two rigidity.  Mechanism, none yet: the block-collapse idea in `RatioTwoRigidity`'s docstring reduces to block starts with ratio `> 2` but not bounded away from 2, the exact gap Nguyen leaves.  Control: `n_k = 2^k` is inside the hypothesis and algebraic.  **Update (Ren, same day):** on divisibility chains (`n k ∣ n (k+1)`) the crux follows from Roth, because partial sums have the single denominator `F_(n J)` (`DivChain.divChain_rigidity`, sorry, ~90%).  So `RestrictedRigidity` holds (`restrictedRigidity_holds`), Sturmian `K` included.  The real crux is non-divisible sequences such as `n_(k+1) = 2 n_k + 1`.  Next lap after the Boundary wiring: prove `DivChain.lean`.  ⚠️ Numerics are blind (`Basic.lean` header): lacunary sums are numerically finite sums.

> ✅ **Phase 65w DONE 2026-10-05 in one lap (`b1a140e`, main `94e1d8e`)**: `ShiftHitPrime.xi_shift_transcendental_of_hitPrime` proved (Lemma 8 + `HitPrime` + `HalfHitPrime` ⇒ E+ for θ < 2/3).  Phase 65 stopped at the hit-prime wall; reopen only with a hit-prime mechanism separating `f₀` and `f₂`.  No current directive.

> 🗺️ **Before planting a phase, grep `src/LeanFormalizations/Maze.lean`**: it records the routes already walked and closed, and each row's `reopenIf` names the new idea needed to walk it again (2026-09-29).

# DIRECTION — read FIRST (operator directive, 2026-09-27, Trevor via Ren)

## (phase Pr1, PLANTED 2026-10-05 on `main`, NOT launched): **practical-number bedrock** - target `src/LeanFormalizations/NumberTheory/Practical/Basic.lean`

New lane (Trevor, 2026-10-05: build practical-number machinery here).  Repo fit: Weingartner's `P(x) ~ c x/log x` runs through a Buchstab-type integral equation, and this repo already owns Buchstab's delay system and rough-number limits (`Erdos385/LinearSieve/DelaySolution.lean`, `RoughOmega.lean`, `RoughLimit.lean`) plus PNT.  formal-conjectures has `Nat.IsPractical` and the open statements (Erdős #18, OEIS A005153 Switkay, A017666); we do not depend on it, so `IsPractical` is restated (adds `0 < n`, like `OeisA5153.A`).

Already green: `IsPractical` (decidable), `sigma1`, `InB θ`, `partBelow`, `PrimePlusPracticalOdd` (def, OPEN), kernel-`decide` tests (`practical_below_31`, `isPractical_78`, `not_isPractical_10`, `window_hyp_8`, `primePlusPractical_le_17`).  Literature Props in `Literature/Practical.lean`: `Weingartner2015`, `Weingartner2019`, `PomeranceWeingartner2021` (Cor. 2, ineffective `x₀`), `PomeranceWeingartner2021Computation` (to `2^71`), `Melfi1996`.

Frozen statements to prove, easiest first.  In `Basic.lean`: `IsPractical.even_of_one_lt`, `isPractical_factorial`, `isPractical_iff_inB` (Stewart–Sierpiński), `isPractical_mul_of_le_sigma`, `primePlusPractical_window` (Pomerance–Weingartner Lemma 9).  Then the claims in `docs/notes/practical-numbers.md`: `Erdos18.lean` `card_le_pow_practicalH`, `practicalH_factorial_ge` (needs `log τ(n!) ≤ (C + o(1)) n / log n`, any constant `< 2` suffices; PNT is in the repo), `practicalH_le_of_dense`; `Constant.lean` `practicalBinary_irrational`, `practicalBinary_not_disjunctive_two`, `practicalBinary_not_disjunctive_two_pow`; `ShortIntervals.lean` `practical_near_sqrt`.  Done when `#print axioms` on all thirteen shows no `sorryAx`.  `erdos18a_of_lcmDivisorsDense` is optional (an edge to an open premise).  This is bedrock, so it is not the destination; the frontier candidates below are.

Frontier candidates (difficulty check, not yet chosen):
- **Margenstern odd case `PrimePlusPracticalOdd`**.  Proved: true for `n > x₀` (ineffective) and `n < 2^71`.  Unproved premise: an explicit `x₀ ≤ 2^71`, or `M(2^a) < 2^{2a+1}` for all large `a`.  Mechanism: none known.  The window route needs a prime `≡ n (mod m)` below about `m·σ(m) ≈ m² log log m`, and GRH only gives `≈ m² log² m`, so even GRH misses by a log factor (Ren's estimate, unchecked).  P–W §1 say ERH in place of Bombieri–Vinogradov gives some `x₀`, possibly too large to close by computation.
- **Erdős #18** (`h(n!) < (log n)^{O(1)}`, $250).  Explored 2026-10-05 in `Practical/Erdos18.lean`.  Counting gives `h(n) ≥ log n / log τ(n)`, hence `h(n!) ≳ (log n)²` (`practicalH_factorial_ge`).  The forum's greedy reduction (`practicalH_le_of_dense`) wires the open premise `LcmDivisorsDense` to (a) (`erdos18a_of_lcmDivisorsDense`).  Mechanism for the premise: none known.
- **Where `c` sits** (Trevor's question): `Practical/Constant.lean`.  Irrationality of `c` is open with no mechanism (`PracticalConstantIrrational`; Mertens/Artin/Brun tier).  The binary constant `Σ 2^{−n}` over practical `n` is irrational (`practicalBinary_irrational`, elementary, sorry) and its transcendence is open, like the prime constant.
- **Practical numbers in short intervals** (2026-10-05, `Practical/ShortIntervals.lean`).  Plugging Tao–Trudgian–Yang 2025's exponent pair into Weingartner 2021 Thm 2 gives `β > 0.486987…` (was `0.48711…`): `practicalShortInterval_tty`, proved from the two cited Props; optimizer `scripts/practical-exponent-opt.py`.  The gain is in the fourth decimal.  A real step needs a new architecture (Weingartner's split `n ~ x^{1/3}`, `m` `(x/n)^{3/4}`-smooth is forced optimal for this argument: `β = α + (1−α)b`, increasing in `α`, with `α ≥ 1/3`).  Elementary `θ = 1/2`: `practical_near_sqrt` (sorry).
- **Effective Weingartner**: an explicit `P(x) ≥ c₀ x/log x` for `x ≥ x₁`, the input an effective P–W `x₀` would need.  This reuses the Buchstab delay machinery directly.

## (phase 65, PLANTED 2026-10-05, MOONSHOT, branch `mills-eplus`, worktree `~/src/lean-formalizations-eplus`): **the 5/9 wall** - target `Mills/SaitoTypeBTheta.lean`

Previous status line: ✅ **Phase 64 DONE 2026-10-05**: 64a proved E+/Theorem E for every short-interval exponent `θ < 5/9` (frozen `θ < 2/3` keeps one `sorry` on `[5/9, 2/3)`, open node `ShiftPisotDegreeLeThree`); 64b kernel-checked `cm3_check` (`decide +kernel`) and `cert_all` (`E1CertCore` + table modules), so the E+ headlines (BHP and `θ < 5/9`) use only `propext`, `Classical.choice`, `Quot.sound`.  No current directive.

Goal: E+ for every short-interval exponent `θ < 2/3` (the frozen `xi_shift_transcendental_of_shortInterval`, now wired through the node and the edge below).  Trevor 2026-10-05: "attack".

### Difficulty check (soul rule: proved implications, unproved premise, mechanism, controls)

- **Proved**: `θ < 5/9` ⇒ E+ (`xi_shift_transcendental_of_shortInterval'`).  Decay along records: `‖ξ^(C k)‖ ≪ ξ^(−μ C k)` for every `μ < 2 − 3θ` (`saitoTypeB_shift_theta`, `card_mul_le_shift_theta`: `(#other conjugates)·μ ≤ 1`).  For `θ < 5/9`, `μ > 1/3` gives degree ≤ 3 and the cubic rigidity (`ShiftRigidity`, `HalfShiftRigidity`, `E1Certificate`) finishes.
- **Edge** `xi_shift_transcendental_of_degree`: the endgame given the degree bound.  Probably mostly bookkeeping: find every use of `hμ3 : 1/3 < μ` in `SaitoTypeBThetaParts.lean` and check it is used ONLY to get degree ≤ 3 (`card_le_two_of_records_theta`).  If the record step (`hT`, records every `T` steps) or `lower_along_records` also uses `μ > 1/3`, name that as a second node.  **Do the edge first.**
- **Node** `shiftPisotDegreeLeThree_holds` (the unproved premise): for `θ ∈ [5/9, 2/3)`, `μ` can be `≤ 1/3`, so `ℓ = deg β ≤ 1 + 1/μ` allows `ℓ ≥ 4`.  Note the node as stated is implied by E+ itself (algebraic least `ξ` is the hypothesis), so the real work is a **ξ-free obstruction**: state, as a new sorry theorem, "a Pisot `β` of degree `≥ 4` cannot have `Tr(β^(n_k)) = ⌊β^(n_k)⌋` prime for all large `k` along `n_(k+1) = 3 n_k + d` (with the decay)", or the strongest version you believe, then wire it into the node.
- **Control already on file**: `DecayDegreeFour.decay_admits_degree_four` (believed): decay alone admits quartic Pisot numbers (`X⁴ − aX³ − 1`).  **Any mechanism must use more than decay**; test each candidate against that family before building on it.
- **Candidate mechanisms** (none known to work; test, don't trust):
  1. *Sign/phase*: `⌊β^n⌋ = Tr(β^n)` forces `Σ_i γ_i^n ∈ (−1, 0]` on the orbit.  For the quartic control, the small conjugates are about `a^(−1/3)·(−1, e^(±iπ/3))`, so the sum's sign is a function of `n mod 6` and the orbit `n ↦ 3n + d`.  Compute (Python is fine, record the result as a Lean `decide`/statement) whether some `d` keeps the sign `≤ 0` forever; if yes, sign alone is insufficient (record as a control).
  2. *Dominant triple*: the HANDOFF's lead - with three conjugates near modulus `β^(−1/3)`, a lower bound on `|Σ γ_i^(n_k)|` along the orbit (analogue of `DominantPair.lower_along_records`) would contradict decay `μ` close to `1/3`.  Check what exponent it needs versus `2 − 3θ`.
  3. *Arithmetic*: prime traces mod small primes along `n ↦ 3n + d` (the `ShiftRigidity` 3-adic argument used `ℓ = 3` to get `3 | tr`; find what replaces it for `ℓ = 4, 5, …`), or a p-adic Skolem step as in `E2Skolem`.
- **Sibling sanity**: whatever closes the node must not also prove something believed false (e.g. it must not show that NO Pisot number of degree ≥ 4 has prime traces along some geometric-like orbit without using the decay).

Done when: `#print axioms SaitoTypeBTheta.xi_shift_transcendental_of_shortInterval` shows no `sorryAx`.  A stuck-bail with a recorded refutation or a sharper named node is an acceptable outcome; record closed routes as `Maze.lean` rows citing declarations.

**Lap 1 outcome (Mac crashed mid-lap 2026-10-05; uncommitted work salvaged by the operator session, build green, `232a72b`):** edge `xi_shift_transcendental_of_degree` proved (`77b8a02`).  Degree-ℓ rigidity node stated, `ℓ = 3` proved (`c24afd9`).  Then a degree-FREE wiring, `ShiftRigidityDeg.xi_shift_transcendental_of_nodes`, proved: eventual records + shift/half-shift rigidity in degree `≥ 3` give E+ for every `θ < 2/3` with no degree bound, via the new `SaitoTypeBThetaParts.saitoTypeB_shift_theta_gen` (record step parametric in `ρ, μ`).  The node `shiftPisotDegreeLeThree_holds` is now discharged vacuously through that wiring.  So the `5/9` wall split into two independent pieces: (a) **eventual records** for `θ ∈ [5/9, 2/3)` - this is where `μ > 1/3` was really used (`card otherConj ≤ 2` feeding `lower_along_records`), and (b) **ξ-free rigidity in degree `≥ 4`** - the cubic 3-adic + spectral argument generalised.  (a) is the weakest point and the crux; it must beat the `DecayDegreeFour` control (decay alone admits degree 4).

**Operator probe after lap 1 (2026-10-05, `ShiftRigidityDeg.eventuallyRecordShift_of_pisotGap`, stated ~85%, English proof in the docstring):** candidate mechanism 1 (sign/phase) is **obsolete, not refuted**.  It targeted the old degree node, and floor = trace (the sign) is already a hypothesis on records.  What a non-record needs is cancellation `|Σ γ_iⁿ| < β^(−n)` (`nonrecord_ineq`, `c ≥ 2`), and `Dubickas2022PisotGap` (`|Σ γ_iⁿ| ≥ Rⁿ n^(−λ)`, `R ≥ β^(−1/L)`) rules that out in every degree `L ≥ 2`.  So **with Lemma 8 the records crux closes** (`xi_shift_transcendental_of_pisotGap`, wiring only), and the wall is then only the ξ-free rigidity `shiftTraceRigidity_ge_four` / `halfShiftTraceRigidity_ge_four`.  The frozen route has avoided Lemma 8 since 2026-09-28, so `eventuallyRecordShift_holds` stays open.  A Lemma-8-free proof needs a lower bound for `|Σ γ_iⁿ|` at a one-step non-record along `n ↦ 3n − d` that avoids Baker.

**Laps 2-3 outcome (supervisor reaped by Claude Code under memory pressure at 15:07 mid-lap-3; staged work salvaged by the operator session, build green, `459a8ac`):** records leaf proved (`0ef6ffc`).  Lap 2 refuted the 3-adic route on the unipotent class: `f₀ = X⁴ − 4X³ − X + 1 ≡ (X − 1)⁴`, `s = −1`, satisfies every 3-adic constraint (`unipotent_trace_congr`, kernel; Maze row; node `UnipotentCovering`, Fermat-number-like).  Lap 3 ported window/Teichmüller/spectral to any degree (`window_shift_any`, `exists_teich_limit_any`, `exists_spectral_any`), then its sibling check refuted the same route on the GENERIC leaf: `f₁ = X⁴ − 8X³ − 5X² + 6X + 3 ≡ X²(X − 1)²`, Pisot β ≈ 8.5, `tr C^(3^n − 1) ≡ −1 (mod 3^(n+1))` (`generic_trace_congr_le_nine`, native, n ≤ 9; all-n `generic_trace_congr` ~95% and `pisot_f₁` ~99% are sorries), spectral solution `u = (1,1,0,0)` from a pair relation among reciprocal roots.  Lap 3's own next-step candidates (PENDING_WORK): characterise the 3-adically consistent generic instances (does a pair relation force a factorisation over a quadratic field after reversal?), and test whether the sharper window `3^(n+1) | ord(C mod p)` separates `f₁`.  Difficulty locus: no non-3-adic mechanism is known; covering primes are the only candidate and are open in the Fermat analogue.

**Phase 65 STOPPED at the hit-prime wall (operator, 2026-10-05, after laps 4-5 of the second run confirmed a stuck-bail, `bb42d5a`):** lap 4 killed `f₁` by the `q`-power class (`f₁ ≡ (X²+X+1)² mod 2`, every trace even) but found survivor `f₂ = X⁴ − 5X³ − 8X² − 6X − 3`, `s = −1`, which escapes both 3-adic and power-class inputs and dies only by a hit prime (`C₂_hit_seven`).  Node `ShiftRigidityUnipotent.HitPrime` (a fixed prime dividing infinitely many `tr C^(3^n + s)`) closes the shift leaves (`not_primeTraces_of_hitPrime`); lap 5 checked self-hit and Newton-at-previous-prime inputs, neither new.  No mechanism for `HitPrime` is known (no fixed prime divides infinitely many Fermat numbers, so a proof must use more than the exponent shape).  Outcome recorded as Lean data in `Mills/ShiftHitPrime.lean`: `HalfHitPrime` (half-shift twin) and the headline `xi_shift_transcendental_of_hitPrime` (Lemma 8 + `HitPrime` + `HalfHitPrime` ⇒ E+ for θ < 2/3), wiring planted as phase 65w.  Reopen phase 65 only with a named hit-prime mechanism that separates `f₀` and `f₂`.

## (phase 64, PLANTED 2026-10-05, branch `mills-eplus`, worktree `~/src/lean-formalizations-eplus`): **E+ on a weaker prime input, then three-core-axiom tightening**

Previous status line: ✅ **Phase 63 DONE 2026-10-05**: `BHPTests.lean` sorry-free, all names free of sorryAx (no frozen statement was false). No current directive.

Trevor named Theorem E+ for external sharing.  Two parts, run sequentially (64b is planted after 64a finishes).

### 64a - E+ from `θ < 2/3` (new mathematics; target `Mills/SaitoTypeBTheta.lean`)

The BHP exponent `21/40` enters E+ only through Saito's Lemma 5.3 (`SaitoTypeBParts.lean`, "Saito Lemma 5.3 at θ = 21/40, ratios ≥ 29/10"), as `1/(1 − θ) + ε ≤ r` with `r` a lower bound on `C(k+1)/C k`.  For `C = 3^k + s` the ratios tend to `3`, so `θ < 2/3` should suffice with `r` chosen in `(1/(1−θ), 3)` and the record lemmas applied eventually in `k`.

Frozen statements (namespace `LeanFormalizations.Mills.SaitoTypeBTheta`):
1. `ingham_iff` (`Iff.rfl`, done) and `ingham_of_bhp` (sanity: BHP → `Ingham1937`, via `BHPTests.PrimesShortInterval.mono` since `21/40 < 5/8`).
2. `xi_shift_transcendental_of_shortInterval` (`0 < θ < 2/3`, `PrimesShortInterval θ`, `Dubickas2022`): the main work.  Suggested route: generalize the `θ = 21/40`-specific lemmas in `SaitoTypeBParts.lean` / `SaitoTypeBRecords.lean` / `SaitoTypeBNoGap.lean` to a parameter `θ` (new `θ`-parametric copies or generalize in place; the existing BHP-named theorems must keep their statements and stay proved, e.g. by specializing the parametric version).  `PrimesShortInterval.mono` lets you raise `θ` (e.g. to `max θ (21/40)`) if a step wants `θ ≥ 1/2`.
3. `xi_shift_transcendental_ingham`: from 2 with `θ = 13/20 ∈ (5/8, 2/3)`.
4. `xi_shifted_transcendental_ingham` (Theorem E, `s = −2`): mirror `SaitoTypeB.xi_shifted_transcendental_classical`.

Done when: `#print axioms` on all four shows no `sorryAx`.

**64a outcome (2 laps, merged to main `96697d3`):** E+ and Theorem E proved for every `θ < 5/9` (`xi_shift_transcendental_of_shortInterval'`, `xi_shifted_transcendental_of_shortInterval'`; covers BHP).  The frozen `θ < 2/3` statement keeps one `sorry` on `[5/9, 2/3)`: the decay exponent `μ < 2 − 3θ` reaches the degree-3 endgame only when `μ > 1/3`.  Open node `ShiftPisotDegreeLeThree`; control `DecayDegreeFour.decay_admits_degree_four` (believed) says decay alone admits Pisot degree 4.  So the Ingham headlines still sit on that `sorry` (`5/8 > 5/9`).

### 64b - three-core-axiom tightening (DONE 2026-10-05, one lap)

Replace the two `native_decide`s on E+'s path (`E1Certificate.cert_all`, `ShiftRigidity.cm3_check`) with kernel-checked proofs (`decide +kernel`, or a structured argument that cuts the case count), so `#print axioms` on the E+ headlines shows only `propext`, `Classical.choice`, `Quot.sound`.  Statements unchanged.

## ✅ (phase 63, DONE 2026-10-05 in one lap; PLANTED 2026-10-05, branch `mills-eplus`, worktree `~/src/lean-formalizations-eplus`): **stress-test the BHP literature Prop** - target `src/LeanFormalizations/NumberTheory/PrimeIntervals/BHPTests.lean`

Theorem E+ rests on `BakerHarmanPintz2001` (`Literature/Primes.lean`).  A literature Prop stated too strongly is false and makes E+ vacuous, so this phase checks the definition against known answers.  Previous status line: ✅ **Phase 62 DONE 2026-10-05**: Theorem E+ now rests only on `BakerHarmanPintz2001` + `Dubickas2022` (`SaitoTypeB.xi_shift_transcendental_classical`, no sorryAx; Baker eliminated for the `3^k + s` family via Skolem-Mahler-Lech for order-3 recurrences).  `saitoTypeBLeast_holds` (Saito's general-`C` statement) stays a frozen OFF-path hole: it needs Baker (`Dubickas2022PisotGap`) and nothing consumes it.  No current directive.

Frozen statements (all in namespace `LeanFormalizations.BHPTests`):
1. `primesIn` unit tests, hand-counted: `primesIn_10_20` (= 4), `primesIn_10_5_13` (= 2), `primesIn_24_28` (= 0), `primesIn_2_2` (= 1), `primesIn_neg5_3` (= 2, negative left end clamps to 0), `primesIn_reversed` (= 0).  Unfold `primesIn`, compute the ceil/floor (`Nat.ceil_eq_iff`, `Nat.floor_eq_iff`, `norm_num`), then `decide`.
2. `PrimesShortInterval θ` (def) and `bhp_iff` (`Iff.rfl`, already proved).
3. **False sibling** `not_primesShortInterval_zero`: `x ^ (0:ℝ) = 1`; take `x = n! + 2` with `n ≥ 3` large enough that `x ≥ X`; `n!+2` and `n!+3` are composite (`Nat.dvd_factorial`), so `primesIn x (x+1) = 0`, while `d₀ / log x > 0`.
4. **True sibling** `primesShortInterval_one`: `primesIn x (2x) ≥ π(⌊2x⌋) − π(⌈x⌉ − 1)`; use `prime_number_theorem` (`NumberTheory/PrimeNumberTheorem/PNT.lean`) to get `π(2x) ≥ (2 − ε)·x/log(2x)` and `π(x) ≤ (1 + ε)·x/log x` eventually; `d₀ = 1/2` works.  Chebyshev bounds are an acceptable alternative route.
5. **Monotone** `PrimesShortInterval.mono` (`0 < θ ≤ θ' ≤ 1`): tile `[x, x + x^θ']` by disjoint windows `[y_i, y_i + y_i^θ]` (step past the right end by 1 to keep the integer sets disjoint), `x ≤ y_i ≤ 2x`, count ≈ `x^(θ'−θ)/2^θ − 1`, each window ≥ `d₀ y^θ/log y ≥ d₀ x^θ/log(2x)`.  Any proof is fine; a cleaner route is welcome.
6. `exists_prime_of_bhp`: from `h`, for `x ≥ max X 2`, the count is positive so the filtered `Finset` is nonempty.
`primesShortInterval_one_of_bhp` is already wired from `mono`.

Done when: `#print axioms` on every listed name shows no `sorryAx`.

## ✅ (phase 62, DONE 2026-10-05 in 5 laps; both classical headlines free of sorryAx; Baker-free route via `SaitoTypeBRecords`/`SaitoTypeBNoGap`/`E2Skolem`; `saitoTypeBLeast_holds` left as an OFF-path frozen hole (general `C` needs Baker), primed `xi_shift_transcendental_classical'` adds `Dubickas2022PisotGap`; PLANTED 2026-10-05, branch `mills-eplus`, worktree `~/src/lean-formalizations-eplus`): **discharge `Saito2025TypeBTrace` for E+: Saito's Type B argument in Lean from Baker–Harman–Pintz + Dubickas 2022 Lemma 6** (Trevor: remove the single-Prop risk under Theorem E+) - target `src/LeanFormalizations/NumberTheory/Mills/SaitoTypeB.lean`.  Frozen: def `SaitoTypeBLeast` (given least `ξ`, no existence, so Matomäki drops out), `saitoTypeBLeast_holds (hB : BakerHarmanPintz2001) (hD : Dubickas2022)` (THE work, route in the header: (3.1) from (B5′), §5.1 dichotomy Lemmas 5.1–5.3 adapting the Saito-2024 proofs in `Irrational.lean`/`SaitoDigits.lean`, Lemma 6.1/5.7/6.2, Prop 3.1(ii)-(iv), ℓ = 3), `xi_shifted_transcendental_classical` (Theorem E corollary, set equality `shiftC 0 (-2) = shiftedC` on `k ≥ 1`); already proved: `saitoTypeBLeast_of_saito`, `xi_shift_transcendental_of_typeB`, `xi_shift_transcendental_classical`.  Frozen also: all earlier statements, everything in `Literature/`.  A further cited input goes in a parallel primed statement, never an edit.  Stop: `xi_shift_transcendental_classical` and `xi_shifted_transcendental_classical` free of `sorryAx`.

## ✅ (phase 61, DONE 2026-10-05 in 5 laps over two runs, `xi_shift_transcendental` + `xi_shifted_transcendental_saito` free of sorryAx; node C in `Mills/ShiftRigidity.lean` + `E1Certificate.lean`, node D in `Mills/HalfShiftRigidity.lean`; PLANTED 2026-10-04, branch `mills-eplus`, worktree `~/src/lean-formalizations-eplus`): **NEW MATH: Theorem E+, `ξ(3^k + s)` transcendental for EVERY `s ≠ 0`** (our `PROOF-THEOREM-E.md` drafts 2–3e, four referee passes, ~70%; phases 58–59 covered only even `s` with 3-free part `≥ 8`, by size) - target `src/LeanFormalizations/NumberTheory/Mills/ShiftedMillsAll.lean`.  Frozen: defs `shiftC`, `ShiftTraceRigidity`, `HalfShiftTraceRigidity`; theorems `shiftedTraceRigidity_of_shift` (edge onto phase 45's node, trivial, do first), `xi_shift_transcendental_of_rigidity` (elementary wiring: Saito hypotheses, `(B5′)`, `g ∈ {3^b, 2·3^b}`, ~95%, do second), `shiftTraceRigidity_holds` (Steps 3–6 for every `s ≠ 0`, ~75%, the heavy node: filter, window, Galois rigidity, mod-3 congruence, E1 certificate), `halfShiftTraceRigidity_holds` (the `g = 2` section for odd `s`, ~72%); the headlines `xi_shift_transcendental` and `xi_shifted_transcendental_saito` (Theorem E, closes phase 45) are already proved from those four.  Route in the file header, step by step, with the phase 44–60 lemmas to reuse.  Only literature input: `Saito2025TypeBTrace`.  Frozen also: all earlier statements, everything in `Literature/`.  Decomposing nodes C/D into named sub-lemmas (new `Mills/` files welcome) is progress; a refutation is progress too (prove `¬`, add a `Maze.lean` row, and stop).  Stop: `ShiftedMillsAll.lean` sorry-free.

## ✅ (phase E10, DONE 2026-10-01 in one lap, all eight statements axiom-clean (463 power saving mod the E9 literature Props; the GoldbachWindow reductions unconditional); PLANTED 2026-10-01, branch `erdos-385-d`, worktree `~/src/lean-formalizations-385d`): **the remainder, stated** - target `src/LeanFormalizations/NumberTheory/Erdos385/Remainder.lean`.  Frozen: `almost_all_erdos463_powerSaving` (E6's shifted window on the E9 pipeline, 85%); the edges `erdos385_ii_of_downMargin`, `erdos463_of_upMargin`, `hyperbolaPrimePairs_of_downMargin_zero`, `goldbach_of_goldbachWindow` (elementary, do first); and `hyperbolaPrimePairs_of_goldbachWindow`, `ees_of_goldbachWindow`, `erdos463_of_goldbachWindow` (the `N = 2√n + 2t` reduction in the header, 75% each).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: Remainder.lean and `Erdos385/Remainder/` sorry-free.

## ✅ (phase E9, DONE 2026-10-01 (≈5 laps over two stints), `almost_all_F385_powerSaving` + `badCount_powerSaving` axiom-clean mod the three Literature Props, Hyperbola.lean fully proved; headline re-routed through `localZeroDetect_of_richert` + `largeValueCount_of_zeroDetect` (P^{η/3} window); the planted `nearOneLargeValues_of_density` stays a frozen OFF-path hole judged ~10% (Maze `SlowMellinWeight`); PLANTED 2026-10-01, branch `erdos-385-c`, worktree `~/src/lean-formalizations-385c`): **NEW MATH: a power saving for Theorem A and the bad set, plus the binary reformulation** - two targets.  (a) `src/LeanFormalizations/NumberTheory/Erdos385/Hyperbola.lean` (cheap, elementary): frozen `good_iff_exists_prime_floor`, `good_of_prime_pair`, `eventually_not_bad_of_hyperbolaPrimePairs`, `erdos430_of_hyperbolaPrimePairs`; do these first.  (b) `src/LeanFormalizations/NumberTheory/Erdos385/PowerSaving.lean` (the crux): frozen `almost_all_F385_powerSaving`, `badCount_powerSaving` (`≪ X^{1−c}`, from `RichertZetaGrowth`, `NearOneZeroDensity`, `ShortIntervalPrimesLower`), and the named sub-lemma `nearOneLargeValues_of_density` (80%; a disclosed hole there is an acceptable finish).  Route in the header: split frequencies by the size of the short prime sum; far part in mean square (power saving by definition + MVT), near part pointwise (near-1 density).  New literature Props `NearOneZeroDensity`, `ShortIntervalPrimesLower` in `Literature/Erdos385VK.lean`.  Frozen also: all earlier statements, everything in `Literature/`.  Stop: both files and `Erdos385/{Hyperbola,PowerSaving}/` sorry-free.  Phase E8 runs concurrently on branch `erdos-385-b` (QuasiPower.lean): touch only these files (+ helpers under `Erdos385/Hyperbola/`, `Erdos385/PowerSaving/`).

## ✅ (phase E8, DONE 2026-10-01 in two laps, both axiom-clean and UNCONDITIONAL, by a new window route (positions near Y = y^{9/4} with a deterministic linear-sieve population, minimal-prime expansion, no tail bound; `QuasiPower/`), not the Freedman plan; PLANTED 2026-10-01, branch `erdos-385-b`, worktree `~/src/lean-formalizations-385b`): **MOONSHOT: the bad-n bound toward the framework ceiling** - target `src/LeanFormalizations/NumberTheory/Erdos385/QuasiPower.lean`, frozen `badCountExp_threeQuarters` (milestone, exponent 3/4−ε) and `badCountQuasiPower_holds` (X exp(−c log X/(log log X)²)), both unconditional.  Route in the header (large sieve with j ≍ log X/(log log X)² primes; Freedman/Bernstein martingale on an equidistribution good event in place of McDiarmid).  A found gap is progress: name it, record the exponent that survives.  Frozen also: all earlier statements, everything in `Literature/`.  Stop: QuasiPower.lean and `Erdos385/QuasiPower/` sorry-free.  Phase E7 runs concurrently on branch `erdos-385-a` (DensityEES.lean): touch only QuasiPower.lean (+ helpers under `Erdos385/QuasiPower/`).
## ✅ (phase E7, DONE 2026-10-01 in one lap, all four axiom-clean mod `RichertZetaGrowth`; diagonal needs no tail split since `B_k` is increasing: `E ∩ [0,X] ⊆ B_{κ(X)}`; PLANTED 2026-10-01, branch `erdos-385-a`, worktree `~/src/lean-formalizations-385a`): **NEW MATH: Erdős–Eggleton–Selfridge for almost all n** - target `src/LeanFormalizations/NumberTheory/Erdos385/DensityEES.lean`, frozen `F_le_add_sqrt`, `density_one_EES` (formal-conjectures `erdos_385.variants.lb` off a density-zero set), `F_sub_div_sqrt_tendsto_one`, `F_sub_tendsto_atTop`, all from `RichertZetaGrowth`.  Route in the header (diagonalize `almost_all_F385_of_richert` over δ → 0).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: DensityEES.lean and `Erdos385/DensityEES/` sorry-free.  Phase E8 runs concurrently on branch `erdos-385-b` (QuasiPower.lean): touch only DensityEES.lean (+ helpers under `Erdos385/DensityEES/`).

## ✅ (phase E4c, DONE 2026-10-01 in one lap, `arithLargeSieveWeak_holds` axiom-clean with `C = 3 + 24π`; helpers `Erdos385/LargeSieve/{Montgomery,Gallagher}.lean`; PLANTED 2026-10-01, branch `erdos-385`, worktree `~/src/lean-formalizations-erdos385`): **the arithmetic large sieve** - target `src/LeanFormalizations/NumberTheory/Erdos385/LargeSieve.lean`, frozen `arithLargeSieveWeak_holds : ArithLargeSieveWeak` (new `Literature/Erdos385LargeSieveWeak.lean`: unspecified constant; the sharp `ArithLargeSieve` needs Selberg's majorant and is not targeted).  Route in the header (Gallagher + Montgomery's lemma).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: LargeSieve.lean sorry-free.  Phase E4 runs concurrently on branch `erdos-385-brun` (Exceptional.lean): touch only LargeSieve.lean (+ helpers under `Erdos385/LargeSieve/`).

## ✅ (phase E6, DONE 2026-10-01 in one lap, `almost_all_erdos463` axiom-clean; shifted-window W2 `card_shift_le` + `coeffA_ne_zero_witness`, coefficient δ fixed at 1/8 independent of the margin; PLANTED 2026-10-01, branch `erdos-385-brun`, worktree `~/src/lean-formalizations-erdos385-brun`): **NEW MATH: Erdős #463 for almost all n** - target `src/LeanFormalizations/NumberTheory/Erdos385/Erdos463.lean`, frozen `almost_all_erdos463` (margin `δ√n`, from `RichertZetaGrowth`).  Route in the header (E3's W1/W2 with the witness window shifted above `n`).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: Erdos463.lean sorry-free.  Phase E5 runs concurrently on branch `erdos-385` (LinearSieve.lean): touch only Erdos463.lean (+ helpers under `Erdos385/Erdos463/`).

## ✅ (phase E5, DONE 2026-10-01 (3 laps), `linearSieveIntervalLower_holds` axiom-clean; merged brun and composed `BadCount.badCountExpBound_holds` (UNCONDITIONAL); PLANTED 2026-10-01, branch `erdos-385`, worktree `~/src/lean-formalizations-erdos385`): **the linear-sieve lower bound** (Jurkat–Richert, interval case) - target `src/LeanFormalizations/NumberTheory/Erdos385/LinearSieve.lean`, frozen `linearSieveIntervalLower_holds`.  Route in the header (Selberg upper sharp for s ≤ 2 + Buchstab + fundamental lemma + Mertens; constants must be asymptotically sharp).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: LinearSieve.lean sorry-free.  Phase E4d runs concurrently on branch `erdos-385-brun` (ExceptionalWeak.lean): touch only LinearSieve.lean (+ helpers under `Erdos385/LinearSieve/`).

## ✅ (phase E4d, DONE 2026-10-01 in one lap, both statements axiom-clean; helpers `Erdos385/ExceptionalWeak/{Sieve,Count,Main}.lean`; PLANTED 2026-10-01, branch `erdos-385-brun`, worktree `~/src/lean-formalizations-erdos385-brun`): **E4 from the linear sieve alone** - target `src/LeanFormalizations/NumberTheory/Erdos385/ExceptionalWeak.lean`, frozen `badCountExpBound_of_weak`, `badCountExpBound_of_linearSieve`.  Route in the header (constant-carrying copies of `sieve_count`, `bad_count_le`, `eventually_bad_le`).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: ExceptionalWeak.lean sorry-free.  Phase E5 runs concurrently on branch `erdos-385` (LinearSieve.lean): touch only ExceptionalWeak.lean (+ helpers under `Erdos385/ExceptionalWeak/`).

## ✅ (phase E4b, DONE 2026-10-01 in one lap, `mcDiarmidFinite_holds` axiom-clean; helpers `Erdos385/McDiarmid/{Hoeffding,Core}.lean`; PLANTED 2026-10-01, branch `erdos-385`, worktree `~/src/lean-formalizations-erdos385`): **discharge `Literature.McDiarmidFinite`** - target `src/LeanFormalizations/NumberTheory/Erdos385/McDiarmid.lean`, frozen `mcDiarmidFinite_holds` (finite-average induction + Hoeffding's lemma + Chernoff; route in the header).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: McDiarmid.lean sorry-free.  Phase E4 runs concurrently on branch `erdos-385-brun` (Exceptional.lean): touch only McDiarmid.lean (+ helpers under `Erdos385/McDiarmid/`).

## ✅ (phase E4, DONE 2026-10-01 in one lap, `badCountExpBound_of_lit` axiom-clean (NEW MATH), helpers in `Erdos385/Exceptional/`; PLANTED 2026-10-01, branch `erdos-385-brun`, worktree `~/src/lean-formalizations-erdos385-brun`): **NEW MATH: the bad set is exponentially thin** - target `src/LeanFormalizations/NumberTheory/Erdos385/Exceptional.lean`, frozen `badCountExpBound_of_lit : ArithLargeSieve → LinearSieveIntervalLower → McDiarmidFinite → BadCountExpBound` (`#{bad n ≤ X} ≪ X exp(−(log X)^{1/2−ε})`); new literature Props in `Literature/Erdos385Exceptional.lean`.  Route in the header (DOOR-EXCEPTIONAL A2, 75% the outline closes; a found gap is progress, name it).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: Exceptional.lean sorry-free.  Phase E3e runs concurrently on branch `erdos-385` (PNTFromVK.lean): touch only Exceptional.lean (+ helpers under `Erdos385/Exceptional/`).

## ✅ (phase E2e, DONE 2026-10-01 in one lap, `vkZeroFreeLogDeriv_of_richert` + `almost_all_F385_of_richert` axiom-clean, helpers in `Erdos385/Landau/`; PLANTED 2026-10-01, branch `erdos-385-brun`, worktree `~/src/lean-formalizations-erdos385-brun`): **Vinogradov–Korobov from Richert's growth bound** (Landau's method) - target `src/LeanFormalizations/NumberTheory/Erdos385/Landau.lean`, frozen `vkZeroFreeLogDeriv_of_richert`, `almost_all_F385_of_richert`; new literature Prop `Literature.RichertZetaGrowth` in `Literature/Erdos385VK.lean`.  Route in the header (Titchmarsh 3.10/3.11; mathlib Borel–Carathéodory; PNT+ StrongPNT helpers, avoiding its sorried lemmas).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: Landau.lean sorry-free.  Phase E3d runs concurrently on branch `erdos-385` (RateVK.lean): touch only Landau.lean (+ helpers under `Erdos385/Landau/`).

## ✅ (phase E3e, DONE 2026-10-01 in one lap, `dlvpStatement_of_VK` + `almost_all_F385_rate_of_VK` axiom-clean; merged E2e and composed `Endpoint.almost_all_F385_rate_of_richert`; PLANTED 2026-10-01, branch `erdos-385`, worktree `~/src/lean-formalizations-erdos385`): **de la Vallée Poussin PNT from VK** - target `src/LeanFormalizations/NumberTheory/Erdos385/PNTFromVK.lean`, frozen `dlvpStatement_of_VK`, `almost_all_F385_rate_of_VK`.  Route in the header (E3's contour shift at a free height `T < P`, smooth sandwich, `η = exp(−2c√log x)`).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: PNTFromVK.lean sorry-free.  Phase E2e runs concurrently on branch `erdos-385-brun` (Landau.lean): touch only PNTFromVK.lean (+ helpers under `Erdos385/PNTFromVK/`).

## ✅ (phase E3d, DONE 2026-10-01 in one lap, `almost_all_F385_rate_VK` axiom-clean; helpers `Erdos385/RateVK/{General,RateGen}.lean` = E3 copied at exponent `a`; PLANTED 2026-10-01, branch `erdos-385`, worktree `~/src/lean-formalizations-erdos385`): **the sharp rate exp(−(log X)^{1/3−ε})** - target `src/LeanFormalizations/NumberTheory/Erdos385/RateVK.lean`, frozen `almost_all_F385_rate_VK` (from `VKZeroFreeLogDeriv` + new `Literature.DLVPStatement`).  Route in the header: re-parametrise E3 at `T₀ = exp((log Z)^{1/3})` with parametrised copies, never editing frozen statements.  Frozen also: all earlier statements, everything in `Literature/`.  Stop: RateVK.lean sorry-free.  Phase E2e runs concurrently on branch `erdos-385-brun` (Landau.lean): touch only RateVK.lean (+ helpers under `Erdos385/RateVK/`).

## ✅ (phase E2d, DONE 2026-10-01 in 2 laps, `mr16Lemma14_holds` axiom-clean, helpers in `Erdos385/Parseval/`; merged E3 in and composed `Headline.almost_all_F385_of_VK : VKZeroFreeLogDeriv → AlmostAllF385`, axiom-clean; PLANTED 2026-10-01, branch `erdos-385-brun`, worktree `~/src/lean-formalizations-erdos385-brun`): **discharge `Literature.MR16Lemma14`** - target `src/LeanFormalizations/NumberTheory/Erdos385/ShortSumParseval.lean`, 1 frozen statement `mr16Lemma14_holds` (Plancherel-in-log-coordinates route in the header; mathlib `Lp.norm_fourier_eq`).  Afterwards E3's headline depends only on `VKZeroFreeLogDeriv`.  Frozen also: all earlier statements, everything in `Literature/`.  Stop: ShortSumParseval.lean sorry-free.  Phase E3 runs concurrently on branch `erdos-385` in another worktree: touch only ShortSumParseval.lean (+ new helper files under `Erdos385/Parseval/` if needed).

## ✅ (phase E2c, DONE 2026-10-01 in one lap: all 3 axiom-clean, MVT via Fejér majorant in `Erdos385/MeanValue.lean`; PLANTED 2026-10-01, branch `erdos-385-brun`, worktree `~/src/lean-formalizations-erdos385-brun`): **discharge literature Props** - target `src/LeanFormalizations/NumberTheory/Erdos385/Discharge.lean`, 3 frozen statements: `card_bad_le_unconditional` (one line from `card_bad_le brunUniformGap_holds`), `mediumPNTStatement_holds` (PNT+ `MediumPNT`; add the import, long first build expected), `montgomeryVaughanMVT_holds` (Fejér-weight route in the header).  Frozen also: all earlier statements, everything in `Literature/`.  Stop: Discharge.lean sorry-free.  Phase E3 runs concurrently on branch `erdos-385` in another worktree: touch only Discharge.lean (+ new helper files under `Erdos385/MVT/` if needed).

## ✅ (phase E2b, DONE 2026-10-01 in one lap, `brunUniformGap_holds` axiom-clean, helpers in `Erdos385/Brun/`; PLANTED 2026-10-01, branch `erdos-385-brun`, worktree `~/src/lean-formalizations-erdos385-brun`): **discharge `Literature.BrunUniformGap`** (side quest: makes `card_bad_le` unconditional) - target `src/LeanFormalizations/NumberTheory/Erdos385/BrunPairs.lean` (1 frozen statement `brunUniformGap_holds`; Selberg-sieve route in header via `Mathlib/NumberTheory/SelbergSieve.lean`).  Frozen also: all earlier statements, Literature/ (do NOT edit `BrunUniformGap`); stop: BrunPairs.lean sorry-free.  Phase E3 runs concurrently on branch `erdos-385` in another worktree: touch only BrunPairs.lean (+ new helper files under `Erdos385/Brun/` if needed).

## (phase E3, PLANTED 2026-10-01, branch `erdos-385`): **Erdős #385 almost-all: `F(n) ≥ n + (1 − δ)√n` for almost all `n`** (new math; Tao's 2024 "within reach" remark, sharper) - target `src/LeanFormalizations/NumberTheory/Erdos385/AlmostAll.lean` (defs `ShortIntervalPNT`, `SmoothPrimeSumVK`, `Admissible`, `coeffA`, `shortSum`, `param*`, `variance`, `badWindow` + frozen statements: edges `shortIntervalPNT_of_mediumPNT`, `smoothPrimeSumVK_of_VKZ`; controls `not_shortIntervalPNTUnitWindow`, `not_smoothPrimeSumVKMRNorm_of_VK`; wiring W0 `exists_admissible`, W1 `witness_margin`, W2 `card_badWindow_le`, W2′ `longAverage_lower`, W3 `variance_small`; headline `almost_all_F385` (concludes the Graph node `AlmostAllF385`)); route in header, scaffolding `PROOF-ERDOS-385-ALMOST-ALL.md` on `main` (Lean parameters: `T₀ = exp(κ (log Z)^{1/10})`, the MediumPNT choice).  Literature inputs (statements only, `src/LeanFormalizations/Literature/Erdos385AlmostAll.lean`): `MR16Lemma14`, `MontgomeryVaughanMVT`, `VKZeroFreeLogDeriv`, `MediumPNTStatement` (dischargeable from PNT+ `MediumPNT`, not wired: olean unbuilt at this pin), each with a known-false control `not_…` to prove (teeth tests).  Order: W0, W1, W2 (elementary) first; then W2′ and the PNT edge; then W3 and the headline; the VK edge last (contour argument, port PNT+'s smoothed-Chebyshev code).  Frozen also: all earlier statements, Literature/; stop: AlmostAll.lean sorry-free (the Literature Props stay hypotheses).  **Decomposing into named sub-lemmas is progress**; a hard leaf may stay a NAMED `sorry` with an English paragraph and a confidence.
## (phase E3c, PLANTED 2026-10-01, branch `erdos-385`, worktree `~/src/lean-formalizations-erdos385`): **a rate for Theorem A** - target `src/LeanFormalizations/NumberTheory/Erdos385/Rate.lean`, 1 frozen statement `almost_all_F385_rate` (`#{n ≤ X : F n < n + (1−δ)√n} ≤ C X exp(−c (log X)^{1/10})` from the same 4 literature Props; dyadic-window route in the header, all pieces already in `AlmostAll.lean`).  Frozen also: every statement in `AlmostAll.lean` and earlier, everything in `Literature/`.  Stop: Rate.lean sorry-free.  Phase E2d runs concurrently on branch `erdos-385-brun` in another worktree (ShortSumParseval.lean); touch only Rate.lean here. **✅ DONE 2026-10-01: Rate.lean sorry-free, axiom-clean mod the 4 Props.**

## ✅ (phase E3, DONE 2026-10-01, `e819725`; `almost_all_F385` axiom-clean modulo the 4 literature Props): (planted 2026-10-01, branch `erdos-385`) **Erdős #385 almost-all: `F(n) ≥ n + (1 − δ)√n` for almost all `n`** (new math; Tao's 2024 "within reach" remark, sharper) - target `src/LeanFormalizations/NumberTheory/Erdos385/AlmostAll.lean` (defs `ShortIntervalPNT`, `SmoothPrimeSumVK`, `Admissible`, `coeffA`, `shortSum`, `param*`, `variance`, `badWindow` + frozen statements: edges `shortIntervalPNT_of_mediumPNT`, `smoothPrimeSumVK_of_VKZ`; controls `not_shortIntervalPNTUnitWindow`, `not_smoothPrimeSumVKMRNorm_of_VK`; wiring W0 `exists_admissible`, W1 `witness_margin`, W2 `card_badWindow_le`, W2′ `longAverage_lower`, W3 `variance_small`; headline `almost_all_F385` (concludes the Graph node `AlmostAllF385`)); route in header, scaffolding `PROOF-ERDOS-385-ALMOST-ALL.md` on `main` (Lean parameters: `T₀ = exp(κ (log Z)^{1/10})`, the MediumPNT choice).  Literature inputs (statements only, `src/LeanFormalizations/Literature/Erdos385AlmostAll.lean`): `MR16Lemma14`, `MontgomeryVaughanMVT`, `VKZeroFreeLogDeriv`, `MediumPNTStatement` (dischargeable from PNT+ `MediumPNT`, not wired: olean unbuilt at this pin), each with a known-false control `not_…` to prove (teeth tests).  Order: W0, W1, W2 (elementary) first; then W2′ and the PNT edge; then W3 and the headline; the VK edge last (contour argument, port PNT+'s smoothed-Chebyshev code).  Frozen also: all earlier statements, Literature/; stop: AlmostAll.lean sorry-free (the Literature Props stay hypotheses).  **Decomposing into named sub-lemmas is progress**; a hard leaf may stay a NAMED `sorry` with an English paragraph and a confidence.

## ✅ (phase E2, DONE 2026-10-01, 1 lap; `card_bad_le` axiom-clean; Graph edges still open): **Erdős #385 bad-n count** - target `src/LeanFormalizations/NumberTheory/Erdos385/Count.lean` (`card_bad_le` as planted in `1d3b2b0`: #{bad n ≤ X} ≪ X·loglog X/(log X)² from `Literature.BrunUniformGap` + `primorial_dvd_or_exists_prime_pair_of_bad`, route in header), then the 3 edges in `Graph.lean` (`noCarrier_of_bad`, `eventually_not_bad_of_crossScaleRepulsion`, `sieveOnlySibling_of_FGKMT`).  Frozen also: all earlier statements incl. Rigidity.lean + FunctionField.lean, Literature/; stop: Count.lean sorry-free.  If the Brun-to-count summation gets hard, leave it as a NAMED sub-lemma with `sorry` and an English paragraph with a confidence - acceptable finish.

## ✅ (phase E1b, DONE 2026-10-01, `2c7c4ae`, 1 lap): **Erdős #385 function-field record + graph edges** - target `src/LeanFormalizations/NumberTheory/Erdos385/FunctionField.lean` (frozen statements as planted in `1d3b2b0`: `X_pow_card_sub_X_dvd_of_not_ffGood` (bad f ⇒ T^q − T ∣ f, the F_q[T] Lemma R), `card_le_natDegree_of_not_ffGood`, `ffGood_of_eval_ne_zero`, `ffGood_of_natDegree_lt_card`, `ffGood_of_ffWitness`, edge `ffWitness_of_BBR` from `Literature.BBR2015Thm23TwoFactor`); then the 3 edges in `Graph.lean`.  Frozen also: all earlier statements incl. Rigidity.lean, Literature/; stop: FunctionField.lean sorry-free.  If `ffWitness_of_BBR` gets hard, leave it as a NAMED sub-lemma with `sorry` and an English paragraph with a confidence - acceptable finish.  Next after this: E2 (`Count.lean` `card_bad_le` from `Literature.BrunUniformGap` + `primorial_dvd_or_exists_prime_pair_of_bad`).

## ✅ (phase E1, DONE 2026-10-01, `8a511f4`, 1 lap): **Erdős #385 / #430 elementary rigidity** (new math: Lemma R, R′, the #430 edge) - target `src/LeanFormalizations/NumberTheory/Erdos385/Rigidity.lean` (defs `Composite`, `F`, `Bad`, `terms` + 9 frozen statements; route in header; data `scripts/test_erdos385_rigidity.py`, 7 checks pass; frozen also: all earlier statements, Literature/ incl. the new `Literature/Erdos385.lean`, and every statement in `NumberTheory/Erdos385/{FunctionField,Graph,Count}.lean`; stop: that file sorry-free).  **Budget 1–2 laps.**  Then E1b: `FunctionField.lean` sorry-free and the three `Graph.lean` edges (see `ROADMAP-ERDOS-385.md`).  This branch runs Erdős phases E1..E4 only; Mills phases continue on `main`.


## ✅ (phase 60, DONE 2026-10-01 — all 7 statements axiom-clean; `Projective.exists_companion_root_vieta` added for `charDisc ≠ 0` via separability of the minpoly): **the Kronecker lemma** (new math, `PROBE-MILLS-RESIDUAL.md` §3): a split charpoly mod `p` makes `tr C^(c^m) mod p` purely periodic when `c ⊥ p(p−1)`; hence in the residual classes with `Tr β ≡ 2 (mod 3)` every late Mills prime has type (1)(2), i.e. the discriminant is a non-square mod it, the field is not cyclic, and a finite Jacobi-symbol certificate kills a cubic — target `NumberTheory/Mills/Kronecker.lean` (def `charDisc` + 7 frozen statements, route in header; numerics `scripts/mills-residual-probe.py kron-control` 79/79 with a failing control; frozen also: all earlier statements, Literature/; `Projective.exists_companion_root` was made public for this phase; stop: that file sorry-free).  **Budget 1–2 laps.**  If a leaf gets hard, leave it as a NAMED sub-lemma with `sorry` and an English paragraph saying why it is true (with a confidence) — that is an acceptable finish.

## ✅ DONE (phase 59): **drop `3 ∤ s` from phase 58**: `ξ(3^k + 3^a s′)` transcendental for even `s′ ≥ 8`, `3 ∤ s′`, any `a`, same two Literature hypotheses: `(B5′)` via `D_m = C_m / 3^a`, Saito `g = 3^b`, then phase 58's argument for `β = ξ^g` with shift `3^(a−b) s′` — target `NumberTheory/Mills/ShiftedMillsThreePow.lean` (1 frozen statement, route in header; reuse phase 58 lemmas, generalizing them in the NEW file if needed; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 58): **`ξ(3^k + s)` transcendental for even `s ≥ 8`, `3 ∤ s`**, conditional only on `Literature.Saito2025TypeBTrace` + new `Literature.Siegel1944SmallestPisot` (no rigidity node): Saito Type B → `g = 1` → `ξ` cubic Pisot → contradiction with phase 57 Theorem D (`ξ^s ≥ κ^8 > 4`) or with 3-divisibility if `f ≡ X³ mod 3` — target `NumberTheory/Mills/ShiftedMillsLarge.lean` (1 frozen statement, route in header; frozen also: all earlier statements, Literature/ incl. the new Siegel def; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 57): **Theorem D in full**: some root a `c`-unit (`f ≢ X^d mod c`), via `T^(Q+1) = T`, `tr T^Q = m ≥ 1`, and one automorphism of ℂ — target `NumberTheory/Mills/TheoremDMixed.lean` (1 frozen statement, route in header; frozen also: all earlier statements, Literature/; stop: that file sorry-free)

## ✅ DONE (phase 56): **Theorem D in every degree** (`c ∤ f(0)`, `α^s > d + 1`) + the plastic-number corollary (degree 3) — target `NumberTheory/Mills/TheoremDGeneral.lean` (2 frozen statements; route = generalize phase 55's integer-system + Nullstellensatz transfer, see header and `HANDOFF-2026-09-30-phase55-complete.md`).  **Decomposing into named sub-lemmas is progress.**  Frozen also: all earlier statements, Literature/; stop: that file sorry-free

## ✅ DONE (phase 55): **Theorem D, quadratic case** (Saito 1.7 for `c^n + s`): `⌊α^(c^n+s)⌋` not prime i.o. for quadratic Pisot `α`, `c ∤ b·disc`, `s ≥ 4` — target `NumberTheory/Mills/TheoremDQuadratic.lean` (1 frozen statement; number-field route WITHOUT completions in header, steps 1–5).  **Decomposing into named sub-lemmas is progress**; laps succeed by advancing the crux (Teichmüller in `𝒪_K` mod `𝔓^(n+1)`, spectral trace, separation, size).  Frozen also: all earlier statements, Literature/; stop: that file sorry-free

## ✅ DONE (phase 54): Theorem A′ (any `d` when `h ≠ 0`) + Tetranacci `T₄(2^n) + h` composite i.o. for EVERY `h` (`h = 0` by parity via the period) — target `NumberTheory/Mills/TheoremAEven.lean` (2 frozen statements + def `tetra`; route in header; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 53): prime-free intervals `[T(3^n) − 3, T(3^n) + 3]` i.o. (Tribonacci; Theorem C for order 3) by an explicit covering certificate (`n ≡ 95 mod 1980`, primes 5, 7, 13, 47, 53, 593) — target `NumberTheory/Mills/TribonacciCovering.lean` (def `tribCoverPrime` + 3 frozen statements, certificate table and route in header; `native_decide` was NOT needed — all certificates are `decide +kernel`, so the three theorems are axiom-clean; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 52): **Theorem A**, order-`d` entries `u(c^n) + h` composite i.o. at inert `c` (odd `d`, `μ_(≤d)(ℤ_c) = {±1}`), plus Tribonacci `T(3^n) + h` and `T(5^n) + h` — target `NumberTheory/Mills/TheoremA.lean` (3 frozen statements + def `trib`, survivor route in header using phase 51 `orbit_sum_entry_congr` + period; hypotheses checked: `scripts/theorem-a-tribonacci-probe.py`; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 51): the Frobenius orbit sum is scalar, Σ_(k<d) A^(c^(n+k)) ≡ tr(A^(c^n))·I mod c^(n+1) for χ_A irreducible mod c (Theorem A route, steps 3–5) — target `NumberTheory/Mills/OrbitSum.lean` (3 frozen statements, route in header; checked on 604 cases, both controls fail as they should: `scripts/orbit-sum-probe.py`; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 50): Dold congruence for EVERY charpoly coefficient (Theorem A route, step 2) + the Cayley–Hamilton-across-Frobenius corollary — target `NumberTheory/Mills/ExteriorDold.lean` (2 frozen statements, exterior-power/compound-matrix route in header; both checked on 960 random cases with a failing control; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 49): PROVE the Gauss (Dold) congruence for matrix traces (discharge `Literature.GaussCongruenceTrace`) and restate phase 29 without it — target `NumberTheory/Mills/GaussCongruenceProof.lean` (3 frozen statements, necklace route in header; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 48): traces in the unipotent class mod 3 (sub-node R4 of `ShiftedTraceRigidity`) — target `NumberTheory/Mills/UnipotentTrace.lean` (3 frozen statements, route in header; statements checked on 3000 random cases; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 47): `A^(c^n)` eventually periodic `c`-adically (integer Teichmüller congruence) — target `NumberTheory/Mills/TeichmullerCongruence.lean` (1 frozen statement, route in header; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 46): the 3-adic window for prime traces along `3^n − 2` — first sub-node of `ShiftedTraceRigidity` — target `NumberTheory/Mills/ShiftedWindow.lean` (1 frozen statement, route in header; frozen also: all earlier statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

## ✅ DONE (phase 45): Theorem E as a graph edge — `ξ(3^k − 2)` transcendental from `Literature.Saito2025TypeBTrace` + our open node `ShiftedTraceRigidity` — target `NumberTheory/Mills/ShiftedMills.lean` (3 frozen theorems + frozen defs; frozen also: `Literature/Saito2025.lean` (new, faithful-or-weaker check in its header), all earlier Mills phase statements, the rest of Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

`ShiftedTraceRigidity` is a `def … : Prop` node (our own math, `PROOF-THEOREM-E.md` Steps 3–6): **do not try to prove it in this phase.**

## ✅ DONE (phase 44): groundwork for Theorems D/E — stuck lemma, abstract-exponent filter, `GL_d` window — target `NumberTheory/Mills/TheoremDGround.lean` (3 frozen statements, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

`PROOF-THEOREM-D.md` Lemmas 2–4 (and E's Step 3).  Statements brute-force checked (random `ε`/`j`; primes `< 400`, `d ≤ 4`, `c ≤ 7`).

## ✅ DONE (phase 39): `⌊α^(c^n)⌋ + h` composite i.o. for quadratic Pisot units of norm −1 (golden ratio included) — target `NumberTheory/Mills/QuadraticPisotFloor.lean` (3 frozen statements + frozen def, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

A cheap corollary of phase 35: `⌊α^N⌋ = V_N(P, −1)` for odd `N`.

## ✅ DONE (phase 43): prime-free intervals around `F(c^n)` for EVERY prime `c`, and around `U_(c^n)(P, ±1)` — target `NumberTheory/Mills/CoveringInstances.lean` (3 frozen statements, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Uses the phase 41 engine; `c = 5` combines the engine (`h ≠ ±1`) with the `F(4k+1) ± 1` factorizations.

## ✅ DONE (phase 42): Theorem B — 2×2 traces at odd primes classified (`DoubleExpTraceComposite` for `n = 2`) — target `NumberTheory/Mills/TraceClassification.lean` (3 frozen statements, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

`ROADMAP-PRIME-TOWERS.md` §1 Theorem B.  Statements numerically checked (2196 congruence cases and 260 survivor-rate cases, 0 failures).

## ✅ DONE (phase 41): the Theorem C engine — (D1) and prime-free intervals along `c^n` for any integer matrix — target `NumberTheory/Mills/CoveringEngine.lean` (4 frozen statements, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Refactor phase 40's mechanism into a general `d × d` engine, then instantiate it for Lucas `V(c^n)` (odd `c ∤ P`) and for Fibonacci at every prime `c ≠ 5`.  `ROADMAP-PRIME-TOWERS.md` §1 Theorem C and §4.

## ✅ DONE (phase 40, `4887023`): prime-free intervals around `F(2^n)` — Dubickas's (D1) for a non-reversible tower — target `NumberTheory/Mills/FibonacciCovering.lean` (4 frozen statements, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Theorem C of `ROADMAP-PRIME-TOWERS.md` (read §1 Theorem C).  Saito's stated wish in arXiv:2504.14968 ("remove the reversibility"), for Fibonacci along `2^n`.  Phase 39 (quadratic Pisot floor corollary) is deferred behind this one.

## ✅ DONE (phase 38, `c4628d5`): `U_(c^n)(P, ±1) + h` composite i.o. at every odd prime `c ∤ D` — target `NumberTheory/Mills/LucasUnitAllPrimes.lean` (4 frozen statements + frozen def `lucasOddPoly`, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Phase 37's exact-composition route for all Lucas `U(P, ±1)`: split and inert `c` alike.

## ✅ DONE (phase 36, `889bdcb`): `U_(c^n)(P,Q) + h` composite i.o. at every odd prime `c` inert in `ℚ(√(P²−4Q))` — target `NumberTheory/Mills/LucasInert.lean` (3 frozen statements, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Generalizes phase 34 (Fibonacci) to all Lucas `U(P,Q)`.  Phases 34, 35, 37 DONE (37 `5e13749`: Fibonacci at every prime).

## ✅ DONE (phase 32, 1 lap, 2026-09-29): Saito's Problem 1.8 — ANSWERED (new math)

`NumberTheory/Mills/SaitoFibonacci.lean` is sorry-free; all five frozen statements are
`#print axioms`-clean.  For **every** integer `h`, `F(2^n) + h` fails to be prime for infinitely
many `n` — Saito's Problem 1.8 (arXiv:2504.14968) resolved affirmatively, unconditionally, with no
`Literature/` hypothesis.  Route exactly as in `PROBE-SAITO-FIBONACCI.md`: odd `h` by parity,
`h = 0` by `F(2^n) ∣ F(2^(n+1))`, even `h ≠ 0` by the phase-30 `GL₂(𝔽_p)` Lagrange mechanism
(entrywise copy `exists_entry_pow_congr`) against the 2-adic **sign flip**
`F(2^(n+1)) ≡ −F(2^n) (mod 2^(n+1))`.  See the probe file's new § Status for the formalization
notes (Cassini, `Nat.fib_gcd` parity, `v₂|GL₂| = 2v₂(p−1)+v₂(p+1)`).

### original directive

## ✅ DONE (phase 33, 1 lap, 2026-09-29): Problem 1.8 for every Lucas sequence `U(P,Q)`, `P,Q` odd

`NumberTheory/Mills/LucasTwoPow.lean` is sorry-free; all five frozen statements are
`#print axioms`-clean.  For every odd `P, Q` with `|U(2^n)| → ∞` and every integer `h`,
`U(2^n) + h` fails to be prime for infinitely many `n`.  The whole Lucas toolkit comes from the
companion matrix `A = !![P,-Q;1,0]`: `A^N = !![u(N+1), v(N+1); u N, v N]` with `v` the companion
solution (`v 0 = 1, v 1 = 0`, `v N = u(N+1) − P u N`), so `V m := u(m+1) + v m = tr(A^m)`, and the
two doubling identities are just `(A^m)^2`:
`U(2m) = U(m) V(m)` (entry `(1,0)`) and `V(2m) = tr² − 2 det = V(m)^2 − 2 Q^m`.
Sign flip: `2^(n+1) ∣ V(2^n)+1` by induction, using `2^(n+1) ∣ Q^(2^n) − 1` for odd `Q`.
New over phase 32: with no monotonicity, the mechanism's conclusion `p ∣ t_(n+j)` only gives
`|t_(n+j)| = |t_n|`; **iterate** it (the `v₂ glCard` hypothesis survives because the modulus is
unchanged and the index grows) to get `|t_{n'}| = |t_n|` for arbitrarily large `n'`, contradicting
`|t_n| → ∞`.  That replaces phase 32's "bigger prime divides smaller" step.

### original directive

## ✅ DONE (phase 37, 1 lap, 2026-09-30): `F(c^n) + h` composite i.o. for EVERY prime `c`

`NumberTheory/Mills/FibonacciAllPrimes.lean` is sorry-free; all four frozen statements are
`#print axioms`-clean.  The split Fibonacci primes `c ≡ ±1 (mod 5)` are CLOSED — no non-integrality
proof was needed.  Key correction to phase 35's pessimism: the entry family *does* have a
composition identity at **odd** index, `F((2j+1)N) = Φ_j(F N)`, because `det(fibM^N) = −1` for odd
`N`.  Full notes in `SWEEP-PRIME-MODULUS.md` § Phase 37.

## 🎯 (phase 38, was 36): general Lucas entries `U(P,Q)` at odd `c` — see the sweep's phase-37 § for the `Q^N` obstruction and why `Q = ±1` should transfer verbatim

### superseded directive (phase 37): `F(c^n) + h` composite i.o. for EVERY prime `c` and every `h` — target `NumberTheory/Mills/FibonacciAllPrimes.lean` (4 frozen statements + frozen def `fibOddPoly`, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Closes the split-prime Maze row via phase 35's exact-composition idea (`F((2j+1)N) = Φ_j(F N)` for odd `N`).  Phase 35 (`6b7cd6e`) DONE.  (Phase 36, general Lucas `U(P,Q)` at inert odd `c`, is queued after this one.)

---

## ✅ DONE (phase 35): `L(c^n) + h` (and `V_(c^n)(P,−1) + h`, `c ∤ P`) composite i.o. for every odd prime `c` — target `NumberTheory/Mills/LucasPrimePow.lean` (7 frozen statements + 2 frozen defs, route in header; frozen also: all earlier Mills phase files' statements, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Traces have no sign flip; the route is the exact composition `V_(cm) = V_c(V_m, −1)` plus a growth bound, which pins the `c`-adic limit to an integer fixed point and then to `0`, contradicting `V ≡ P (mod c)`.  Phase 34 (`2eb97a9`) DONE.

---

## ✅ DONE (phase 34): `F(c^n) + h` composite i.o. for every inert prime `c` and for `c = 5` — target `NumberTheory/Mills/FibonacciPrimePow.lean` (6 frozen statements, route in header; frozen also: SaitoFibonacci, LucasTwoPow, ThreeAdic, SharedConjecture, Projective, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

From the sweep `SWEEP-PRIME-MODULUS.md`.  Phase 33 (`78fd009`) DONE.

---

## ✅ DONE (phase 33): Problem 1.8 for every Lucas sequence `U(P,Q)`, `P, Q` odd — target `NumberTheory/Mills/LucasTwoPow.lean` (5 frozen statements, route in header; frozen also: SaitoFibonacci statements (only `exists_entry_pow_congr`'s `private` may be dropped), ThreeAdic, SharedConjecture, Projective, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Phase 32 (`677d14a`) DONE: `SaitoFibonacci.lean` sorry-free, Saito Problem 1.8 answered for every `h`.  Problem 1.7 probed and parked (Maze row, `PROBE-SAITO-FIBONACCI.md` § Problem 1.7).

---

## ✅ DONE (phase 32): Saito's Problem 1.8, `F(2^n) + h` composite i.o. for every `h` — target `NumberTheory/Mills/SaitoFibonacci.lean` (5 frozen statements, route in header; frozen also: ThreeAdic, SharedConjecture, Projective, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Read [PROBE-SAITO-FIBONACCI.md](PROBE-SAITO-FIBONACCI.md).  Unconditional: no `Literature/` hypothesis.  The phase-29 mechanism (Lagrange in `GL₂(𝔽_p)`, modulus = the prime) plus the 2-adic sign flip `F(2^(n+1)) ≡ −F(2^n) (mod 2^(n+1))`.  Adapt `exists_trace_pow_congr` to the matrix entry `(0,1)`.  Helper lemmas are free; the five statements are frozen.

---

## ✅ DONE (phase 31, 1 lap, 2026-09-29): the projective-order lemma — `NumberTheory/Mills/Projective.lean` is sorry-free, all four statements `#print axioms`-clean

Astra's argument, in Lean.  `K = AdjoinRoot` of the reduced charpoly is a field of `p³` elements;
every `Q`-th power (`Q = p²+p+1`) lands in the prime field (Frobenius/norm, using a
roots-counting characterisation of `range (algebraMap (ZMod p) K)`); `9 ∤ Q` **for every** `p`
(`decide` over `ZMod 9`), so with `m ≥ 1` the order `d` of the class of `x^(3^m)` in `Kˣ/𝔽_pˣ` is
prime to 3; `j = φ(d)` gives `x^(3^(m+j)) = λ·x^(3^m)`, transferred to matrices via
`F ∣ X^(3^(m+j)) − C λ · X^(3^m)` plus Cayley–Hamilton.

Two hypotheses of the frozen statement turn out to be **unnecessary**: `p ≠ 3` (because `9` never
divides `p²+p+1`, including at `p = 3`) and `p ∤ det C` (the root is nonzero by degree).  They are
kept, the statements being frozen.

`mills_reducible_mod_primes` needs the companion matrix's charpoly to have `A^(3^m)` as a root,
which the frozen `exists_companion_of_algebraic_mills` does not expose; its construction is
therefore reproved in `Projective.lean` as the private `exists_companion_root`, with the new
`companion3_charpoly` and the Vieta relation giving the root.

### original directive

## 🎯 (phase 31): the projective-order lemma — target `NumberTheory/Mills/Projective.lean` (4 frozen statements, route in header; frozen also: ThreeAdic, SharedConjecture, Literature/; stop: that file sorry-free, then `scripts/fact-graph`)

Read [PROBE-MILLS-PROJECTIVE.md](PROBE-MILLS-PROJECTIVE.md) for the full argument and remaining gap; summary in `FINDING-MILLS-3ADIC.md` § Extension (Astra's idea).  For `composite_of_irreducible_divisor`, include trace growth (for example, `t_k → +∞`): recurrent divisibility alone does not exclude the value q itself.  New file `NumberTheory/Mills/Projective.lean`.  Frozen statements to write:
- `dvd_trace_of_irreducible_mod`: `C : Matrix (Fin 3) (Fin 3) ℤ`, `p` prime, `p ≠ 3`, `Irreducible (C.charpoly.map (Int.castRingHom (ZMod p)))`, `1 ≤ m`, `(p:ℤ) ∣ (C^(3^m)).trace`, `¬ (p:ℤ) ∣ C.det` ⟹ `∃ j ≥ 1, (p:ℤ) ∣ (C^(3^(m+j))).trace`.
- `not_irreducible_mod_eventually`: eventually prime and increasing ⟹ for all large `k`, the charpoly is reducible mod `t_k`.
- `composite_of_irreducible_divisor`: a prime `q ≠ 3` with the charpoly irreducible mod `q` dividing some `t_m` (`m ≥ 1`) ⟹ `∃ᶠ k, ¬ Prime t_k`.
- Mills corollary via phase 30's floor = trace lemma.

---

## ✅ DONE (phase 30, `2df929e`, 1 lap): one conjecture behind Fermat and Mills

Target `NumberTheory/Mills/SharedConjecture.lean`, three frozen statements (route in the header):
- `fermat_of_doubleExpTraceComposite`;
- `mills_transcendental_of_doubleExpTraceComposite` (factor phase 29's floor = trace glue out of `mills_threeAdic` into a reusable lemma first);
- `lt_padicValNat_glCard_prime_base`.

Frozen: those three statements, `DoubleExpTraceComposite`, everything in `ThreeAdic.lean`, all of `Literature/`.  Stop condition: that file sorry-free.  After the lap, run `scripts/fact-graph`.

---

## ✅ DONE (phase 29, `9fa5b21`): a 3-adic obstruction (was: THE OBJECTIVE): a 3-adic obstruction to an algebraic Mills constant — NEW MATH

Read `PROBE-MILLS-3ADIC.md` first.  Target `NumberTheory/Mills/ThreeAdic.lean`, five frozen statements (route in the header):
- `dvd_trace_pow_three_of_glCard` (group theory in `GL_n(𝔽_p)`), unconditional;
- `lt_padicValNat_glCard`, unconditional;
- `threeAdic_pm_one`, which uses `Literature.GaussCongruenceTrace`;
- `mills_threeAdic`, glued to Saito's Pisot branch (`transcendental_or_pisot`, `pisot_branch_otherConj_real`, `pair_pow_sum_re_neg`);
- `transcendental_of_not_pm_one`.

Attack order: steps 1, then 2, then 3, then 4, then 5.  Step 4's glue (an integer matrix whose power traces equal `⌊A^(3^k)⌋`: the companion matrix of the integer minimal polynomial) is the one real infrastructure leaf.  Split it into named lemmas freely; a higher sorry count is fine.  If a frozen statement is false, record the counterexample and STOP.  Never edit `Literature/` and never weaken a frozen statement.  Stop condition: that file sorry-free.  After the lap, run `scripts/fact-graph`.

---

## ⏸️ PARKED (phase 28): Leopoldt in unit rank ≥ 2 — the Baker–Brumer wall

Phase 27 closed rank ≤ 1 **unconditionally** (see below), and located the wall exactly.  For
`r ≥ 2` the local lemma `eq_zero_of_local_tendsto_one` is genuinely false as stated: the
valuation argument controls one unit's `p`-part, not a linear combination of `r` of them.  The
next real target is Ax's reduction: Leopoldt for `K/ℚ` abelian follows from the `p`-adic Baker
theorem (Brumer 1967) — `ℚ_p`-linear independence of `log_p α₁, …, log_p αₙ` for multiplicatively
independent algebraic `αᵢ`.  Two prerequisites mathlib lacks at our pin: a `p`-adic logarithm on
principal units, and the `ℚ_p`-linear-forms machinery.  Attack order: (1) build `padicLog` on
`U⁽¹⁾` of `v.adicCompletion K` as the limit of `((1+x)^{p^n} - 1)/p^n` or via the power series,
(2) state Brumer as a `Literature/` axiom with a faithfulness argument, (3) derive rank-2
Leopoldt for a concrete abelian field (ℚ(ζ₇), rank 2) from it.  Step (1) is the only one with
real content and should go first.

---

## ✅ DONE (phase 27, `50514ad`, 2026-09-29, 1 lap): Leopoldt in unit rank ≤ 1, ℚ(ζ₈) at p = 7

**Both frozen statements proved and `#print axioms`-clean; `RankOne.lean` is sorry-free.**  The
phase-26 plan (a `ℤ_p`-action on principal units by continuity, plus torsion-freeness of `U⁽¹⁾` for
odd unramified `p`) turned out to be unnecessary, and what landed is far stronger:
`leopoldt_of_rank_le_one : Units.rank K ≤ 1 → LeopoldtConjecture K p` for **every** number field
and **every** prime — no abelian hypothesis, no `p` odd, no unramifiedness, no `p`-adic log.

Two observations collapse it (details in the `RankOne.lean` header):
- the principalising exponent `N` is prime to `p`, hence a `ℤ_p`-unit, so it suffices to kill
  `N·a` and one may use the exponents `N · m n` throughout — no residue-class subsequence;
- on a principal unit, an exponent prime to `p` does not move the valuation at all
  (`valuation_zpow_sub_one : W (θ^t − 1) = W (θ − 1)`), so only the `p`-part of the exponent can
  push `ε^m` towards `1`, and `a ≠ 0` bounds that `p`-part.

Rank `≤ 1` enters only via `card_le_rank` (multiplicative independence ⟹ `ℤ`-linear independence
in `Additive (𝓞 K)ˣ`, of `ℤ`-rank `rank K`).  Infrastructure lives in
`NumberTheory/Leopoldt/PrincipalUnits.lean`.

### original directive

The first nontrivial test of `Literature.LeopoldtConjecture` (adversarial review: faithful, 88%; header updated).  Target `NumberTheory/Leopoldt/RankOne.lean`: `rank_cyclotomic_eight`, `leopoldt_cyclotomic_eight_seven`.  This is multi-lap infrastructure: principal units of `adicCompletion`, a `ℤ_p`-action by continuity, torsion-freeness for odd unramified `p` (plan in the header).  Infrastructure leaves are progress.  If the statement proves unfaithful, record the counterexample and stop; never edit `Literature/`.  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 26, `374eea7`, 2026-09-29): Leopoldt statement stress tests + the ℚ̄ shifted-six variant

Trevor 2026-09-29: *"I think I do want the statement.  This is math worth having in the world."*  `Literature.LeopoldtConjecture` is Ren's formulation, with no p-adic log (faithfulness argument in its header, ~75%).  Targets:
- `NumberTheory/Leopoldt/StressTests.lean`: `leopoldt_of_rank_zero` (positive), `not_leopoldtNoIndep_rat` (negative: the independence clause bites).  Stretch: real quadratic.
- `NumberTheory/Transcendence/SharpSixVariants.lean`: `shiftedAlg_of_sharp` (the ℚ̄ variant is true), `witness_not_algIndep`.

If a test shows the Leopoldt statement is unfaithful, record the counterexample and STOP; do not repair `Literature/`.  Stop condition: both files sorry-free.

---

## ✅ DONE (phase 25, 2026-09-29, 1 lap): sharp-six repair + periods / zeta values

**All ten frozen statements are PROVED and `#print axioms`-clean; `Periods.lean` is
sorry-free.**  Nothing turned out false or underivable.  Three design points: the sharp form's
conclusion `xᵢyⱼ = βᵢⱼ` collapses both six- and five-exponentials to `x₀y₀ = 0` vs. linear
independence, so the phase-24 refutation of the *shifted* form really is repaired; the three
zeta theorems (Apéry, ζ(5), Ball–Rivoal) are one lemma `irrational_zeta_odd` uniform in `k`,
via mathlib's `riemannZeta_im_eq_zero_of_one_lt`; and `ζ(3)/π³` and `G/π²` are one lemma
`transcendental_div_pi_pow`.  Route and gotchas: the file header.  `scripts/fact-graph` rerun
(30 edges, 27 hypotheses).

### original directive

## ✅ DONE (phase 25, 2026-09-29, `564ae0a`): sharp-six repair + periods / zeta values

**Operator correction to the phase-24 handoff:** `SixExponentialsShifted` is NOT a dropped overbar.  The rendered survey page really says `ℚ`; the survey misprints the sharp six exponentials theorem, dropping the exceptional case `xᵢyⱼ = βᵢⱼ`.  The correct statement is now `Literature.SixExponentialsSharp` (Waldschmidt NCTS 2003 slide 23; Waldschmidt 2005 Thm 1.4), and it keeps `ℚ`-independence.  The ℚ̄ repair suggested in the handoff would NOT contain the six exponentials theorem, so do not use it.

Target `NumberTheory/Transcendence/Periods.lean`, 10 frozen statements (routes in the header): sharp six ⇒ six; sharp six + Baker ⇒ five; zeta-values conjecture ⇒ Apéry, ζ(5), Ball–Rivoal, `ζ(3)/π³` transcendental, `ζ(3), ζ(5)` alg. indep.; `catalanG = Catalan.catalanConst`; Catalan–π conjecture ⇒ `G` transcendental and `G/π²` irrational.  After the lap, run `scripts/fact-graph`.  Frozen: the 10, every earlier name, all of `Literature/`.  Stop condition: that file sorry-free.

---


## ✅ DONE (phase 24, 2026-09-29): weakest hypotheses — what follows from Conjecture 1

Trevor 2026-09-29: *"Feed the treadmill w/ cheap consequences."*  Target `NumberTheory/Transcendence/WeakSchanuel.lean`, 5 frozen statements (routes in header): Conj 1 ⇒ Gelfond–Schneider, ⇒ Baker1966, ⇒ log-primes alg. indep., ⇒ π + log-primes alg. indep., ⇒ strong four exponentials (⚠️ the last is Ren's ~70% reading; refuting or failing it is an advance).  After the lap, run `scripts/fact-graph`.  Frozen: the 5, every earlier name, all of `Literature/`.  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 23, 2026-09-29, 1 lap): Schanuel ⇒ log π, π^e, π^π

**All five frozen statements are PROVED and `#print axioms`-clean; `SchanuelPi.lean` is
sorry-free.**  Nothing turned out false or underivable.  The one real obstruction was step 0 —
irrationality of `log π`, open unconditionally — obtained from Schanuel's own `e, π`
independence via `π^d = e^n`.  Second design point: the step-2 linear independence is uniform in
`c₀ ∈ {e, π}` (one lemma `linearIndependent_quad`), because the coefficient split
`c + d·c₀ ≠ 0` / `= 0` only ever needs the *pair* `(c₀, log π)` from step 1 plus irrationality
of `c₀`.  Route and gotchas: the file header.

### original directive

Target `NumberTheory/Transcendence/SchanuelPi.lean`, 5 frozen statements, two-step Schanuel bootstrap in the header.  Frozen: the 5, every earlier name, all of `Literature/`.  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 22, 2026-09-29, 1 lap): more bedrock, via LW and Baker

**All five frozen statements are PROVED and `#print axioms`-clean; `BedrockBaker.lean` is
sorry-free.**  Nothing turned out false or underivable.  Two real design points: `tan` is a
*linear* relation in `e^{2ia}` (not a quadratic in `e^{ia}`), so the weak `ℚ`-form of
Hermite–Lindemann suffices there; and `2^√2·3^√3` needs no third logarithm beyond
`μ = √2 log2 + √3 log3` itself, at the cost of a case split on whether `log2, log3, μ` are
`ℚ`-independent.  Route, leaves (`baker_relation`, `not_quad_cexp_real`, `logTwoPair`) and the
`simp`-rewrites-`ofReal_log` gotcha: the file header.

### original directive

Target `NumberTheory/Transcendence/BedrockBaker.lean`, 5 frozen statements (routes in the header): `tan`, `sinh`, `cosh` at nonzero algebraic reals (LW); `π + log 2` and `2^√2·3^√3` transcendental (Baker, homogeneous).  Frozen: the 5, every earlier name, all of `Literature/`.  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 21, 2026-09-29, 1 lap): bedrock — unconditional consequences of LW, GS, Nesterenko

**All eleven frozen statements are PROVED and `#print axioms`-clean; `Bedrock.lean` is
sorry-free.**  No statement turned out to be false or underivable.  The one real design point:
Hermite–Lindemann has to be stated *over the algebraic numbers* (`transcendental_algClosure_cexp`),
not over `ℚ` — the `sin`/`cos` witness polynomials `X² − 2(cos a)X + 1` and `X² − 2i(sin a)X − 1`
have algebraic, not rational, coefficients, so the `ℚ`-form is too weak to contradict.  Route and
gotchas: the file header.

### original directive

## ✅ DONE (phase 21, 2026-09-29, `5a2a8d7`): bedrock — unconditional consequences of LW, GS, Nesterenko

Target `NumberTheory/Transcendence/Bedrock.lean`, 11 frozen statements (routes in the header): Hermite–Lindemann family (exp, log, sin, cos at algebraic points), Gelfond–Schneider (`2^√2`, `log 3/log 2`), Nesterenko (`e^π`, `π+e^π`, `π·e^π`, `Γ(1/4)`, `e^{−π/2}`).  Inputs: `Literature/Lindemann.lean`, `GelfondSchneider.lean`, `Nesterenko.lean`; reuse `Schanuel.lean`'s toolkit (e.g. `linearIndependent_log_primes`, `eq_zero_of_algebraicIndependent_linear`).  Frozen: the 11, every earlier name, all of `Literature/`.  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 20, 2026-09-29, `56eee43`): Waldschmidt 2023 §5, rank of matrices of logarithms

Target `NumberTheory/Transcendence/StructuralRank.lean` (header has the routes), 4 frozen statements: rk ≤ r_str; Conj 1 ⇒ rk = r_str; six exp ⇒ (r_str ≥ 3 ⇒ rk ≥ 2); structural-rank sanity example.  Definitions are in `Literature/StructuralRank.lean` (Definition 1 read off the rendered page).  If a definition turns out unfaithful or a statement false, record the counterexample; that is an advance.  Frozen: the four, every earlier name, all of `Literature/`.  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 19, 2026-09-29, 1 lap): Waldschmidt 2023, Conjecture 1 and its derivations

All five frozen statements are PROVED and `#print axioms`-clean; `Waldschmidt2023.lean` is
sorry-free.  No statement was underivable.  The one real content: Conjecture 1 alone (not full
Schanuel) suffices for four exponentials — phase 16's heart lemma uses `hS` only through
`algebraicIndependent_of_exp_isAlgebraic`, so weakening the hypothesis is exact.  Route and
gotchas: the file header.  Remaining uncovered survey items (see `WALDSCHMIDT-2023.md`):
Leopoldt §2, the structural-rank §5, and Conj 7 (Roy's equivalent of Schanuel).

### original directive

## ✅ DONE (phase 19, 2026-09-29, `99f8e17`): Waldschmidt 2023, Conjecture 1 and its derivations

Coverage map: `WALDSCHMIDT-2023.md`.  Target `NumberTheory/Transcendence/Waldschmidt2023.lean`, 5 frozen statements: Schanuel ⇒ Conj 1; Conj 1 ⇒ four exponentials (the survey's route, separate from phase 16's); Conj 1 ⇒ Baker homogeneous; Conj 1 ⇒ `log 2, π` algebraically independent; Conj 1 at `n = 1` from Lindemann–Weierstrass.  Inputs are `Literature/Waldschmidt2023.lean` plus the phase 15–17 toolkit.  Frozen: the five, every earlier name, all of `Literature/`.  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 18, 2026-09-29, 1 lap): Champernowne's constant is transcendental, via Roth

**All four frozen statements are PROVED and `#print axioms`-clean; `Champernowne.lean` is
sorry-free.**  `irrational_champernowne` is unconditional and was proved from the *same* block
approximations (Roth needs `Irrational`, so it could not be assumed).  The numeric exponent check
held: `δ = 1` works with room to spare.  Route, leaf names and the strictness trick that makes the
whole thing go: the file header and `HANDOFF-2026-09-29-phase18-complete.md`.

### original directive

Planted: `NumberTheory/Transcendence/Champernowne.lean` (route + leaves in header; `scripts/champernowne-approx.py` checks the exponents).  Frozen: `champernowne_prefix`, `irrational_champernowne`, `transcendental_champernowne`, `transcendental_champernowne_of_stephan`, the two defs.  Stop condition: that file sorry-free.  Mahler 1937.  The run of consecutive k-digit integers is a small-denominator rational (≈ (10^k−1)²), which gives approximations far better than q^(−2−ε); then apply `roth1955_of_stephan`.  Check the approximation exponent numerically before freezing statements.  Normality of Champernowne belongs in normal-numbers.  After it, continue working through Waldschmidt 2023 statement by statement (theorems → Literature, conjectures → hypothesis Props, derived implications → proofs).

---

## ✅ DONE (phase 16, 2026-09-29, 1 lap): four/six exponentials, more Schanuel

Trevor 2026-09-29: *"Seems like there's a lot we can continue to chip away at along this vein?"*  Target file `NumberTheory/Transcendence/Exponentials.lean`, 6 frozen statements: Schanuel ⇒ four exponentials (the meaty one; the phase-15 note calling it *not* implied was wrong); four exp ⇒ `2^t` or `3^t` transcendental; six exponentials (a Literature theorem, Lang/Ramachandra) ⇒ `p^t ∈ ℤ` for three primes forces `t ∈ ℕ` (unconditional); `e, e^e, e^{e^e}`; `π` + log primes; `e + log 2`.  Inputs are `Literature/Exponentials.lean` and the phase-15 toolkit.  If a statement proves underivable, record why; that counts as an advance.  Frozen by name: the six, every earlier name, all of `Literature/`.  Stop condition: `Exponentials.lean` sorry-free.

**Result: all six are PROVED and `#print axioms`-clean; `Exponentials.lean` is sorry-free.**
No statement turned out to be underivable.  The meaty one (Schanuel ⇒ four exponentials) went
through; the phase-15 note calling it *not* implied is now definitively retracted in the file
header.  Route and reusable leaves: `HANDOFF-2026-09-29-phase16-complete.md`.

---


## ✅ DONE (phase 17, 2026-09-29, `206efab`): consequences of the KNOWN exponentials theorems

Operator fix 2026-09-29: `StrongSixExponentials` now takes `ℚ̄`-independence (the `ℚ` version is kept as `StrongSixExponentialsOverQ`, refuted); `Literature.Baker1966` was added, and `fiveExponentials_of_shifted` now takes `hB : Baker1966` (the lap showed that the reduction needs exactly Baker for two logs).  New frozen target: `strongSixExponentials_of_schanuel`.  Target `NumberTheory/Transcendence/ExponentialsKnown.lean`: unconditional `2^t, 3^t, 5^t` (six exp), and consistency edges among `Literature/ExponentialsKnown.lean` (five exp, shifted six exp, Roy's strong six exp).  Stop condition: that file sorry-free.

---

## ✅ DONE (phase 15, 2026-09-29, 1 lap): what follows from Schanuel's conjecture

`NumberTheory/Transcendence/Schanuel.lean` is **sorry-free**; all ten frozen statements are
axiom-clean.  Route, toolkit and gotchas: `HANDOFF-2026-09-29-phase15-complete.md`.  **No
contradiction turned up** — the three consistency edges (Gelfond–Schneider,
Lindemann–Weierstrass, Nesterenko) all fall out as they should.  The Wright row of `Maze.lean`
stays open: every level `≥ 2` transcendental is consistent with every level sitting just above a
prime.  Cheap follow-ons are listed at the end of that handoff.

### original directive

## ✅ DONE (phase 15, 2026-09-29, `c2a7e2d`): what follows from Schanuel's conjecture

Trevor 2026-09-29: *"Since there are a lot of things that follow from it, I think it's worth writing those things down.  Maybe, just maybe, we'll bump into a contradiction, or notice something interesting."*  Hypothesis: `Literature.SchanuelConjecture` (verbatim from formal-conjectures).  Target file `NumberTheory/Transcendence/Schanuel.lean`: 10 frozen statements (consistency edges to Gelfond–Schneider, Lindemann–Weierstrass and Nesterenko; open consequences `e, π` algebraically independent, `e+π`, `eπ`, `e, e^e`, logs of primes; Wright towers).  Sketches are in the header.  Add further consequences as new theorems freely; a statement found underivable is an advance, so record it.  Frozen by name: the ten statements, every earlier name, all of `Literature/`.  Stop condition: `Schanuel.lean` sorry-free.

---

## ✅ DONE (phase 14, 2026-09-29, `01af4c1`, 1 lap): Mills' constant is transcendental under RH

Trevor 2026-09-29: formalize Saito 2025 Thm 1.8.  Target file
`NumberTheory/Mills/TranscendentalRH.lean`: `pisot_branch_otherConj_real` (unconditional complex-case
kill, ×3 circle dynamics) and `transcendental_of_RH`.  Route and leaves in the file header; paper
`papers/saito-2025-transcendency-variants-mills.txt`, probe `PROBE-MILLS-TRANSCENDENCE.md`.  Build on
`Transcendental.lean` (`transcendental_or_pisot`), `SaitoDegreeTwo.lean`, `RH.lean` (`gseq`, `lpa`,
Schoenfeld).  New literature inputs: none (RH enters via `Schoenfeld1976`).  Split into named leaves
freely.  Frozen by name: the two phase-14 theorems, every earlier name, all of `Literature/`.
Stop condition: `TranscendentalRH.lean` sorry-free.

---

## ⏸️ PARKED (phase 13b, 2026-09-29): Dubickas Lemma 6 from Stephan's machine-checked CZ

**Parked by Trevor 2026-09-29**: *"Why bother with 13b?  That's filling a hole that we're no longer
looking to publish."*  The unconditional Dubickas chain only mattered for an OEIS citation, and OEIS
is out.  Literature theorems stay as hypothesis `Prop`s; effort goes to new math (phase 14).

Phase 13 is STOPPED and superseded: Stephan formalized Corvaja–Zannier 2004 itself
(`rwst/Subspace-Theorems`, `CorvajaZannier2004/`).  Its Main Theorem and Lemma 4 are now
`Literature.Stephan2026CZMain` / `Stephan2026CZLemma4` (verbatim, frozen).  Phase 13b is
`NumberTheory/Transcendence/CorvajaZannierStephan.lean`: wire them into the phase-9 statements and
`Dubickas2022`.  Sketches in the file header.  Do NOT continue `CorvajaZannier.lean`.  Frozen by
name: the three phase-13b theorems, every earlier name, all of `Literature/`.  Stop condition:
`CorvajaZannierStephan.lean` sorry-free.

---

## 🎯 THE OBJECTIVE (phase 13, 2026-09-29): Corvaja–Zannier from Stephan's Subspace Theorem

Phase 12 is green (`StephanEdges.lean`).  R. Stephan's Subspace Theorem with several places is
now `Literature.Stephan2026Subspace` (verbatim, frozen, with his `approxProd`).  Phase 13 is
`NumberTheory/Transcendence/CorvajaZannier.lean`: derive the two phase-9 disclosed statements
(`corvajaZannier_dichotomy_of_stephan`, `corvajaZannier_lemma4_of_stephan`) and then
`dubickas2022_of_stephan : Dubickas2022` from `Stephan2026Subspace` + `Stephan2026Ridout`.  Source:
`papers/corvaja-zannier-2004-powers-algebraic.txt` (12 pp.); route in the file header.  Do NOT prove
the Subspace Theorem.  This is moonshot-sized: decompose into named leaves freely (more `sorry`s is
progress); a precise obstruction in `PROBE-DUBICKAS-NOSUBSPACE.md` is also a result.  Frozen by
name: the three phase-13 theorems, every earlier name, all of `Literature/`.  Leave the phase-9
`sorry`s in `DubickasNoSubspace.lean` alone (this file supersedes them).  Stop condition:
`CorvajaZannier.lean` sorry-free.

---

## 🎯 THE OBJECTIVE (phase 12, 2026-09-28): Roth / Mahler / Mills from Stephan's machine-checked Ridout

Roth is already formalized (R. Stephan, `rwst/Subspace-Theorems`, Lean 4, 2026; see
`PROBE-ROTH.md`).  Do NOT prove Roth.  His `Rat.finite_setOf_ridout` is now
`Literature.Stephan2026Ridout` (verbatim, frozen).  Phase 12 is
`NumberTheory/Diophantine/StephanEdges.lean`: derive `Roth1955`, `Ridout1957SUnitDen`,
`mahler_mul_of_stephan` (same statement as `mahler_mul_of_ridout1957`), `Mahler1957`, and
`Mills.irrational_of_stephan`.  Proof sketches in the file header; reuse `Edges.lean`'s
Mahler bookkeeping (lowest-terms reduction, `p* ≤ 2q αⁿ`, `β ≠ q`).  Frozen by name: the five
phase-12 theorems plus every earlier name and all of `Literature/`.  Phase 9's two disclosed
Corvaja–Zannier `sorry`s stay.  Stop condition: `NumberTheory/Diophantine/` sorry-free.

---

## 🎯 THE OBJECTIVE (phase 11, 2026-09-28): A003095's siblings — `PolyIteration/Siblings.lean`

Phase 10 is green.  Phase 11 is `NumberTheory/PolyIteration/Siblings.lean`: Bala's general
divisibility properties of polynomial iterations, then the elementary OEIS facts for Sylvester's
sequence A000058 (Euclid-number product, pairwise coprimality, Egyptian fraction sum `= 1`,
no squares, `−3` a QR mod every prime factor, residues mod 1000/3000/864, Mohanty's generalization),
A003096, A002065, A004019.  Reuse `Sylvester.lean` (`sub_dvd_sub_shift`, `isStrongDivSeq_*`) and
`A003095.lean`.  All statements checked numerically before freezing; `decide`/`native_decide` for
small cases is fine.  Frozen by name: every phase-11 def/theorem plus every earlier name.
Phase 9's two disclosed Corvaja–Zannier `sorry`s stay.  Stop condition: `NumberTheory/PolyIteration/`
sorry-free.

---

## 🎯 THE OBJECTIVE (phase 10, 2026-09-28): A003095's elementary facts — low-hanging fruit

Phases 1–9 are merged (phase 9's two Corvaja–Zannier `sorry`s in `DubickasNoSubspace.lean` are
DISCLOSED OPEN - leave them).  Phase 10 is `NumberTheory/PolyIteration/`: Sylvester's theorem and
Bala's generalization (`Sylvester.lean`), then every elementary fact on OEIS A003095
(`A003095.lean`: strong divisibility, Bala's identities, the Bala conjectures as proved by Harden,
Somos's relation, the digit cycles).  Proof sketches in both headers; sources
`papers/bala-2026-sylvester-strong-divisibility.txt`, `papers/harden-2026-bala-conjectures.txt`.
All statements were checked numerically on small `n` before freezing.  `decide`/`native_decide`
for small cases is fine.  Frozen by name: every phase-10 theorem and `IsStrongDivSeq`, `a003095`,
plus every earlier name.  Stop condition: `NumberTheory/PolyIteration/` sorry-free.

---

## 🎯 THE OBJECTIVE (phase 9, 2026-09-28): drop Lemma 6 from Dubickas Theorem 1 — a 3-lap PROBE

Phase 8 removed Lemma 8.  Theorem 1 now rests on `Dubickas2022` (Lemma 6, Corvaja–Zannier,
subspace theorem) alone, consumed once in `exists_pisot_pow`.  Trevor wants the OEIS-linked
headline unconditional.  Target: **`exists_pisot_pow_noD`** in
`NumberTheory/Transcendence/DubickasNoSubspace.lean` (special case + leads in its header), or a
direct `c_eq_zero_or_two_uncond` that bypasses it.

Once one is proved: drop `hD` from the three `Dubickas.lean` headlines (names and path unchanged,
the file is ⚓ OEIS-linked), update `Comparator/Dubickas/Challenge.lean` to match, and confirm
`scripts/comparator-probe Dubickas` says identical.

**This may well need subspace-theorem strength.**  A precise obstruction in
`PROBE-DUBICKAS-NOSUBSPACE.md` is a full success: which step needs what, and the smallest
literature `Prop` that would close it.  Do not state that `Prop` in `Literature/` yourself; propose
it in the write-up.  Frozen: every earlier name, all of `Literature/`.
Stop condition: `NumberTheory/Transcendence/` sorry-free.

---

## (previous directive, branch `erdos-385-c` only) set 2026-10-01, review lap of phase E9b

**THE single objective:** prove `localZeroDetect_of_richert` (`Erdos385/PowerSaving/ZeroDetect.lean`):
a large VK deviation `‖vkDev f P t‖ ≥ P^{1−η}` forces a zero with `Re ≥ 1 − 2η − A loglog P/log P`
within `A P^{η/3} log P / 2` of `t`.  It is the one analytic crux left under
`almost_all_F385_powerSaving`; the transport `largeValueCount_of_zeroDetect` (ZeroCount.lean, 85%)
is the only other open leaf on the headline path.

**Mandated next move:** decompose the crux in `PowerSaving/` exactly as ZeroDetect.lean's header:
(a) `local_logDeriv_bound` — `local_landau` on `closedBall (1+η₂+iy₀) (4η₂)` with Richert (σ ≤ 1),
PNT+ `ZetaUpperBnd` (σ ≥ 1), `ZetaLowerBound3` (centre): `|ζ'/ζ| ≤ K(log P)²` on the zero-free box;
(b) a general rectangle shift `[σ₁, σ₂] × [−U, U]` (copy `rect_shift_norm`);
(c) the contour assembly modelled line-by-line on `vertical_integral_bound` (V4 identity at Re 2 →
shift to `c = 1 + 1/log P` on `|y| ≤ P` → split at `L` → shift to `1 − η₂` on `|y| ≤ L`).
Then the transport.  Hardest-first: (a) and (c) before (b) polish and before the transport.

**Forbidden drift:** proving `nearOneLargeValues_of_density` (frozen, OFF the headline, ~10%:
needs beyond-VK zero-free info for slow-Mellin weights — Maze row anchored at `SlowMellinWeight`);
re-deriving `NearOneLargeValues`-based transports; editing frozen statements or `Literature/`.

**Why:** the review lap found the planned route (`largeValueCount_of_lit` ⇐ `NearOneLargeValues`)
rested on a statement that is not derivable for a general `C^∞` weight.  `LargeValueCount` only needs
a `P^{η/2}` count, so a polynomial window `P^{η/3}` (any weight, Mellin decay `y^{−4}`) suffices.

**Directive history**
- 2026-09-28 (review lap): phase 8 CLOSED — Lemma 8 dropped from the Dubickas headlines; next
  phase must attack a literature *hypothesis*, not a leaf.
- 2026-09-28 (review lap #2): phase 9's probe goal MET; Lemma 3 is the Subspace Theorem and stays a
  disclosed leaf.  New objective = THREE leaves → ONE, via the general-`k` Newton collapse + the
  `den(U_N) ∣ D^N` upper bound + the cofiniteness dichotomy.
- 2026-10-01 (review lap, phase E3, `erdos-385`): one `sorry` left (V4 `smoothTwist_sub_main_eq`);
  objective = close it, nothing else.  Closed the same lap (`e819725`).
- 2026-10-01 (review lap, phase E9b, `erdos-385-c`): `NearOneLargeValues` (∀ weights) judged not
  derivable; headline re-routed through `LocalZeroDetect` (P^{η/3} window).  Objective = that crux.
- 2026-10-05 (review lap, phase 61, `mills-eplus`): A, B, C proved; objective = node D only, by the
  flip lemma + root-of-unity circulant (generic) and γ ∈ ℚ(ζ₁₃), τ³γ = ±γ (E1 at g = 2).
- 2026-10-05 (review lap 3, phase 62, `mills-eplus`): records route kept; the three open leaves reduce to
  Skolem at an odd prime `p ∤ N(β)` (three-zero `p`-adic determinant first) + Mignotte-lite/dominant-pair dynamics.

---

## 🎯 THE OBJECTIVE (phase 8, 2026-09-27): drop Lemma 8 from Dubickas Theorem 1 — a 3-lap PROBE

Phases 1–7 are GREEN and merged.  Trevor wants the OEIS-linked `Dubickas.lean` headline to become
**unconditional**; its two literature inputs are `Dubickas2022` (Lemma 6, subspace theorem — out
of scope) and `Dubickas2022PisotGap` (Lemma 8 — this phase).  Lemma 8 is consumed exactly once,
in `c_eq_zero_or_two` (`hL1`).  Target: **`c_eq_zero_or_two_noGap`** in
`NumberTheory/Transcendence/DubickasNoGap.lean` (leads in its header), from `Dubickas2022` only.
Reuse `DubickasPisot.lean` / `Mills/SaitoPisot.lean` lemmas; decompose into named leaves freely.

Once it is proved: drop the `hG` argument from `transcendental_growth_of_monic_quadratic`,
`theorem1`, `oeis_constants` in `Dubickas.lean` (names and file path unchanged — the file is
⚓ linked from OEIS), route through `_noGap`, update `Comparator/Dubickas/Challenge.lean` to match,
and confirm `scripts/comparator-probe Dubickas` says identical.

A refutation is an advance: if the elementary route is blocked, write the obstruction in
`PROBE-DUBICKAS-NOGAP.md` and stop.  Frozen: every earlier name, all of `Literature/`
(`Lindemann.lean` is a pending-mathlib-PR stub: never prove it).
Stop condition: `NumberTheory/Transcendence/` sorry-free.

---

## 🎯 THE OBJECTIVE (phase 7, 2026-09-27): Dubickas 2022 Theorem 1 — κ, ζ, Sylvester γ, η, τ transcendental

Phases 1–6 are GREEN and merged.  Phase 7 is `NumberTheory/Transcendence/Dubickas.lean` (route in
its header): **`transcendental_growth_of_monic_quadratic`** (Theorem 2 for `d = 2`, `a₀ = 1`), then
`theorem1` (the five constants — check (17)/(18) by `decide`/`norm_num`), then `oeis_constants`
(half-rate limits = `√α`).  Inputs: the frozen `Dubickas2022`, `Dubickas2022PisotGap`, `IsPisot`
(`Literature/Pisot.lean`) — reuse the Pisot conjugate-multiset lemmas phase 6 built in
`Mills/SaitoPisot.lean` etc. rather than re-deriving (move shared lemmas to a common file if
needed, without changing their statements).  Formula (6) (limit exists, `x_n = α^(2ⁿ) − a₁/2 +
O(α^(−2ⁿ))`) is elementary and is the likely long pole.  Decompose into named `sorry` leaves freely.

⚠️ If a frozen `Prop` is too weak for Dubickas's step, STOP and write it up in HANDOFF.
Source: `papers/dubickas-2022-transcendency-polynomial-iterations.{pdf,txt}` §1, §4–5.
Frozen by name: the phase-7 defs (`kappaSeq`, `zetaSeq`, `sylvester`, `etaSeq`, `tauSeq`,
`HasTranscendentalGrowth`, `HasTranscendentalHalfGrowth`) and three theorems, plus every earlier
name.  `Literature/Lindemann.lean` is a pending-mathlib-PR stub: never prove it.
Stop condition: `NumberTheory/Transcendence/` sorry-free.

---


## 🎯 THE OBJECTIVE (phase 6, 2026-09-27): Saito's transcendence theorems (Thm 1.1, 1.2)

Phases 1–5 are GREEN and merged.  Phase 6 is `Mills/Transcendental.lean` (plan in its header):
`exists_minMillsC_of_BHP`, then **`transcendental_of_four_le`** (ξ_c transcendental, c ≥ 4), then
`transcendental_or_pisot` (ξ₃ transcendental or ξ₃^(3^m) Pisot of degree 3).  New literature
inputs `Dubickas2022`, `Dubickas2022PisotGap`, `IsPisot` in `Literature/Pisot.lean` — frozen.
Generalise the c = 3 machinery of `Irrational.lean` (Lemmas 3.5–3.9) to exponent `c` as NEW
lemmas (a new file `Mills/SaitoGeneral.lean` is fine); never change existing statements.
Decompose into named `sorry` leaves freely — more sorries with a clearer crux is progress.

⚠️ If a frozen literature `Prop` turns out mis-stated (too weak to carry Saito's step, or
suspected false), STOP and write it up in HANDOFF — do not edit it.

Source: `papers/saito-2024-mills-irrational.{pdf,txt}` §3–§4 (render pages for formulas).
Frozen by name: `IsPisot`, `Dubickas2022`, `Dubickas2022PisotGap`, `IsMillsC`, `IsMinMillsC`,
the three phase-6 theorems, plus every earlier name.  Stop condition: `Mills/` sorry-free.

---


## 🎯 THE OBJECTIVE (phase 5, 2026-09-27): Diophantine wiring edges — make Mahler a theorem

Prove the three edges in `src/LeanFormalizations/NumberTheory/Diophantine/Edges.lean`
(plans in its header): **`mahler_of_ridout1957` first** (it turns the `Mahler1957` hypothesis of
Saito's `irrational` into a consequence of Ridout), then `ridoutSUnitDen_of_ridout1957`, then
`roth_of_ridout1958`.  Then add, in `Mills/Irrational.lean`, a corollary
`irrational_of_ridout (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hR : Ridout1957)`.

Sources (gitignored, local): `papers/mahler-1957-fractional-parts-ii.{pdf,txt}`,
`papers/ridout-1957-rational-approximations.{pdf,txt}`, `papers/ridout-1958-p-adic-roth.{pdf,txt}`.
Text extraction drops displayed formulas — render a page (`pdftoppm -f N -l N -r 150 -png`) and
read the image when a formula matters.

**All `Literature/` statements are frozen** (never edit; never strengthen).  Frozen by name:
`Roth1955`, `Ridout1958`, `Ridout1957`, `Ridout1957SUnitDen`, `Mahler1957`, the three edge
theorems, plus every earlier name.  Lane: `NumberTheory/Diophantine/` + the one corollary in
`Mills/Irrational.lean`.  Stop condition: `NumberTheory/Diophantine/` sorry-free.

---


## 🎯 THE OBJECTIVE (phase 4, 2026-09-27): explicit upper bound without RH

Phases 1–3 are GREEN and merged.  Phase 4 is one file, `Mills/UpperBound.lean`:
`exists_minMills_lt_of_dudek` — from `Literature.Dudek2016` (new, frozen), the least Mills
number exists and is `< 2 · exp(exp(33.3)/3)`.  Plan in the file header.  Generalise the
`Basic.lean`/`Chain.lean` construction to start at a chosen prime if needed (new lemmas; do not
change existing statements).  Frozen by name: `Dudek2016`, `exists_minMills_lt_of_dudek`,
`minMills_lt_of_dudek`, plus every earlier name.  Stop condition: `Mills/` sorry-free.

---


## 🎯 THE OBJECTIVE (phase 3, 2026-09-27): the unconditional lower bound

Phases 1–2 are GREEN and merged.  Phase 3 is one small file, `Mills/LowerBound.lean`:
`lower_bound_of_isMills` — every Mills number exceeds `1.3063778838`, **no hypothesis** (RH is
only needed for the upper end).  Proof plan in the file header: case-split along the greedy chain
2, 11, 1361, 2521008887.  Frozen by name: `lower_bound_of_isMills`, `lower_bound`, plus every
phase 1–2 name.  Do not add hypotheses.  Stop condition: `Mills/` sorry-free.

---


## 🎯 THE OBJECTIVE (phase 2, 2026-09-27): Mills digits under RH + Saito irrationality

Phase 1 (Wright, conditional Mills, least Mills) is GREEN and merged — see below.  Phase 2
closes the last two formal-conjectures Mills statements, each from **named literature
inputs** in `src/LeanFormalizations/Literature/Primes.lean`:

- 🎯 **`lower_bound_of_RH`** (`Mills/RH.lean`, Caldwell–Cheng 2005): the leaf work is
  `primeBetweenCubes_of_schoenfeld` (Schoenfeld ⇒ prime in every cube gap; n ≤ 13 by
  computation) and `minMills_mem_Ioo_of_primeBetweenCubes` (greedy chain 2, 11, 1361,
  2521008887 is the least Mills number; 81st-power `norm_num` for the digits).  **Do this first.**
- 🎯 **`irrational`** (`Mills/Irrational.lean`, Saito 2024, specialised to `c_k = 3`): from
  `BakerHarmanPintz2001`, `Matomaki2007`, `Mahler1957`.  Route in the file header, lemma numbers
  are Saito's.  Leaves first: `primeBetweenCubes_of_BHP`, then Lemmas 3.5, 3.8, 3.6, 3.9, then
  the Mahler contradiction.  Decompose into named leaves freely.

**Sources (local, gitignored):** `papers/saito-2024-mills-irrational.txt`,
`papers/caldwell-cheng-2005-mills-constant.txt`.  Read the relevant section before a leaf.

**🔒 Literature statements are FROZEN and must never be strengthened.**  `Literature/Primes.lean`
holds published theorems as `Prop`s (hypotheses, not axioms).  A stronger-than-published
hypothesis could be false and would make every theorem using it vacuous — the worst failure
this repo can have.  Do not edit them.  If one looks WRONG against its source (too strong, or
too weak to be usable), stop that leaf, write the finding into the HANDOFF loudly, and move to
another leaf.  Adding a NEW literature `Prop` (with page/theorem citation, faithful or weaker)
is allowed when a proof genuinely needs one; say so in the commit message.

**Frozen by name (host-enforced):** everything in phase 1's list, plus `primesIn`,
`BakerHarmanPintz2001`, `Matomaki2007`, `Mahler1957`, `Schoenfeld1976`, `lower_bound_of_RH`,
`minMills_mem_Ioo_of_primeBetweenCubes`, `primeBetweenCubes_of_schoenfeld`,
`primeBetweenCubes_of_BHP`, `exists_mills_of_BHP`, `irrational`.

**Lane:** `src/LeanFormalizations/NumberTheory/Mills/` (+ reading `Literature/`, + import lines,
+ README row).  Stop condition: `Mills/` sorry-free (host-checked).  Branch `mills`.

---


## 🎯 THE OBJECTIVE: Mills + Wright — `src/LeanFormalizations/NumberTheory/Mills/`

Branch **`mills`** (cut from `main` 2026-09-27).  Two prime-representing-function theorems, both
formalized nowhere as of 2026-09-27 (formal-conjectures has `Mills.exists'` etc. as `sorry`
statements; mathlib has nothing):

- 🟢 **Wright (1951)** — `wright` in `Wright.lean`: some `ω` makes `⌊2^2^…^2^ω⌋` prime for every
  tower height `n ≥ 1`.  **Unconditional** (Bertrand is in mathlib).  Proof plan in the header.
- 🟡 **Mills (1947), conditional** — `exists_mills_of_primeBetweenCubes` in `Basic.lean`: a prime
  strictly between consecutive cubes from `N` on (`PrimeBetweenCubesFrom N`, Ingham's theorem)
  implies `∃ A > 1, IsMills A`.  Proof plan in the header.
- 🟢 **Least Mills number** — `exists_least_of_exists`: one Mills number ⇒ a least one.
  Unconditional given its hypothesis.
- 🔴 **NOT targets:** Ingham's theorem itself, `PrimeBetweenCubesFrom` for any concrete `N`,
  irrationality of Mills' constant, its digits.  The hypothesis stays a hypothesis; no lap may
  claim or headline an unconditional Mills theorem.

**Frozen statements, guarded BY NAME** (host `--require-decls` enforces; do not rename, weaken,
or delete): `IsMills`, `IsMinMills`, `PrimeBetweenCubesFrom`, `exists_mills_of_primeBetweenCubes`,
`exists_least_of_exists`, `exists_least_of_primeBetweenCubes` (Basic.lean) · `tower`, `wright`
(Wright.lean).  `IsMills`/`IsMinMills` are **verbatim copies** of formal-conjectures'
`FormalConjectures/Wikipedia/Mills.lean` — that faithfulness is the point, never edit them.  If a
frozen statement is *wrong* (the scaffold was compiled, not proved), FIX it and say so loudly in
the commit message and HANDOFF; never route around it silently.

**Order** (each is a green checkpoint — commit each):
1. `wright` — decompose into named leaves (Bertrand step with strict upper bound, inverse-tower
   monotonicity, nested intervals, floor identification).  Easiest; land it first.
2. `prime_add_one_lt_cube` → `exists_mills_of_primeBetweenCubes` (same nested-interval shape
   with `x ↦ x^(1/3)`; mind the `ℕ+` re-indexing in `IsMills`).
3. `exists_least_of_exists` (closure of left-closed intervals under antitone limits).
Share the nested-interval engine between 1 and 2 if it falls out naturally; do not force it.

**Before the hard part of any lap: commit a compiling skeleton with named `sorry` leaves.**
Raising the `sorry` count by splitting a leaf into named leaves is progress.

## Lane discipline (Mills run)
- Work ONLY in `src/LeanFormalizations/NumberTheory/Mills/` (+ its import lines in
  `src/LeanFormalizations.lean`, + a Mills row in `README.md` once something is green).
- DO NOT TOUCH any other thread.  Read them for technique.
- Mathlib-only imports.  **Do not import PrimeNumberTheoremAnd** in this thread.
- No `axiom`, ever.  Goal end-state per headline: `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`; run it when a headline closes, mention it only if it fails.
- Rules below ("Rules (same as every autonomous run here)") apply, except: work on the **`mills`**
  branch, not `catalan`.

## Stop condition (Mills run)
Done when `src/LeanFormalizations/NumberTheory/Mills/` is `sorry`-free (the host checks this).
Do NOT stop because one headline landed.

---

# 📚 ARCHIVE — earlier objectives (Catalan / Dirichlet β, both finished).  Historical: the Mills sections above supersede every objective, lane and stop rule below.

## (was) DIRECTION of 2026-09-04

## 🎯 THE OBJECTIVE: the Catalan salvage — `src/LeanFormalizations/NumberTheory/Catalan/`

Zhi-Wei Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1 (3 Sep 2026), claims
`G = Σ (-1)^k/(2k+1)^2 ∉ ℚ`.  **The proof is wrong**: a 2-adic bookkeeping error kills §3–§9
(`papers/sun-2026-catalan-irrationality.md` — read it once; the PDF sits beside it).  This thread
builds the machine-checked **conjecture graph** around what survives.  The product is the graph;
the unit of progress is one green node, one green edge (a wiring theorem), or one probe-refuted
node.  Report what the mathematics *says*; the axiom audit is a check, never a headline.

- 🟢 **Node A — Theorem 2.1** (`residual_rank`, engine `resid_rank`): the `(S+3) × S` weighted
  residual matrix has full column rank.  The one clean, correct, self-contained object in the
  paper — proved here for **any** sequence satisfying the recurrence `T_m + T_{m+1} = 1/(2m+1)^2`
  (`IsTailSeq`), then instantiated at the real tails.  ⚠️ The paper's own proof has two index
  slips (expansion base `T_i` vs `T_{i+1}`; a `k = 0` term that is not a polynomial) — the repair
  and the full proof plan are in `Residual.lean`'s header.  **Discharge it.**
- 🟢 **Node B — the 2-adic no-go** (`two_pow_padicValNat_bigF_dvd_NB`,
  `padicValNat_two_bigF_ge`, headline `sun_ledger_impossible`): under `G = a/q` the paper's own
  integer `N_B` is divisible by `2^{v₂(F_B)}` with `v₂(F_B) ≥ B(2B−1) − 2B(⌊log₂ 2B⌋+1)`, and
  some row set makes it nonzero, so `|N_B| → ∞` where Theorem 9.1 needs `|N_B| → 0`.  This is
  the **signpost** (a kernel-checked negation of the refuted route, so nobody re-argues §9).
  It consumes Node A over `ℚ` (Corollary 2.1 gives the nonzero minor).  **Discharge it.**
- 🔴 **Sink — `Irrational catalanConst`.  NOT a target.  Nothing here proves it; no lap may
  claim, imply, or headline it.  Catalan's constant remains open.**
- 🌙 **Frontier question** (Phase 2, only after A and B are green): *what is the weakest open
  node on any path from A to the sink?*

## Phase 1 — the grind (laps start here)

**Frozen statements, guarded BY NAME** (also enforced by the host's `--require-decls`; do not
rename, weaken, generalise-into-restriction, or delete):
`tail`, `catalanConst`, `wtail`, `tail_add_tail_succ` (Tails.lean) · `normaliser`, `IsTailSeq`,
`resid`, `resid_rank` (Residual.lean) · `fakeTail`, `bigF`, `normaliserProd`, `qhat`, `NB`,
`two_pow_padicValNat_bigF_dvd_NB`, `padicValNat_two_bigF_ge` (TwoAdic.lean) · `residual_rank`,
`sun_ledger_impossible`, `fakeTail_eq_tail_of_catalan_eq` (Statement.lean).
If a frozen statement is *wrong* (the planted scaffold was hand-checked, not machine-checked, so
this can happen), FIX it: the fix plus the reason go in the commit message and the HANDOFF, and
the lap says so loudly.  Never route around a wrong statement silently.

**Order** (each is one coherent green checkpoint — commit each; a lap that lands one is a
successful lap):
1. `Tails.lean`: `summable_tailTerm` → `tail_add_tail_succ` → `tail_eq_catalan_sub_partialSum`
   (then `tail_pos`, `tail_lt` if cheap; they are anchors, not on the path).
2. `Residual.lean`, in this order: `IsTailSeq.shift` → `alt_choose_sum_eval_eq_zero` →
   `exists_poly_of_alt_sums_eq_zero` → `no_rational_solution` → **`resid_mulVec_eq_zero`** (the
   crux).  Decompose the crux into NAMED sub-lemmas following the header plan (`D_λ`, `P_λ`,
   the polynomial `K`, its `4B+1` zeros, `deg K ≤ 4B`).  Raising the `sorry` count by splitting
   one fat leaf into named leaves IS progress; a lap succeeds by advancing the crux.
3. `TwoAdic.lean`: `odd_den_mul_fakeTail` → `odd_den_smul_resid` → `odd_den_det` →
   `two_pow_padicValNat_bigF_dvd_NB` → `padicValNat_two_bigF_ge`.
4. `Statement.lean`: `exists_row_set_det_ne_zero` → `fakeTail_eq_tail_of_catalan_eq` →
   `sun_ledger_impossible`.
Steps 1, 3 and 4a are independent of step 2 — if the crux stalls, land those and come back.

**Before the hard part of any lap: commit a compiling skeleton with named `sorry` leaves.**  A lap
that dies with nothing committed loses the hour whatever killed it (an output-token cap kills a
lap the same way a spent window does, and no model switch helps).

## Phase 1 — GREEN (2026-09-04, one lap, merged to `main`)

All seven headlines axiom-clean; every frozen statement char-identical to the scaffold.  Record:
`HANDOFF-2026-09-04-catalan-phase1-green.md`.

## Phase 2 — the moonshot (review laps own this)

### ☠️ Killed thread: N1 alone (2026-09-04, host, `papers/sun-2026-catalan-twoadic-check.py ledger`)

The fake-rational probe was the wrong instrument for the real place (with `G = a/q` the "tails"
do not decay).  With `G` **formal**, `det R[A,J]` is a degree-`≤S` polynomial `P_A(G) ∈ ℚ[G]`
(interpolated exactly); `y_A := P_A/∏_{i<N}Π_i`; `Δ_B` := lcm of `y_A`'s coefficient denominators
(so `Δ_B q^S y_A(a/q) ∈ ℤ` for **every** `a/q`, F_B-free by construction, `v₂(Δ_B) = 0`); and
`|y_A(G)|` at the true `G`, 4000 digits.  Then, minimised over `A`:

    log10|N_B| = log10 Δ_B + log10|y_A(G)|  ≈  +3.4·S·B   and GROWING at every (B,S) tested
    (S=2: 12.8 → 91.0 for B=3..14; S=3: 30.9 → 142.9 for B=4..14).
    Real-place decay ≈ −7.4 B² (log10) against an integerizer ≈ +7.9 B²; both are B², the
    difference is ~ S·B.  No constant fixes this; the construction loses at the odd primes / ∞
    once the 2-adic F_B is removed.

Verdict: **Sun's construction (weights `1/(2m+1)`, normaliser `Π_i`) does not produce small
integer forms, with or without `F_B`.**  N1 is refuted as a repair; N2 (even normaliser) is moot
for the same reason unless it also shrinks `Δ_B` by ~S·B in the log, which nothing suggests.
Re-run: `uv run --with mpmath python3 papers/sun-2026-catalan-twoadic-check.py ledger 14 2`.

### ☠️ Killed thread: Path 1 positive forms from the EMN motive (2026-09-04, host, `papers/catalan-emn-search.py`)

Eskandari–Murty–Nemoto (arXiv:2510.20648) give `I(F,t) = ∫_Δ F/(1−x²−y²)^{t+1} = a + bG` for
σ-invariant `F` with `x^{2⌈t/2⌉}y^{2⌈t/2⌉} | F`.  Their construction was made exact and general
here (every branch validated to 30 digits against quadrature).  The only non-Dirichlet-trivial
search is over **positive** forms `F = σ-orbit-sum(h²)`, where `I(F,t) = cᵀ(A + BG)c` is an exact
quadratic form and the minimisation is an SVP (LLL).  Scan `N ≤ 20`, `0 ≤ t ≤ 6`: best
`log10(D·I) ≈ −1.16` (`N=16–18, t=3`), never trending to `−∞`; per degree the integral shrinks
like `≈ 10^{−0.35}` (≈ `2^{−1}`) while the exact integerizer grows like `≈ 10^{+0.5}` — the same
factor-of-4-per-degree gap the authors computed from their uniform bound (Remark 8.3.4).  LLL beats
the best single monomial square by ≤ 1 order of magnitude, not exponentially.  Limits: `N ≤ 20`,
float64 LLL (dims ≤ 66).  Positivity via SOS is sufficient, not necessary; a signed family needs a
*proof* of decay (Padé/hypergeometric), which is Path 3's world.  Re-run:
`./papers/catalan-emn-search.py validate && ./papers/catalan-emn-search.py scan 20 6`.

### Phase 3 — ACTIVE (authorized by Trevor 2026-09-04, "dig in!") — the generic frame

**File: `Frame.lean`** (wired into `src/LeanFormalizations.lean`; module docstring carries a
proof plan per leaf; every statement below was hand-derived AND numerically checked before
freezing — D5 to 55 digits, E1 exactly).  The payoff is being the fastest independent verifier
of whatever v2 lands, not a proof of irrationality: **the sink stays a non-target**, `SmallForms`
is a `def … : Prop` and must never become a theorem (the host probe says it is false for these
weights).

**Frozen statements, guarded BY NAME** (host `--require-decls` on `Frame.lean`; do not rename,
weaken, generalise-into-restriction, or delete — if one is WRONG, fix it loudly, per Phase 1):
`irrational_of_forms` · `alt_choose_sum_inv_eq` · `alt_choose_sum_inv_sq_eq` ·
`alt_choose_sum_div_sq` · `redPi` · `resid_tail_eq` · `oddLcm` · `resid_fakeTail_den` ·
`det_resid_fakeTail_den` · `abs_det_ge_of_rational` · `SmallForms` ·
`catalan_irrational_of_smallForms`.

**Order** (each a green checkpoint — commit each):
1. **W**: `irrational_of_forms` (cheap; `Int.one_le_abs` against `Tendsto … (𝓝 0)`).
2. **E**: `oddLcm_pos` → `odd_dvd_oddLcm` → `resid_fakeTail_den` → `det_resid_fakeTail_den` →
   `abs_det_ge_of_rational` → **`catalan_irrational_of_smallForms`** (the sink edge; consumes E3
   + `fakeTail_eq_tail_of_catalan_eq` + `RingHom.map_det`).  Landing the sink edge is the lap's
   headline: it makes "the ledger is the only missing thing, and E3 is its floor" kernel-checked.
3. **D**: `alt_choose_sum_inv_eq` → `alt_choose_sum_inv_sq_eq` → `lin_dvd_bigPi` /
   `redPi_mul_lin` / `natDegree_redPi_le` → `alt_choose_sum_div_sq` → **`resid_tail_eq`**
   (the real-place engine; the swap of `Σ_i` with `∑'_r` is the only analysis).
Steps 1–2 and 3 are independent; if D stalls, land W+E and come back.  Decomposing a fat leaf
into named sub-lemmas is progress.  **No asymptotic estimate is to be attempted in Lean** — the
bound on the RHS of `resid_tail_eq` is a probe question, not a Lean question.

**Before the hard part of any lap: commit a compiling skeleton with named `sorry` leaves.**

### The original Phase 2 text (kept for provenance)

Sun's stages 3–5 die for a *structural* reason: the `2B` monomial reference columns `i^r` make
the finite-difference transform triangular with pivots `r!`, planting `F_B = ∏_{r<2B} r!`
(`2^{2B²}` of 2-power) in the integer, against a normaliser `∏Π_i` that is entirely odd.  Any
"patch" must change the *construction*, not a constant.  Two levers, each a candidate node:
- **N1 (binomial completion)**: with reference columns `C(i, r)` the transform is unitriangular,
  so the analogue of (3.4) is `det Ã_B = ± det R[A,J]` with NO `F_B` — a true, cheap linear-algebra
  statement.  It removes `F_B` from the 2-adic ledger *and* from the real one, so the real-place
  size of the new integer `N'_B := num(q^S det R[A,J]/∏Π_i)` is the open question.
- **N2 (an even normaliser)**: replace `Π_i` by a family with 2-power content while keeping the
  polynomial-divisibility that Theorem 2.1's proof needs (`(2(i+k)+1)^2 ∣ Π_i` for `1 ≤ k ≤ S`).
**Discipline — paths before roads.**  A Phase-2 node is a `def … : Prop` with a provenance
docstring, an odds estimate, and a **numeric refutation probe** run FIRST:
`papers/sun-2026-catalan-twoadic-check.py` already prints, for a fake `G = a/q`, both the paper's
`N_B` and the `F_B`-free `N'_B` (valuations and digit counts); extend it for N2.  A node whose
probe says the integer *grows* with `B` is refuted — record that as progress (a killed-thread
entry), do not build a road to it.  No asymptotic ledger is to be attempted in Lean.  Do not
propose Lean discharges for Phase-2 nodes; the deliverable there is the stated `Prop` + probe
result + the next story.

## Phase 4 — ✅ DONE 2026-09-04 (planted 2026-09-04) — the nearest TRUE theorem: one of β(2),…,β(20) is irrational

**Status**: all eight leaves closed; `exists_even_beta_irrational` and `catalan_or_higher_beta_irrational`
are `#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry` in the directory.  N2 landed via
`Symmetry.lean` (reflection `R_n(-t-n)=R_n(t)`, symmetrized coefficients, odd vanishing) +
`PartialSums.lean` (shift recursion `T_q(a+1) = 1/a^q - T_q(a)` from the base `T_q(½)=2^q E_q`) +
the assembly in `LinearForm.lean`.

**Independently verified by the architect (2026-09-04), not taken on the lap's word.**  Definitions
did not drift: `dirichletBeta`, `Rval`, `rForm`, `dn` are byte-identical to the scaffold commit
`225c11f`, so the headline is about the objects that were frozen and numerically validated.  The
only frozen-signature change in the whole run is `rForm_neg`'s unused `hodd` binder becoming
`_hodd`.  Axiom footprints re-printed from a separate file, including the wiring
`exists_irrational_of_forms`.  `src/` is `sorry`-free by a scan that excludes prose (a naive grep
returns 38 hits, all of them the word "sorry" inside docstrings — do not read that number as
checkpoints).

**Two laps found better mathematics than the plan specified.**  N3, the crux, went **integral-free**
— strictly completely monotone sequences instead of the `s`-fold Beta integral, and it does not need
`Odd s`.  N2 avoided derivatives entirely, via a partial-fraction integrality lattice.  That is the
scaffold working as intended: the frozen statements were the contract, the routes were the lap's to
choose, and it chose better than I had.  Original planting text follows.

**Lane**: *formalizing a known result* (not moonshot).  Directory
`src/LeanFormalizations/NumberTheory/DirichletBeta/`.  Scaffold planted and green; eight `sorry`
leaves remained at planting (all now closed), and **the headline is already wired**: `Statement.lean` is proof-complete, so
closing the leaves closes the theorem with no further design work.

**The theorem** (Rivoal–Zudilin 2003, Math. Ann. **326** 705–721 / Zudilin 2019 arXiv:1804.09922 §2,
made elementary in the pattern of his SIGMA 2018 odd-zeta paper `papers/zudilin-2018-odd-zeta-elementary.txt`):

    exists_even_beta_irrational : ∃ i ∈ Icc 1 10, Irrational (dirichletBeta (2 * i))

i.e. **at least one of β(2), β(4), …, β(20) is irrational**.  `β(2) = G`, so
`catalan_or_higher_beta_irrational` restates it as "`G` is irrational, or one of β(4),…,β(20) is".
⚠️ This does **not** claim `G ∉ ℚ`; every disjunct is individually open.  Nobody has formalized any
result of this type (reservoir + mathlib swept 2026-09-04).

**The ledger** (`s = 21`, `n` even, `d_n = lcm(1..n) = Nat.lcmUpto n`):

    Rval s n u = 2^{6n}(n!)^{s-3}(3n+1+2u)·(u+3n)!/u! / ∏_{j=0}^{n}((2(n+1+u+j)-1)/2)^s
    rForm s n  = Σ_{u≥0} (-1)^{n+u+1} Rval s n u                       ( = r_n, Zudilin's linear form )
    d_n^21·r_n = A_0 + Σ_{i=1}^{10} A_i β(2i),  A_i ∈ ℤ                (N2)
    r_n < 0                                                            (N3, the crux)
    |r_n| ≤ e^{-21.3 n},   d_n ≤ e^{1.01 n}                            (N4, N5)
    ⇒ |d_n^21 r_n| ≤ e^{(21·1.01 − 21.3)n} = e^{-0.09n} → 0, a nonzero integer form → contradiction.

True rates: `lim|r_n|^{1/n} = e^{-21.657}` and `d_n^{1/n} → e`, so `21 < 21.657` closes with
`0.657/n` to spare; the frozen constants `-21.3` and `1.01` spend part of that margin to keep the
bounds coarse.  **Do not tighten them** — any pair with `21·c₅ < −c₄` works, and the slack is what
makes N4/N5 elementary.

**Frozen names** (guard by name; the shapes are the contract):
- `Beta.lean` — `dirichletBeta`, `summable_betaTerm`, `beta_two_eq_catalanConst`
- `Rational.lean` — `Rval`, `rForm`, `Rval_pos`, `summable_Rval`
- `LinearForm.lean` — `dn`, **`exists_int_combination`** (N2)
- `Integral.lean` — **`rForm_neg`** (N3, the crux), `rForm_ne_zero`
- `Bound.lean` — **`abs_rForm_le_exp`** (N4)
- `Lcm.lean` — **`dn_le_exp`** (N5)
- `Statement.lean` — `exists_irrational_of_forms` (W', proved), `exists_even_beta_irrational`
  (proved from the leaves), `catalan_or_higher_beta_irrational` (proved)

**Order of attack** (easiest first; each is independent):
1. **N5 `dn_le_exp`** — nearly free: `Chebyshev.psi_eq_log_lcmUpto` (mathlib) + `WeakPNT''`
   (`PrimeNumberTheoremAnd.Consequences`) give `log d_n / n → 1`.
2. **`summable_betaTerm`, `beta_two_eq_catalanConst`** — routine; `Catalan/Tails.lean` has the
   summability pattern and `catalanConst = tail 0` is definitionally the same series.
3. **`Rval_pos`, `summable_Rval`** — positivity is `positivity` once the factorials are unfolded;
   summability from the `u^{3n+1−s(n+1)} ≤ u^{-2}` decay.
4. **N2 `exists_int_combination`** — the arithmetic grind: partial fractions of `R_n`, SIGMA
   Lemma 1 integrality `d_n^{s−i}a_{i,k} ∈ ℤ`, odd-`i` vanishing from `R_n(−t−n) = R_n(t)`.
   Only the *existential* is frozen, so any route is fair.
5. **N4 `abs_rForm_le_exp`** — bound `|r_n|` by `poly(n)·max_u|Rval 21 n u|` (legitimate: the
   ledger probe shows max-term rate = exact rate), then explicit factorial/Stirling bounds.
6. **N3 `rForm_neg`** — the crux: the `s`-fold Beta integral
   (`integral_fintype_prod_eq_prod`, binomial series of `(1−T)/(1+T)^{3n+2}`).  Sign convention
   `r_n = −C_n·∫` is **verified numerically** — do not re-derive it from scratch.

**Every frozen statement was validated numerically before planting**, on exactly the hypothesis
range it states (`Odd s`, `Even n`, `3 ≤ s`) — the Phase 3 `E1` lesson.  Probes:
`papers/catalan-beta-validate.py` (integrality, decomposition, the integral at `s=3,n=2`),
`papers/catalan-beta-ledger.py` (rates, odd `s` from 7 to 41 at `n=40`),
`papers/catalan-beta-rval-check.py` (the shifted `Rval` against the source `R_n(ν−½)`: termwise
**exact**).  ⚠️ If a lap finds a frozen statement FALSE, say so loudly and stop that leaf — that
is a result, not a failure (Phase 3 found `E1` false and it was the most valuable thing the lap did).

## NOT a stop condition
Do NOT stop because a leaf landed, "to take stock", or because N3 is hard.  Closing N5 or the
`Beta.lean` pair is a lap's worth of progress on its own.  Trevor ends the run.

## Lane discipline
- Work ONLY in `src/LeanFormalizations/NumberTheory/DirichletBeta/` (Phase 4, the live lane) and
  `src/LeanFormalizations/NumberTheory/Catalan/` (Phases 1–3, green — read, don't churn).  New files get wired into
  `src/LeanFormalizations.lean` (the lib builds only what is reachable from that root).
- **DO NOT TOUCH** any other thread (`Transcendence/`, `Constructible/`, `Curtis/`, `PowerTower/`,
  `Logic/`, `Combinatorics/`, `Kakeya2D/`, `PrimeNumberTheorem/`).  Read them for technique.
- No `axiom`, ever.  `decide +kernel` before `native_decide`; `native_decide` must not touch a
  headline's axiom path.  A disclosed `sorry` in `src/` is a checkpoint; a bare axiom is not.
- Goal end-state for every headline: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
  Run it when you close a real leaf; mention the tier only if it fails.

## Rules (same as every autonomous run here)
- **Commit every green build** from a real `lake build` you saw succeed.  **NEVER push** (the host
  pushes).  Never claim green you didn't see.  Work on the `catalan` branch.
- Toolchain `v4.31.0`, mathlib `v4.31.0`.  Verify lemma names against THIS repo's mathlib
  (`.lake/packages/mathlib`).  `push_neg` is deprecated → `push Not at h`.
- **Reference corpus** (cross-lap memory, NOT auto-loaded):
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/` — `ls` it at lap start and
  `grep -rl <keyword>` it before re-deriving any tactic/API friction.
- Blocked needing the open web?  First check `ON-LINE-FINDINGS-*.md`; else append a dated, specific
  item to `ON-LINE-REQUEST.md` and continue on another leaf.  Do not block.
- **Don't mark new declarations `private`.**  Helpers are reusable facts, and hiding them has already caused duplication: phase 31 reproved a companion-matrix construction, phase 32 copied `exists_trace_pow_congr`, and phase 33 needed a visibility edit to a frozen file.  Give helpers specific, namespaced names instead.  Existing `private` declarations may be made public whenever something needs them.  (Trevor, 2026-09-29: *"Why would you keep something true private?"*)
- Keep `HANDOFF.md` current (thin pointer) and write a dated `HANDOFF-<date>-<desc>.md` at lap end;
  on the governor's budget signal, `/handoff` and end the lap.

## NOT a stop condition
No self-stop until every `sorry` in `src/LeanFormalizations/NumberTheory/DirichletBeta/` is closed
and `exists_even_beta_irrational` is axiom-clean.  Do NOT stop because a leaf landed, "to take
stock", or because N3 is hard.  Trevor ends the run.

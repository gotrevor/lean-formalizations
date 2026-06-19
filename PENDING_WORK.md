# PENDING_WORK — no-three-in-line / HJSW frontier (branch `ntl-hjsw`)

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

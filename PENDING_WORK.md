# PENDING_WORK — lean-formalizations

## 🎯 ACTIVE FRONTIER (refreshed 2026-06-19 lap 2 — A4 CLOSED)

**Section A (growth theory of `ONote.fastGrowing`) is COMPLETE + axiom-clean.** A1
(`le_fastGrowing`), A2 (`fastGrowing_monotone`), A3 (`fastGrowing_bachmann_reach`), **A4
(`fastGrowing_lt_fastGrowingε₀`)** all proved. The A4 engine (`Domination.lean`): CNF `norm`,
`lt_fundamentalSequence_of_norm_le` (key cofinality bound), `reaches_of_lt` (general
reachability), `osucc` + strict step. General index monotonicity `fastGrowing_le_of_lt` /
`hardy_le_of_lt` added. `Logic/FastGrowing/*` is sorry-free.

### C2 — the semantic bridge `toOrdinal` ↔ `ONote.repr`  ✅ DONE (2026-06-19 lap 2)
`Logic/Goodstein/Growth.lean` (axiom-clean): `toONote b n` (the computable notation),
`repr_toONote : (toONote b n).repr = toOrdinal b n`, `toONote_NF`, and the descent on `ONote`:
`seqONote m k := toONote (k+2) (goodsteinSeq m k)`, `repr_seqONote = Engine.seqOrd m k`, and
**`seqONote_lt`** (`goodsteinSeq m k ≠ 0 ⟹ seqONote m (k+1) < seqONote m k`). The Goodstein
ε₀-descent now lives on the same `ONote` as the fast-growing growth theory.

### NEXT CRUX: C3 — `goodsteinLength m = H_{seqONote m 0}(2) − 2`  (the Cichoń identity)
**MEASURED + PROVED modulo ONE narrow sorry (2026-06-19 lap 3).** The whole C3 chain is built
and the headline holds modulo a single isolated lemma. Identity (native_decide-confirmed):
`hardy (seqONote m 0) 2 = goodsteinLength m + 2`. Done this lap:
- **Intrinsic Hardy machinery** (`FastGrowing/Hardy.lean`, axiom-clean): `hstep` (budget-
  incrementing Hardy step on `ONote`), `hardy_hstep : o≠0 → H_o(n)=H_{hstep o n}(n+1)`,
  `fundamentalSequence_inr_ne_zero`, `hstep_oadd_tail` (peel leading `oadd` term).
- **C3 assembly** (`Goodstein/Growth.lean`): `hstep_seqONote`, `hardy_seqONote_step` (per-step
  invariance), `hardy_seqONote_telescope`, `hardy_seqONote_zero`, `goodsteinLength_eq_hardy`
  (HEADLINE). Helpers `toONote_bump`, `toONote_oadd`, `toONote_single`,
  `fundamentalSequence_oadd_zero_zero`, `hstep_oadd_zero_zero`.
- **The crux `hstep_toONote`** (`hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`): strong
  induction on `p = c·b^L + r`. PROVED: `r≠0` (tail recursion via `hstep_oadd_tail` + IH +
  `toONote_oadd`/`toONote_bump`) and `r=0 ∧ L=0` (finite, `hstep_oadd_zero_zero`).

**THE LONE OPEN CORE: `hstep_oadd_one_zero` (general `L≥1`, `c=1`)** — predecessor of `ω^E`,
`E = toONote b L`. Target: `hstep (oadd (toONote b L) 1 0) b = toONote (b+1) ((b+1)^(bump b L) − 1)`.

**DONE 2026-06-19 lap 4 (4 commits) — crux narrowed `r=0,L≥1` ⟶ this single `c=1` lemma:**
1. **Lemma A (coefficient peel) — PROVED.** `hstep_oadd_coeff` (+ `fundSeq_oadd_coeff`): for
   `E≠0, c≥2`, `hstep (oadd E ⟨c⟩ 0) b = oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`. The `r=0,L≥1`
   branch of `hstep_toONote` is now FULLY PROVED modulo `hstep_oadd_one_zero` (c=1).
2. **Lemma B finite base case — PROVED.** `hstep_oadd_one_zero_finite`: `E = finite(d+1)`,
   `d≤b`, gives `(b+1)^(d+1)−1`. Validates the whole recursion engine end-to-end.
3. **Recursion primitives — PROVED.** `hstep_oadd_one_of_succ`/`_of_limit` (descent on
   `oadd E 1 0`), `fundSeq_oadd_one_of_succ`/`_of_limit`, `hstep_finite_pred`, `fundSeq_finite_succ`.
4. **`evalNat` linchpin — PROVED.** `evalNat b o` (= `repr o` read as base-`(b+1)` numeral);
   `evalNat_toONote : evalNat b (toONote b L) = bump b L`. The general answer is
   `toONote (b+1) ((b+1)^(evalNat b E) − 1)`.

**Remaining (next lap): the general recursion.** WF recursion on `repr E`:
- **Limit case CLEAN** (no reconstruction): `hstep_oadd_one_of_limit` → IH on `f b`, closes via
  `evalNat (f b) = evalNat E` (identity `evalNat_fundSeq`, TODO — at the fixed index `b`).
- **Successor case** needs `evalNat E = evalNat E' + 1` (`evalNat_succ`, TODO) AND the
  reconstruction `toONote (b+1) (evalNat E') = E'` for `E' = pred E`. Reconstruction is the
  real wall: it holds for base-`(b+1)`-CNF `E'` but the descent's `f b` introduces coefficient
  `b+1` (at index `b`). KEY OBSERVATION: that `b+1` is always immediately peeled by
  `hstep_oadd_coeff`, and `pred` of a reachable successor keeps coefficients `< b+1` at the
  decremented position — so a **coefficient-bound invariant** (≤ b+1, with the b+1 only where
  peelable) makes reconstruction go through. Formalize that invariant + the two `evalNat`
  identities, then the WF recursion closes `hstep_oadd_one_zero`.
3. **Aristotle: job `77c99f0e`** still RUNNING on the (pre-narrowing) general borrowing goal —
   if it returns a full proof, it subsumes everything; VERIFY + `#print axioms` before porting.

### Domination corollary (after the C3 identity closes)
With `goodsteinLength_eq_hardy` + A4 (`fastGrowing_lt_fastGrowingε₀`) + `hardy_le_of_lt`, derive
`goodsteinLength` eventually outgrows every `fastGrowing o`; then a thin audit-surface headline.

### B ladder (Hardy) — lower priority
B2/B3 done. **B4** (`H_{ω^α}=f_α`) is a trap under mathlib's `ω[n]=n+1` (measured: not a
constant shift, `H_{ω^2}(2)=23 ≠ f_2(2)+1=9`). Needs a reformulated statement; long-horizon.

---

## 🔭 OPEN-ITEM INVENTORY (refreshed 2026-06-17, operator directive)

`src/` is **100% axiom-free** (0 custom axioms, 0 `sorry`/`admit`; `lake build` green, 8274
jobs). Three threads are COMPLETE + axiom-clean — **do not reopen**: Curtis 1990
(no-Frobenius-formula), π/e-transcendence + squaring-the-circle (the `hermite_lindemann` axiom
was discharged + deleted 2026-06-16), and constructible numbers / Wantzel (full iff + 5 classical
impossibilities). Completion records below.

### ✅ COMPLETE (2026-06-18) — power-tower SHARP `iff` (the `0 < x < e^(-e)` divergence)
**DONE, axiom-clean.** The operator-directed target of the 2026-06-17 `DIRECTION.md` is
finished. `EngineLower.tower_diverges_lower` (`0<x<e^(-e) ⟹ ¬∃L`) + the headline
`Statement.tower_converges_iff_full` (`x>0` converges **iff** `x ∈ [e^(-e), e^(1/e)]`) are
both proved; `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The proof followed
the planned route exactly: `fixedpoint_exists` (IVT fixed point `y`), `log_fixedpoint_lt_neg_one`
(the repelling seed `x<e^(-e) ⟹ log y < -1` — by contradiction, `log y ≥ -1 ⟹ y ≥ 1/e ⟹
-ye ≤ -1`, no `v·e^v` monotonicity lemma needed), `strict_two_cycle_exists` (IVT on `g-id`
both sides of `y`, where `g'>1` on a neighbourhood from continuity of `g'` + `g'(y)=(log y)²>1`),
and the even/odd-trapping bound (`a(2n) ≥ γ₀ > β₀ ≥ a(2n+1)`) ⟹ distinct limits ⟹ no limit.
The subsequence construction is now the shared `tower_subseq_limits` (used by both directions).
The Lóczi §3 reference was NOT needed (no `ON-LINE-REQUEST` filed).

### ✅ COMPLETE (2026-06-16) — π/e-transcendence, axiom-clean, `hermite_lindemann` DELETED
`Transcendence.transcendental_pi` proved from first principles, axiom-clean;
`squaring_the_circle_impossible_uncond` rewired to it; the cited axiom deleted → repo
math-axiom count = **0**. Assembly: `ETranscendental.lean` (`e_transcendental`, the Hermite
assembly of `exp_polynomial_approx`) → `PiLindemann.lean` (combinatorial reduction + non-monic
analytic engine) → `MonicRootSums.lean` (fact (a) `sum_aeval_roots_int`, Aristotle `9a19f72e`)
→ `SubsetSumEsymm.lean` (fact (b) `subsetSum_esymm_rational`, fundamental theorem of symmetric
polynomials, Aristotle `b7252abe`) → `PiTranscendental.lean`. Both Aristotle proofs independently
kernel-verified. (For the *alternative* path not taken — adopting mathlib PR #28013 on a future
bump — see `archive/findings/ON-LINE-FINDINGS-2026-06-15-pi-transcendence.md`.)


## ✅ COMPLETE (2026-06-14, operator-bounded run): Curtis verification hardening

All four items in `DIRECTION.md` are built, green, sorry-free, axiom-clean
(commits `ea89147`, `0498df8`). Every optional stretch part was also done:

1. ✅ `Boundary.n2_polynomial_relation_exists` — Sylvester hypersurface; n=2/n=3 line.
2. ✅ three new Lemma-2 anchors (⟨3,7,11⟩, ⟨3,13,14⟩, ⟨5,11,23⟩, one also direct) +
   ✅ stretch `frobeniusNumber_6_9_20` (McNugget 43, outside Curtis's family).
3. ✅ `symmetric_guess_not_a_formula` (worked) + ✅ stretch `no_single_polynomial_formula`.
4. ✅ `Curtis/FINDINGS.md` + fixed stale docstrings in `Engine.lean` / `Curtis/README.md`.

Run self-stopped on completion per `DIRECTION.md` (sentinel written). The PARKED targets
below remain Trevor's call for a future, separately-scoped run.

---

## ✅ COMPLETE (2026-06-14, power-tower LOWER half run)

Mandatory `tower_converges_of_mem` (convergence on the FULL Euler interval
`[e^(-e), e^(1/e)]`) is PROVED and **fully axiom-clean** (`[propext,
Classical.choice, Quot.sound]`). The lower-bound crux `two_cycle_collapse` (no
nontrivial 2-cycle of `t↦x^t` for `x ≥ e^(-e)`) is **machine-checked, no axiom** —
via the slope bound `g'(t) ≤ |log x|/e ≤ 1` (`EngineLower.lean`): contraction +
Banach for `x > e^(-e)`, antitone-on-interval for the boundary `x = e^(-e)`.
(The DIRECTION's "subtract the tangent-line inequalities" sketch is mathematically
invalid; the derivative/slope bound is the correct mechanism.)

### Sharp `iff` lower direction (`0 < x < e^(-e)` diverges) — NOW THE ACTIVE TARGET
`tower_converges_iff_full` was omitted as a stretch on the 6-14 run (the convergence half
`tower_converges_of_mem` + `tower_diverges` shipped; the lower divergence requires a *genuine
attracting 2-cycle*, multi-lap real analysis). **As of 2026-06-17 it is the directed goal —
see `DIRECTION.md` and "THE ONE ACTIVE ITEM" at the top.** NO `sorry` was ever left here.

---

## ✅ COMPLETE (2026-06-15): P1 Layer 1 — constructible-numbers algebraic core + all three classical impossibilities

`Geometry/Constructible/` — **PROVED, axiom-clean** (`[propext, Classical.choice,
Quot.sound]` on every headline). Exactly the Layer-1 plan below, and then some:
- `IsSqrtTower` / `IsConstructible` on `IntermediateField ℚ ℝ`; engine
  `IsSqrtTower.finrank_eq_pow_two` (degree `2ⁿ`) via tower law + quadratic step.
- **Doubling the cube**: `cbrt2_not_constructible` (`minpoly ℚ ∛2 = X³−2`,
  Kummer-irreducible; `[ℚ(∛2):ℚ]=3`).
- **Trisecting 60°**: `cos20_not_constructible` (triple-angle ⟹ `2cos20°` root of the
  monic `X³−3X−1`, irreducible by integral-root theorem; degree 3).
- **Squaring the circle**: `squaring_the_circle_impossible (hπ : Transcendental ℚ π)`
  via `IsConstructible.isAlgebraic`. Conditional on `π`-transcendence (mathlib gap).
- Constructibles form a **subfield closed under √** (`IsSqrtTower.sup_exists` +
  `IsConstructible.{add,sub,mul,neg,inv,sqrt}`, `isConstructible_ratCast`).

### ✅ DONE (2026-06-16): P1 Layer 2 + the full converse — Wantzel as an iff
The geometric faithfulness layer is COMPLETE and axiom-clean, and then some:
- `ConstructiblePoint : ℝ×ℝ → Prop` (inductive: `{(0,0),(1,0)}` closed under
  line∩line / line∩circle / circle∩circle). `ConstructiblePoint.isConstructible_coords`
  proves geometry ⟹ algebra via `line_meet_line` / `line_meet_circle` /
  `circle_meet_circle` (`ConstructiblePoint.lean`).
- **Converse** (`Converse.lean`): `AxisConstructible` closed under `+,−,·,⁻¹,/,√` by
  explicit compass constructions; tower induction `isSqrtTower_le_axisField` gives
  algebra ⟹ geometry. Headline `isConstructible_iff_constructiblePoint`.
- Geometric impossibility headlines (`cbrt2_point_not_constructible`,
  `heptagon_point_not_constructible`); positive `isConstructible_cos_pi_div_five`
  (pentagon); heptagon added (`Heptagon.lean`, 5th classical instance).

### ✅ DONE (2026-06-16): squaring-the-circle is now UNCONDITIONAL
`squaring_the_circle_impossible_uncond` no longer takes a hypothesis — it is wired to the
axiom-clean `Transcendence.transcendental_pi` (full Lindemann assembly; see the π completion
record at the top). The "multi-year wall" was discharged from first principles. No axiom remains.

### ✅ DONE (2026-06-16): regular heptagon / 7-gon
`Heptagon.lean` — `twoCosHept_not_constructible`, axiom-clean. Minpoly `X³+X²−2X−1`
derived from `cos(4θ)=cos(3θ)` at `θ=2π/7` (factor out the `c=1` root).

## 🅿️ PARKED — future runs, Trevor's call (NOT this run; do not start)

Preserved for a future, separately-scoped run. These are genuine extensions but are
**explicitly out of scope now** — do NOT treat them as "open frontier" when deciding to stop.

### P2. Upstream Curtis to `Mathlib.NumberTheory.FrobeniusNumber`
mathlib has the n=2 Chicken-McNugget theorem and notes it stops at n=2; Curtis's n=3
impossibility is the natural sequel. Needs a mathlib style pass (drop the bespoke
`IsAdmissible`/audit framing for an idiomatic statement) and an AI-contribution-policy check
(reference corpus: `2026-06-07-mathlib-ai-contribution-policy.md`). Web/CLA-gated.

### P3. Sharpen the "not algebraic" framing
State explicitly: `(s₁,s₂,s₃,g)` lies on no proper hypersurface of ℂ⁴ (graph Zariski-dense).
A short repackaging of `no_polynomial_relation`. (Item 4 of the active run *documents* this;
P3 would be a full theorem-level statement — defer.)

---

## Lemma2.lean lint warnings — LEAVE THEM
The unused-variable warnings on `lemma2`'s hypotheses (`h1,h2,h3,hk_hi,hr_hi`) are the
*mathematical* hypotheses of Curtis's Lemma 2, kept for the audit surface even though this
proof path doesn't consume all of them. Do not strip them. The two unused-simp-arg warnings
are inside Aristotle-verified tactic blocks — not worth the regression risk to touch.

## Aristotle
Nothing genuinely open → Aristotle correctly idle. The old Lemma-1 job (`80d9166c`) is
OBSOLETE (the proof needs no Lemma 1). Do not feed redundant cross-confirms. The verification
items 1–4 are all elementary and do NOT need Aristotle.

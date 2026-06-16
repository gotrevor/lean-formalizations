# PENDING_WORK — lean-formalizations

## 🔭 OPEN-ITEM INVENTORY + ATTACK PATHS (refreshed 2026-06-16, review lap)

`src/` is axiom-clean except for **one cited axiom** (`hermite_lindemann`, 🟡) and
**one disclosed `sorry`** (`no_intPoly_aeval_eq_zero`, the active chip toward it).
The active frontier is discharging the transcendence wall behind squaring-the-circle.

### ✅ DONE this lap — Open item A.1: `Transcendental ℚ Real.pi` narrowing
Stated **Hermite–Lindemann** (`hermite_lindemann`: nonzero algebraic α ⟹ `exp α`
transcendental) as one disclosed `axiom` and machine-checked `transcendental_pi` from it
(Euler `exp(iπ) = -1`). `squaring_the_circle_impossible_uncond` shipped; `#print axioms`
= trust base + `hermite_lindemann` only. File `NumberTheory/Transcendence/HermiteLindemann.lean`.

### ✅ DONE this lap — Open item A.2: transcendence of `e`, fully axiom-clean
`ETranscendental.lean` — `e_transcendental : Transcendental ℚ (Real.exp 1)`,
`#print axioms` = trust base only. The complete Hermite assembly of
`LindemannWeierstrass.exp_polynomial_approx`: algebraic reduction
(`exists_intPoly_aeval_eq_zero`) + analytic decay/prime-selection
(`tendsto_const_mul_pow_div_factorial`, `exists_prime_smallness`) + Hermite-polynomial
data (`hermitePoly_eval_zero_ne`, `hermitePoly_aroots`) + the integer-`N`/mod-`p`
contradiction (`no_intPoly_aeval_eq_zero`). Discharges the `α=1` instance of
`hermite_lindemann`. (Aristotle job `e502fd22` canceled — proved locally.)

### 🎯 ACTIVE — Open item B: `hermite_lindemann` for `π` (the conjugate-product extension)
To make squaring-the-circle fully unconditional, discharge `hermite_lindemann` at
`α = iπ`. Unlike `e`, this needs the **algebraic part** of Lindemann–Weierstrass —
symmetric functions over the Galois conjugates.

**KEY (from `archive/findings/ON-LINE-FINDINGS-2026-06-15-pi-transcendence.md`): the
realistic axiom-kill is adopting mathlib PR #28013** ("feat: Lindemann-Weierstrass
Theorem", Yuyang Zhao — the same author as `AnalyticalPart.lean`). It adds, over `ℤ`,
`transcendental_pi`, `transcendental_e`, `transcendental_exp` (= our `hermite_lindemann`
as a real theorem), `transcendental_log`, `linearIndependent_exp`. It's OPEN/awaiting-author,
not merged. **When mathlib is next bumped past the merge:** delete `axiom hermite_lindemann`,
`import …Lindemann.Basic`, and bridge `Transcendental ℤ π → Transcendental ℚ π` via
`transcendental_algebraMap_iff` / `isAlgebraic_algebraMap_iff` (ℤ↔ℚ, char 0). That kills
the axiom with no local algebraic-part build. Findings recommend NOT re-deriving the
algebraic part locally. The local route is only worth it if no bump is coming; if pursued,
attack paths:
1. **Hermite–Lindemann for a single algebraic α** (Baker ch.1 / Niven): let `α` have
   minimal polynomial with conjugates `α = α₁,…,α_d`; the product `∏_j (relation at α_j)`
   has *symmetric* (hence rational, then integer after scaling by `den^?`) coefficients —
   feed `exp_polynomial_approx` to `f = den·minpoly` and re-run the integer-`N`/mod-`p`
   contradiction. The `e` assembly here is the reusable analytic core; the NEW piece is
   the symmetric-function integrality (`MvPolynomial.symmetric`, `Multiset.esymm`,
   Newton's identities / `Polynomial.roots` of the conjugate set). Build that as a
   standalone lemma first.
2. **Lindemann–Weierstrass directly for `{0, iπ}`**: `e^0 + e^{iπ} = 0` is a ℚ-linear
   dependence of `exp` at distinct algebraic exponents `0, iπ`; LW says that's impossible
   unless `iπ` non-algebraic. Same symmetric-function machinery, framed as lin. indep.
3. **Architect for Aristotle**: once the symmetric-function leaf is isolated, hand it over
   (`aristotle submit`, project-dir). `ON-LINE-REQUEST.md` filed for porting templates
   (Isabelle AFP `Lindemann_Weierstrass`).

### Open item C — power-tower sharp `iff`, lower direction (`0<x<e^{-e}` diverges)
1. **2-cycle existence via IVT** on the second-iterate boundary map (sign change of `g∘g−id`).
2. **Instability ⟹ non-convergence**: fixed point repelling (`|g'(y)|>1`), tower off its
   stable manifold (monotone bracketing).
3. **Reformulate** as even/odd subsequences → distinct limits; reuse `EngineLower` in reverse.

### Open item B — power-tower sharp `iff`, lower direction (`0<x<e^{-e}` diverges)
1. **2-cycle existence via IVT on the boundary map**: show the second-iterate map has a
   nontrivial fixed pair `β<γ` for `x<e^{-e}` (sign change of `g∘g − id`), then attracting.
2. **Instability ⟹ non-convergence**: the fixed point `y` is repelling (`|g'(y)|>1`); show
   the tower from `a₀=1` is not on its stable manifold (monotone bracketing).
3. **Reformulate** as divergence of the even/odd subsequences to distinct limits and reuse
   the existing `EngineLower` slope machinery in reverse. (All multi-lap real analysis.)

### Open item C — Curtis upstream to mathlib (P2/P3 below) — web/CLA-gated, parked.


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

### OMITTED stretch — the sharp `iff` lower direction (`0 < x < e^(-e)` diverges)
`tower_converges_iff_full` is NOT shipped. The `x > e^(1/e)` direction is `tower_diverges`
(have it) and the convergence half is `tower_converges_of_mem`; the missing piece is
**non-convergence for `0 < x < e^(-e)`**, which requires proving a *genuine attracting
2-cycle exists* (`β < γ` strictly) — i.e. that the would-be fixed point `y` is repelling
and the tower from `a₀=1` does not land on its stable manifold. That is a separate,
multi-lap real-analysis development (instability ⟹ non-convergence), exceeding the
DIRECTION's ~2-lap budget for the stretch. Omitted with this note, NO `sorry`. Natural
next scope if the iff is wanted.

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

### Only open on this thread: make squaring-the-circle unconditional
Needs `Transcendental ℚ Real.pi`. mathlib has only the analytic part of
Lindemann–Weierstrass (`NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`),
not the conclusion. This is a multi-year wall (full Lindemann–Weierstrass) — debt,
not a one-lap target. Advance by formalizing the next missing Lindemann prerequisite,
or file an `ON-LINE-REQUEST` for the state of π-transcendence in any proof assistant.

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

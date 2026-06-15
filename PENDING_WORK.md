# PENDING_WORK — lean-formalizations

## 🔭 OPEN-ITEM INVENTORY + ATTACK PATHS (refreshed 2026-06-15, post-Wantzel)

`src/` is **sorry-free and has zero custom axioms** (verified: grep + `#print axioms` on
12 headlines = `[propext, Classical.choice, Quot.sound]`). The remaining work is
mathematical *extensions*, each blocked or multi-lap. Three concrete paths each:

### Open item A — `Transcendental ℚ Real.pi` (makes squaring-the-circle unconditional)
1. **Reduce-then-axiomatize**: state Lindemann–Weierstrass (lin. indep. of `exp` at
   distinct algebraic exponents) as a *disclosed* `axiom`, then PROVE `Transcendental ℚ π`
   from it natively (contrapositive: π alg ⟹ iπ alg; `e^{iπ}+e^0=0` contradicts LW). This
   isolates the deep wall to one cited statement and machine-checks the reduction. Bounded,
   build-safe, ~1 lap. **Most promising — do this first when budget allows.**
2. **Formalize the algebraic part of LW** on top of mathlib's `exp_polynomial_approx`
   (analytic part is present): the symmetric-function / Galois-conjugate-product argument
   forcing a nonzero integer `< 1`. Multi-lap; needs the reference from `ON-LINE-REQUEST.md`.
3. **Port** an existing prover's π-transcendence skeleton (Isabelle AFP
   `Lindemann_Weierstrass`) — needs the web; `ON-LINE-REQUEST.md` filed.

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

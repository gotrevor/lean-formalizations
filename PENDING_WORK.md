# PENDING_WORK — lean-formalizations

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

## 🅿️ PARKED — future runs, Trevor's call (NOT this run; do not start)

Preserved for a future, separately-scoped run. These are genuine extensions but are
**explicitly out of scope now** — do NOT treat them as "open frontier" when deciding to stop.

### P1. Compass-and-straightedge impossibility (constructible numbers / doubling the cube)
mathlib lacks constructible-number theory (its `Constructible.lean` is topology/spectra).
Plan (Layer 1 algebraic core): `IsSqrtTower` predicate on `IntermediateField ℚ ℝ`
(`base : ⊥`, `step` adjoining `a` with `a*a ∈ K`); `Constructible x := ∃ K, IsSqrtTower K ∧
x ∈ K`; prove `IsSqrtTower K → ∃ n, finrank ℚ K = 2^n` (tower law + `adjoin.finrank ≤ 2`);
witness `∛2` via `X³−2` Eisenstein-irreducible ⟹ `[ℚ(∛2):ℚ]=3`, `¬∃n, 3=2^n`. Layer 2 (hard,
multi-lap): faithful geometric definition (line/circle intersections) + bridge to quadratic
towers. Files would mirror Curtis's audit-surface/engine split under `Geometry/Constructible/`.

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

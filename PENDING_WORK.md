# PENDING_WORK — lean-formalizations

## 🎯 ACTIVE SCOPE (2026-06-14, operator-bounded run): Curtis verification hardening

**The ONLY authorized work this run.** Full specs in `DIRECTION.md`. Curtis 1990 is complete
and axiom-clean; this run adds independent faithfulness cross-checks, then STOPS.

1. **n = 2 boundary check** (`n2_polynomial_relation_exists`) — exhibit Sylvester's
   hypersurface; the theorem's content lives exactly at the n=2 / n=3 line. MANDATORY.
2. **More numerical anchors** — 2–3 extra Lemma-2-value vs `FrobeniusNumber` agreements
   (MANDATORY); optional `g(6,9,20)=43` outside-family check (STRETCH, omit if costly).
3. **Refute a candidate formula** — `symmetric_guess_not_a_formula` at ⟨3,7,8⟩ (MANDATORY
   worked example); optional general constructive corollary (STRETCH).
4. **Document free findings** (not-algebraic / sub-families-have-formulas) + fix stale
   "currently sorry" docstrings in `Engine.lean` + `Curtis/README.md`. MANDATORY.

**Completion → STOP.** When 1–4 are built (or stretch parts honestly omitted), `lake build`
green, `src/` sorry-free: this run is DONE. On a review/reflect lap, self-stop per
`DIRECTION.md` (allow-stop is armed). No `sorry` ever — omit an intractable stretch item.

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

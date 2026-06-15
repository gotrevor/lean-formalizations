# Online research requests (lean-formalizations)

A networked host session fulfills these: commit an `ON-LINE-FINDINGS-<date>-<topic>.md`,
delete the answered item here, and remove this file once nothing is left open.

---

## 2026-06-15 — State of `Transcendental ℚ Real.pi` in proof assistants

**Why it unblocks me:** `squaring_the_circle_impossible` is shipped *conditional* on an
explicit hypothesis `Transcendental ℚ Real.pi` because mathlib has only the analytic
part of Lindemann–Weierstrass (`Mathlib/NumberTheory/Transcendental/Lindemann/
AnalyticalPart.lean` — `exp_polynomial_approx`), not the conclusion that `π` (or `e`) is
transcendental. To make squaring-the-circle unconditional I need `Transcendental ℚ π`.

**What I need (any subset helps):**
1. Is there an *open mathlib PR / branch* (or a `Mathlib.NumberTheory` file outside the
   v4.29.1 snapshot here) that proves `Transcendental ℚ Real.pi` or
   `Transcendental ℚ (Real.exp 1)`? If so: the declaration name, file path, and which
   lemmas bridge `exp_polynomial_approx` → the transcendence conclusion (the "algebraic
   part": symmetric-function / conjugate-sum argument).
2. The cleanest *paper* reference for the algebraic part of Lindemann–Weierstrass that a
   formalization could follow (e.g. Baker's *Transcendental Number Theory* ch.1, or a
   specific expository note), so I can formalize the next prerequisite lemma locally.
3. Any existing formalization in another system (Isabelle/HOL `Lindemann_Weierstrass`,
   Coq/Rocq, Metamath) of π-transcendence, with a pointer to its proof skeleton — useful
   as a porting template.

**Status of my side:** the rest of the constructible-numbers development is complete and
axiom-clean (full Wantzel equivalence `isConstructible_iff_constructiblePoint`, 3 classical
impossibilities + nonagon + heptagon, pentagon positive). Only π-transcendence is left to
make squaring-the-circle unconditional.

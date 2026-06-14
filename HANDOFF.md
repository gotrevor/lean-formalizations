# HANDOFF — lean-formalizations (umbrella; impossibility / no-formula meta-theorems)

> ✅ **OPERATOR-SCOPED BOUNDED RUN — COMPLETE (2026-06-14, Trevor via Ren).** The four
> verification cross-checks in `DIRECTION.md` are now ALL built, green, sorry-free and
> axiom-clean (commits `ea89147`, `0498df8`). The prior lap (`5f56063`) had only rewritten
> the work-order; this lap actually built items 1–4 plus every optional stretch part. Per
> `DIRECTION.md`'s completion exit the run self-stops here (sentinel written).
>
> **Parked for a FUTURE, separately-scoped run (Trevor's call — do NOT auto-start):**
> constructible-numbers / doubling-the-cube impossibility (P1), mathlib upstream (P2),
> "not algebraic" full theorem (P3). See `PENDING_WORK.md`. Curtis 1990 is DONE — do not
> reopen or extend it.

## ✅ Verification hardening — what got built this lap
- `Curtis/Boundary.lean` (NEW, axiom-clean):
  - `n2_polynomial_relation_exists` (item 1) — n=2 analogue is TRUE; Sylvester's
    `X0*X1 - X0 - X1 - Y` vanishes on the whole 2-generator graph (via `frobeniusNumber_pair`
    + `IsGreatest` uniqueness). Content sits exactly on the n=2/n=3 line.
  - `symmetric_guess_not_a_formula` (item 3, worked) — symmetric degree-2 guess = 83 ≠ 5 at ⟨3,7,8⟩.
  - `no_single_polynomial_formula` (item 3, stretch) — every single candidate is refuted by
    some admissible triple (k=1 case of `no_finite_polynomial_formula`).
- `Curtis/Anchors.lean` (extended, axiom-clean): three new Lemma-2 anchors ⟨3,7,11⟩=8,
  ⟨3,13,14⟩=11, ⟨5,11,23⟩=29 (last uses k=3); ⟨3,7,11⟩ also proved directly; plus stretch
  `frobeniusNumber_6_9_20` (McNugget 43, outside Curtis's family, no `native_decide`).
- `Curtis/FINDINGS.md` (NEW, item 4) — not-algebraic / sub-families-have-formulas write-up.
- Fixed stale "currently sorry" docstrings in `Curtis/Engine.lean` + `Curtis/README.md`.

## ✅ Curtis 1990 — COMPLETE and axiom-clean (verified)
All public results in `Statement.lean` (+ `Anchors.lean`) are machine-checked and
axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
no custom axioms anywhere):
- `no_polynomial_relation` — Curtis's theorem (Frobenius number of a triple is not
  algebraic over its generators).
- `no_finite_polynomial_formula` (+ `_of_algebra` / `_int` / `_rat`) — no finite menu of
  polynomials (over any ℂ-algebra; in particular ℤ/ℚ) computes the Frobenius number.
- `no_finite_polynomial_formula_multivar (n) (3 ≤ n)` — the n ≥ 3 generalization.
- `Anchors.lean` — faithfulness witnesses (`⟨3,7,8⟩`, Frobenius number `5`, two ways).

Paper: `papers/Curtis-1990-Frobenius-formula.pdf` (3 pp., fully read).

## 🎯 Items 1–4 (see `DIRECTION.md` for full specs) — ALL DONE incl. every stretch
1. **n = 2 boundary check** — ✅ `Boundary.n2_polynomial_relation_exists`.
2. **More numerical anchors** — ✅ 3 new Lemma-2 anchors (+ direct route on one) + ✅ stretch
   `frobeniusNumber_6_9_20`.
3. **Refute a named candidate formula** — ✅ `symmetric_guess_not_a_formula` + ✅ stretch
   `no_single_polynomial_formula`.
4. **Document the "free findings" + fix stale docstrings** — ✅ `FINDINGS.md`, Engine/README updated.

All headlines + all new checks re-verified axiom-clean (`[propext, Classical.choice, Quot.sound]`,
no `sorryAx`, no `native_decide`/`ofReduceBool`). `lake build` green (only the documented,
to-be-left Lemma2 lint warnings remain).

## File layout
- `Curtis/Defs.lean` — `IsAdmissible`, `evalPoint` (shared; audit these).
- `Curtis/Lemma2.lean` — Curtis's Lemma 2 (Brauer–Shockley), via Aristotle, verified.
- `Curtis/GridVanish.lean` — the grid-vanishing lemma (replaces the limit argument).
- `Curtis/Engine.lean` — the engine: spine, Step A (`substCurve_eq_zero`), Step B.
- `Curtis/Statement.lean` — audit surface; all headline theorems.
- `Curtis/Anchors.lean` — concrete faithfulness witnesses.
- (this run) suggested new: `Curtis/Boundary.lean` (items 1+3); extend `Anchors.lean` (item 2).

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from a real `lake build`).
- Keep `Statement.lean` faithful; engine lives in siblings and delegates.
- `Lemma2.lean` lint warnings: LEAVE THEM (mathematical hypotheses + Aristotle blocks).
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue.

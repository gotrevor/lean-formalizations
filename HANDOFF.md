# HANDOFF — lean-formalizations (umbrella; impossibility / no-formula meta-theorems)

> ⛔ **OPERATOR-SCOPED BOUNDED RUN (2026-06-14, Trevor via Ren).** Read `DIRECTION.md`
> FIRST — it is the authoritative work-order and supersedes all earlier batons (the
> dated `HANDOFF-*` files are archived under `archive/handoff/`).
>
> **This run does ONE thing: build the four verification cross-checks in `DIRECTION.md`,
> then STOP** (`--allow-stop` self-stop on a review/reflect lap). Do **not** start any new
> target — constructible numbers, mathlib upstream, etc. are PARKED in `PENDING_WORK.md`
> and explicitly deferred. Curtis 1990 is DONE; do not reopen or extend it.

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

## 🎯 This run — verification hardening (see `DIRECTION.md` for full specs)
1. **n = 2 boundary check** — exhibit the Sylvester hypersurface; show the theorem's content
   sits exactly at the n=2 / n=3 line. (mandatory)
2. **More numerical anchors** — extra Lemma-2-vs-`FrobeniusNumber` agreements; optional
   g(6,9,20)=43 outside-family check. (mandatory core + optional stretch)
3. **Refute a named candidate formula** — concrete worked refutation at ⟨3,7,8⟩. (mandatory
   worked example + optional general corollary)
4. **Document the "free findings"** (not-algebraic / sub-families-have-formulas) + fix the
   stale "currently sorry" docstrings in `Engine.lean` + `Curtis/README.md`. (mandatory)

**No `sorry` — omit an intractable stretch item rather than leave a hole.** When 1–4 are done
(or honestly omitted) + green + sorry-free, STOP.

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

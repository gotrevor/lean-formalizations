# HANDOFF — lean-formalizations (umbrella; impossibility / no-formula meta-theorems)

> **Thin pointer.** Durable overview → `STATUS.md`. Newest baton →
> `HANDOFF-2026-06-14-1545.md`. Open items / attack plan → `PENDING_WORK.md`.
>
> ✅ **Curtis 1990 is COMPLETE and axiom-clean** — re-verified 2026-06-14 by real
> `#print axioms` on all 7 headlines (pure trust base, no `sorryAx`/custom axioms).
> **Next target chosen:** compass-and-straightedge impossibility (constructible numbers /
> doubling the cube) — absent from mathlib, on-theme. See `PENDING_WORK.md` (top) for the
> Layer-1 attack plan. Do not reopen Curtis.

**Repo purpose.** An umbrella for *solved-but-unformalized* results, with a soft spot
for **no-formula / impossibility** meta-theorems.

## 🎯 Status — Curtis 1990: DONE
All public results in `Statement.lean` (+ `Anchors.lean`) are machine-checked and
axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`, no custom axioms anywhere):
- `no_polynomial_relation` — Curtis's theorem (Frobenius number of a triple is not
  algebraic over its generators).
- `no_finite_polynomial_formula` — the ℂ corollary (no finite list of formulas).
- `no_finite_polynomial_formula_of_algebra` / `_int` / `_rat` — coefficients in any
  ℂ-algebra; in particular **no integer/rational polynomial formula**.
- `no_finite_polynomial_formula_multivar (n) (3 ≤ n)` — the **n ≥ 3** generalization
  (the paper's full title), by reduction to n = 3.
- `Anchors.frobeniusNumber_3_7_8` etc. — faithfulness witnesses.

Paper: `papers/Curtis-1990-Frobenius-formula.pdf` (3 pp., fully read).

## File layout
- `Curtis/Defs.lean` — `IsAdmissible`, `evalPoint` (shared; audit these).
- `Curtis/Lemma2.lean` — Curtis's Lemma 2 (Brauer–Shockley), via Aristotle, verified.
- `Curtis/GridVanish.lean` — the grid-vanishing lemma (replaces the limit argument).
- `Curtis/Engine.lean` — the engine: spine, Step A (`substCurve_eq_zero`), Step B.
- `Curtis/Statement.lean` — audit surface; all headline theorems.
- `Curtis/Anchors.lean` — concrete faithfulness witnesses.

## How the crux closed (the insight)
Curtis's Lemma 1 (Dirichlet + Farey, for a *converging coprime* sequence) and his
projective/limit argument are **unnecessary**: admissibility + Lemma 2 never need
`gcd(x,y)=1`. Fix ONE prime `x ≡ 1 (mod p)`, `x > p(D+1)`; the interval
`((p−k)x,(p−k+1)x)` (length `x`) holds no multiple of `x` and `≥ D+1` residues
`y ≡ p−k+1 (mod p)`. `D+1` such primes give a `(D+1)²` grid of zeros of
`substCurve F p k`; `grid_vanish` (double root-counting + `MvPolynomial.funext`)
forces it to vanish. Details + next targets in `PENDING_WORK.md`.

## Next targets (none blocked; details in PENDING_WORK.md)
1. (Done this lap) ~~n ≥ 3 generalization~~.
2. Upstream to `Mathlib.NumberTheory.FrobeniusNumber` (needs style pass + AI-policy
   check; web-gated — see reference corpus `2026-06-07-mathlib-ai-contribution-policy`).
3. Optional: "Zariski-dense graph" repackaging of `no_polynomial_relation`.

## Aristotle
Nothing genuinely open → idle is correct. The old Lemma-1 job (`80d9166c`) is
OBSOLETE (the proof needs no Lemma 1). Don't feed redundant cross-confirms.

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from real `lake build`).
- Keep `Statement.lean` faithful; engine lives in siblings and delegates.
- `Lemma2.lean` lint warnings: LEAVE THEM (mathematical hypotheses + Aristotle blocks).
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue.

# HANDOFF — lean-formalizations (target: Curtis 1990)

> ⚠️ **READ [`DIRECTION.md`](DIRECTION.md) FIRST** (operator directive 2026-06-14):
> hardest-first. Step A (`substCurve_eq_zero`) is the SOLE gate; spike it and report its
> feasibility honestly each lap; everything else stays `sorryAx` until it closes; park
> with a named gap if it's a wall. Don't dress up scaffolding as a deliverable.

**Repo purpose.** An umbrella for *solved-but-unformalized* results, with a soft spot
for **no-formula / impossibility** meta-theorems. Current target: Curtis 1990, the
no-Frobenius-formula theorem.

## 🎯 THE TARGET — Curtis 1990
Prove, axiom-clean, the two theorems in
`src/LeanFormalizations/NumericalSemigroups/Curtis/Statement.lean` (the **audit
surface**; statements delegate to `Engine.lean`):
- `no_polynomial_relation` — THEOREM: no nonzero `F ∈ ℂ[X₁,X₂,X₃,Y]` vanishes on the
  graph of the Frobenius number over Curtis's admissible family `A`.
- `no_finite_polynomial_formula` — COROLLARY (reduces to the THEOREM; ⚠️ still `sorryAx`
  via Step A — NOT yet a deliverable).

Paper: `papers/Curtis-1990-Frobenius-formula.pdf` (3 pp.), fully read.

## File layout
- `Curtis/Defs.lean` — `IsAdmissible`, `evalPoint` (shared; audit these too).
- `Curtis/Lemma2.lean` — Curtis's Lemma 2 (Brauer–Shockley), PROVED (axiom-clean).
- `Curtis/Engine.lean` — proof engine.
- `Curtis/Statement.lean` — audit surface; the two theorems delegate to Engine.

## State of the engine — ONLY ONE `sorry` LEFT
PROVED, axiom-clean (modulo the single open sorry):
- `no_finite_polynomial_formula_engine` — corollary via `F = ∏(rename castSucc fᵢ − X 3)`.
- `no_polynomial_relation_engine` — **spine + final contradiction** (fixed totalDegree
  can't dominate `(p-1)/2` along Euclid's primes; good-prime selection).
- `finite_specCurve_eq_zero` — bad-prime set finite (finSuccEquiv → roots over a domain).
- `half_le_totalDegree` — **the entire Step B degree-counting finish** (root-counting via
  `finSuccEquiv ∘ rename (finRotate 3)`, distinct `linForm p k`, `card_roots'`).
  Plus reusable helpers `eval_finSuccEquiv_eq_aeval_cons`, `totalDegree_aeval_le`,
  `totalDegree_specCurve_le`, `substCurve_eq_aeval_specCurve`.
- `Curtis.Lemma2.lemma2` — **Curtis's Lemma 2**, via Aristotle, re-verified in our kernel.

THE ONE OPEN `sorry` (in `Engine.lean`):
- `substCurve_eq_zero` (Step A, **deep**): `F` vanishes on graph ⟹ each substituted
  curve is `0`. Needs only **Lemma 1** (Dirichlet+Farey, OUT TO ARISTOTLE) + **the limit
  argument**. Assembly recipe in `PENDING_WORK.md`.

## Aristotle
- Lemma 2 (job `03706c46`) — **DONE, verified, ported** to `Lemma2.lean`.
- Lemma 1 (job `80d9166c-a0af-4717-978b-98bda8c0af50`) — **RUNNING**. Prompt
  `tools/aristotle/curtis-lemma1-prompt.txt`. On return: download, verify in our kernel +
  `#print axioms`, port to a sibling `Lemma1.lean`.

## Next steps (recommended order; details in PENDING_WORK.md)
1. **Harvest Aristotle Lemma 1** (`80d9166c`) when it returns; verify + port.
2. **The limit argument** — independent; build now against the Lemma 1/2 statements.
3. **Assemble `substCurve_eq_zero`** from Lemmas 1+2 + the limit argument → closes the
   last sorry and the whole theorem becomes axiom-clean.

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from real `lake build`).
- Keep `Statement.lean` faithful; engine lives in siblings and delegates.
- Aim axiom-clean; disclosed `axiom`/`sorry` + citing docstring is fine for genuinely-hard
  sub-lemmas — then keep chipping.
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue.

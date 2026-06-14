# HANDOFF — lean-formalizations (target: Curtis 1990)

**Repo purpose.** An umbrella for *solved-but-unformalized* results, with a soft spot
for **no-formula / impossibility** meta-theorems. Current target: Curtis 1990, the
no-Frobenius-formula theorem.

## 🎯 THE TARGET — Curtis 1990
Prove, axiom-clean, the two theorems in
`src/LeanFormalizations/NumericalSemigroups/Curtis/Statement.lean` (the **audit
surface**; statements delegate to `Engine.lean`):
- `no_polynomial_relation` — THEOREM: no nonzero `F ∈ ℂ[X₁,X₂,X₃,Y]` vanishes on the
  graph of the Frobenius number over Curtis's admissible family `A`.
- `no_finite_polynomial_formula` — COROLLARY. ✅ **PROVED** (reduces to the THEOREM).

Paper: `papers/Curtis-1990-Frobenius-formula.pdf` (3 pp.), fully read.

## File layout (restructured this lap)
- `Curtis/Defs.lean` — `IsAdmissible`, `evalPoint` (shared; audit these too).
- `Curtis/Engine.lean` — proof engine.
- `Curtis/Statement.lean` — audit surface; the two theorems delegate to Engine.

## State of the engine (`Engine.lean`)
PROVED (machine-checked):
- `no_finite_polynomial_formula_engine` — corollary via `F = ∏(rename castSucc fᵢ − X 3)`.
- `no_polynomial_relation_engine` — **spine + final contradiction** (fixed totalDegree
  can't dominate `(p-1)/2` along Euclid's primes; good-prime selection from the infinite
  set of primes minus the finite bad set).
- `finite_specCurve_eq_zero` — the bad-prime set is finite (via `finSuccEquiv` →
  univariate over a domain → finitely many roots). **Axiom-clean.**
- `substCurve_eq_aeval_specCurve` — Step-B bridge: substitution = Y-substitution of
  the specialization.

TWO OPEN `sorry`s (both in `Engine.lean`):
1. `half_le_totalDegree` (Step B, **degree-counting finish — TRACTABLE**). All sub-lemmas
   located; only an eval→root bridge + a `totalDegree_aeval_le` remain. See `PENDING_WORK.md`.
2. `substCurve_eq_zero` (Step A, **deep**: Curtis's Lemma 1 (Dirichlet+Farey) + Lemma 2
   (Brauer–Shockley) + a limit argument). Multi-lap. See `PENDING_WORK.md`.

## Aristotle
- Job `03706c46-1ccd-44b2-8b2a-ea4b2dfd9e83` — **Curtis Lemma 2** (Brauer–Shockley value),
  RUNNING. Prompt archived at `tools/aristotle/curtis-lemma2-prompt.txt`. On return:
  `aristotle download <id> --destination x.tar.gz`, verify in our kernel + `#print axioms`,
  then port onto the real `FrobeniusNumber {s₁,s₂,s₃}` def. Then feed Lemma 1 next.

## Next steps (recommended order; details in PENDING_WORK.md)
1. **Finish `half_le_totalDegree`** — purely algebraic, well-scoped.
2. **Harvest Aristotle Lemma 2** when it returns.
3. **Lemma 1** (Farey adjacency + mathlib Dirichlet) and **the limit argument**.

## Standing rules (this repo)
- DO NOT push (host publishes). Commit every green build (verify from real `lake build`).
- Keep `Statement.lean` faithful; engine lives in siblings and delegates.
- Aim axiom-clean; disclosed `axiom`/`sorry` + citing docstring is fine for genuinely-hard
  sub-lemmas — then keep chipping.
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web? Append a dated item to `ON-LINE-REQUEST.md` and continue.

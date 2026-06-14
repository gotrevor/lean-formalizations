# Curtis 1990 — no closed formula for the Frobenius number (n ≥ 3)

> Frank Curtis, *On formulas for the Frobenius number of a numerical semigroup*,
> Math. Scand. **67** (1990), 190–192. [DOI](https://doi.org/10.7146/math.scand.a-12330)
> · open-access [PDF](https://www.mscand.dk/article/download/12330/10346)

## Status
- **COMPLETE and axiom-clean.** All headline results in `Statement.lean` are
  machine-checked (`#print axioms` = `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`, no custom axioms): `no_polynomial_relation` (the main theorem),
  `no_finite_polynomial_formula` (+ `_of_algebra` / `_int` / `_rat`), and
  `no_finite_polynomial_formula_multivar` (the `n ≥ 3` generalization).
- Faithfulness anchors in `Anchors.lean` (six concrete triples) and boundary /
  refutation cross-checks in `Boundary.lean`. See `FINDINGS.md` for the two
  consequences the proof gives for free (not-algebraic; sub-families still have
  formulas). Proof internals live in `Engine.lean` (+ `Lemma2.lean`,
  `GridVanish.lean`); the elementary grid-vanishing argument replaces Curtis's
  Dirichlet/Farey limit argument.

## What to audit (the entire trust surface)
Read **`Statement.lean`** against the paper. Two theorems + two small defs:

- `IsAdmissible s₁ s₂ s₃` — Curtis's set `A`: `s₁ < s₂ < s₃`, `s₁` and `s₂`
  prime, `s₁ ∤ s₃`, `s₂ ∤ s₃`. (Paper, the `THEOREM` statement, p. 190.)
- `no_polynomial_relation` — the `THEOREM`: no nonzero `F ∈ ℂ[X₁,X₂,X₃,Y]` with
  `F(s₁,s₂,s₃, g⟨s₁,s₂,s₃⟩) = 0` on all of `A`.
- `no_finite_polynomial_formula` — the `COROLLARY`: no finite menu of polynomials
  computes `g` piecewise.
- `FrobeniusNumber` is **mathlib's** (`Mathlib.NumberTheory.FrobeniusNumber`):
  `IsGreatest {k | k ∉ AddSubmonoid.closure s} n`. Uniqueness of the Frobenius
  number is why quantifying `∀ g, FrobeniusNumber g {…} → …` is faithful.

Everything else (proof internals, once written) is out of scope for faithfulness.

## Why this is a real gap (searched 2026-06-14)
Not in mathlib (only the 2-var `frobeniusNumber_pair`), not in
`google-deepmind/formal-conjectures`, not in the Lean Zulip ITC corpus, not in
FineLeanCorpus (509k pairs — only concrete instances + the 2-var formula), and no
Reservoir package. Closest neighbor: `AxiomMath/FelConjecture` (numerical-
semigroup *syzygies*, a different result). First known formalization of Curtis.

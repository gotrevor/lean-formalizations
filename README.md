# LeanFormalizations

Formalizations of **solved-but-unformalized** mathematical results in Lean 4 +
mathlib — with a soft spot for *no-formula / impossibility* meta-theorems (the
genre where you reify a class of formulas and prove the target escapes it).

**Status:** local, unpublished. Not pushed, not registered, not announced.

## Contents

| Area | Result | Status |
|------|--------|--------|
| `NumericalSemigroups/Curtis` | Curtis 1990: the Frobenius number of a triple has no closed formula (and isn't even algebraic over the generators); incl. the ℤ/ℚ corollaries. | **PROVED, axiom-clean** |
| `RealAnalysis/PowerTower` | Euler 1783: the infinite power tower `ⁿx` converges iff `x ∈ [e^(-e), e^(1/e)]`. Upper half (`x ≥ 1`, sharp endpoint `e^(1/e)`) scaffolded. | **Scaffold** (`iff` proved; convergence/divergence `sorry`) |

Planned: gather the Erdős formalizations here once their publishing gate clears
(they're separate repos today: `erdos-403`, `erdos-482`, `erdos-1213`, …).

## Layout
- `src/LeanFormalizations/<Area>/<Result>/Statement.lean` — the **designated
  audit surface**: the load-bearing statement(s), written to be checked against
  the source. Proof engine lives in sibling files.
- `<Result>/README.md` — "what to audit" + provenance + status.
- `papers/` — source PDFs (gitignored; summaries/provenance committed). See
  `SOURCES.md`.

## Build
```sh
lake exe cache get      # fetch prebuilt mathlib oleans (do this first)
lake build              # non-vacuous: defaultTargets = ["LeanFormalizations"]
```
After the first successful build, enable the green-gate:
`git config core.hooksPath .githooks` (see `.githooks/README.md`).

## Prior art / neighbors in the Lean ecosystem
- mathlib `Mathlib.NumberTheory.FrobeniusNumber` — the general def + the 2-var
  Chicken McNugget theorem `frobeniusNumber_pair`. Curtis explains why it stops
  at n = 2. Curtis's natural long-term home is a PR extending that file.
- `AxiomMath/FelConjecture` (github.com/AxiomMath/fel-polynomial) — active
  numerical-semigroup formalization (Fel's syzygy conjecture, arXiv:2602.03716).

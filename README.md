# LeanFormalizations

Formalizations of **solved-but-unformalized** mathematical results in Lean 4 +
mathlib — with a soft spot for *no-formula / impossibility* meta-theorems (the
genre where you reify a class of formulas and prove the target escapes it).

**Status:** local, unpublished. Not pushed, not registered, not announced.

## Contents

| Area | Result | Status |
|------|--------|--------|
| `NumericalSemigroups/Curtis` | Curtis 1990: the Frobenius number of a triple has no closed formula (and isn't even algebraic over the generators); incl. the ℤ/ℚ corollaries. | **PROVED, axiom-clean** |
| `RealAnalysis/PowerTower` | Euler 1783: the infinite power tower `ⁿx` converges iff `x ∈ [e^(-e), e^(1/e)]`. Both halves proved — upper (`x ≥ 1`, monotone) and lower (`e^(-e) ≤ x < 1`, oscillating; crux = no 2-cycle for `x ≥ e^(-e)`, via the slope bound `g' ≤ \|log x\|/e ≤ 1`). | **PROVED, axiom-clean** — headline `tower_converges_of_mem` (convergence on the full `[e^(-e), e^(1/e)]`) + lower-bound crux fully discharged (no axiom). Sharp `iff` divergence half (`x < e^(-e)`) omitted. |
| `Geometry/Constructible` | Wantzel 1837: the three classical compass-and-straightedge impossibilities — doubling the cube (`∛2`), trisecting the 60° angle (`cos 20°`), squaring the circle (`√π`, conditional on `π` transcendental). One engine: a constructible real has degree `2ⁿ` over `ℚ`. Constructibles shown to form a subfield closed under `√`. | **PROVED, axiom-clean** (Layer 1, algebraic core) — `cbrt2_not_constructible`, `cos20_not_constructible`, `squaring_the_circle_impossible`. Geometric faithfulness (Layer 2) open. |

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

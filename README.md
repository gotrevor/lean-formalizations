# LeanFormalizations

Formalizations of **solved-but-unformalized** mathematical results in Lean 4 +
mathlib — with a soft spot for *no-formula / impossibility* meta-theorems (the
genre where you reify a class of formulas and prove the target escapes it).

**Status:** public. Build green; `src/` is `sorry`-free; per-headline `#print axioms`
footprints are in [`STATUS.md`](STATUS.md).

**Checking this repo without trusting it:** the transcendence headlines carry a
[`comparator`](https://github.com/leanprover/comparator) harness - read
[`Comparator/Transcendence/Challenge.lean`](Comparator/Transcendence/Challenge.lean)
(imports only Mathlib; the entire audit surface), and CI replays the proofs through the
Lean kernel and the independent `nanoda` kernel under an axiom whitelist
([workflow](.github/workflows/comparator.yml)). Provenance, AI methods and cost:
[`formalization.yaml`](formalization.yaml).

> **How this was built.** Most of the Lean here, and most of these docs, were written by
> Claude working in long autonomous sessions against a `lake build` + `#print axioms` gate;
> two symmetric-function lemmas came from Harmonic's Aristotle and were re-verified in this
> repo's kernel (`tools/aristotle/` keeps the prompts). I reviewed and directed the work, but
> I did not hand-write most of it. `git log` shows the co-authorship. Everything is
> machine-checked, so judge it by the kernel and not by me - and see
> [`archive/README.md`](archive/README.md) for the unedited session log, warts included.

## Contents

| Area | Result | Status |
|------|--------|--------|
| `NumericalSemigroups/Curtis` | Curtis 1990: the Frobenius number of a triple has no closed formula (and isn't even algebraic over the generators); incl. the ℤ/ℚ corollaries. | **PROVED, axiom-clean** |
| `Combinatorics/NoThreeInLine` | Ben Green's open problem 72: max points on an `N×N` grid with no three collinear. `2N` upper bound (pigeonhole), Erdős `Θ(N)` parabola lower bound (mod-`p` determinant), order `Θ(N)`. HJSW `3N/2`: two independent constructions (pinwheel + sheared hyperbola), lifted to all `N` via the PNT prime gap. | **PROVED, axiom-clean** - `2N` upper + Erdős lower; HJSW `3(p−1)` pinwheel `three_mul_pred_le_maxNoThreeInLine`; the all-`N` `(3/2−ε)N` frontier `maxNoThreeInLine_ge_three_halves_sub`. |
| `RealAnalysis/PowerTower` | Euler 1783: the infinite power tower `ⁿx` converges **iff** `x ∈ [e^(-e), e^(1/e)]` — the SHARP iff, both endpoints. Convergence via the no-2-cycle crux for `x ≥ e^(-e)` (slope bound `g' ≤ \|log x\|/e ≤ 1`); the `x < e^(-e)` divergence via a *genuine attracting 2-cycle* (`y` repelling, `g'(y) = (log y)² > 1`). | **PROVED, axiom-clean** — sharp headline `tower_converges_iff_full` (`x>0` converges iff `x ∈ [e^(-e), e^(1/e)]`); both cruxes discharged (`two_cycle_collapse`, `strict_two_cycle_exists`), no axiom. |
| `Geometry/Constructible` | Wantzel 1837: the three classical compass-and-straightedge impossibilities — doubling the cube (`∛2`), trisecting the 60° angle (`cos 20°`), squaring the circle (`√π`, **unconditional** - `π`-transcendence is proved in-repo, see the next row). One engine: a constructible real has degree `2ⁿ` over `ℚ`. Constructibles shown to form a subfield closed under `√`. | **PROVED, axiom-clean** (Layer 1, algebraic core) — `cbrt2_not_constructible`, `cos20_not_constructible`, `squaring_the_circle_impossible_uncond`. Geometric faithfulness (Layer 2) open. |
| `NumberTheory/Transcendence` | Hermite 1873 / Lindemann 1882: `e` and `π` are transcendental over `ℚ`. The full Lindemann assembly built on mathlib's `exp_polynomial_approx`: the analytic engine generalised to an arbitrary conjugate polynomial, plus the algebraic half (symmetric functions over the Galois conjugates of `iπ`, via the fundamental theorem of symmetric polynomials). Makes squaring-the-circle unconditional. | **PROVED, axiom-clean** - `transcendental_pi_axiomClean`, `e_transcendental`; **externally checkable** via the comparator harness (`Comparator/Transcendence/`, see above). |
| `Logic/Goodstein` | Goodstein 1944: every Goodstein sequence terminates (`∀ m, ∃ N, goodsteinSeq m N = 0`). Faithful hereditary-base bump (`Nat.log`/div/mod peeling), interpreted into ordinals (`base ↦ ω`). Descent engine: strict monotonicity + CNF leading bound of `toOrdinal` (one combined induction), base-bump invariance (`toOrdinal (b+1) (bump b n) = toOrdinal b n`), so `seqOrd` strictly decreases ⟹ well-foundedness of `<` on `Ordinal` forces `0`. | **PROVED, axiom-clean** — `goodstein_terminates`, anchors `m=0..3` pinned by `native_decide`. (Kirby–Paris PA-independence is out of scope.) |

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

## Prior art / neighbors in the Lean ecosystem
- mathlib `Mathlib.NumberTheory.FrobeniusNumber` — the general def + the 2-var
  Chicken McNugget theorem `frobeniusNumber_pair`. Curtis explains why it stops
  at n = 2. Curtis's natural long-term home is a PR extending that file.
- `AxiomMath/FelConjecture` (github.com/AxiomMath/fel-polynomial) — active
  numerical-semigroup formalization (Fel's syzygy conjecture, arXiv:2602.03716).

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris

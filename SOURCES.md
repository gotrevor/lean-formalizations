# Sources

Source papers live in `papers/` locally (PDFs gitignored — this repo is
eventually-public, so we commit citations + summaries, not copyrighted binaries).

## NumericalSemigroups/Curtis
- **Frank Curtis**, *On formulas for the Frobenius number of a numerical
  semigroup*, **Math. Scand. 67** (1990), no. 2, 190–192.
- DOI: https://doi.org/10.7146/math.scand.a-12330
- Open-access PDF: https://www.mscand.dk/article/download/12330/10346
- JSTOR (paywalled): https://www.jstor.org/stable/24492663
- Local file: `papers/Curtis-1990-Frobenius-formula.pdf` (3 pp.)
- Result: for numerical semigroups with ≥ 3 generators there is no closed
  polynomial formula for the Frobenius number; stronger, the Frobenius number of
  a triple is not algebraic over its generators. Contrast Sylvester's 2-generator
  `g(a,b) = ab − a − b`.
- Proof tools: Dirichlet primes in AP + Farey sequences (Lemma 1); Brauer–Shockley
  Apéry-set formula (Lemma 2); polynomial degree / root-counting (finish).
- Related video (popular framing of the 3-generator case): Michael Penn, "why you
  can't order 43 nuggets" — `g(6,9,20) = 43`.

## Combinatorics/NoThreeInLine
- The no-three-in-line problem (Dudeney 1917); **Ben Green, *Open Problems*, problem 72**
  (https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf).
- Wikipedia: https://en.wikipedia.org/wiki/No-three-in-line_problem
- Erdős's `Θ(n)` parabola construction (via K. F. Roth, *On a problem of Heilbronn*, J.
  London Math. Soc. **26** (1951) 198–204); the `3n/2` improvement: R. R. Hall, T. H.
  Jackson, A. Sudbery, K. Wild, *Some advances in the no-three-in-line problem*, J. Combin.
  Theory Ser. A **18** (1975) 336–341.
- Asymptotic heuristic `≈ 1.814 n`: Guy–Kelly (1968), corrected by G. Ellmann (2004).
- Not formalized elsewhere (Reservoir mirror, 2026-06-18); only the all-`sorry`
  `formal-conjectures` `Green72` stub exists. No PDF committed (results are textbook/classical).

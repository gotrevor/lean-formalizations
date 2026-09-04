# Three proof paths for Catalan's constant after Sun v1

**Research note, 2026-09-04.**  This is a paths-before-roads document.  It does not claim that
Catalan's constant is irrational.  It records three constructions worth probing after the exact
integerizer killed Sun's weights.  No Lean work belongs here until a probe finds a viable ledger.

## 1. Mixed-motive forms and weighted lattice optimization

Eskandari, Murty, and Nemoto, arXiv:2510.20648, construct a two-dimensional motive whose relevant
periods are exactly `1` and `G`.  For suitable `sigma`-invariant polynomials,

```text
I(F,t) = integral_Delta F(x,y)/(1-x^2-y^2)^(t+1) dxdy = a(F,t) + b(F,t) G,
```

with explicit rational `a(F,t)` and `b(F,t)`.  This avoids unwanted periods and supplies a direct
irrationality criterion: find positive forms with exact common denominator `D(F,t)` such that
`D(F,t) I(F,t) -> 0`.

The companion `catalan-motive-probe.py` implements the paper's exact formulas for two monomial
families.  It reproduces all three published examples.  In particular,

```text
384 * integral_Delta x^4 y^4/(1-x^2-y^2)^3 dxdy = -49 + 54G = 0.462142... .
```

This isolated success does not iterate.  For

```text
I_n = integral_Delta x^(4n)y^(4n)/(1-x^2-y^2)^(2n+1) dxdy,
```

the minimally cleared values for `n=1..5` are approximately
`0.4621, 79.45, 7512, 44201, 5.14e9`.  The monomial ray is refuted.

The live experiment is to build the exact coefficient map `(F,t) -> (a,b)` on the full invariant
monomial basis, then LLL-reduce the coefficient lattice with an archimedean evaluation row.  Scan
the entire degree/pole-order triangle.  Certify nonvanishing independently with orbit-sums of
squares or another positive cone.  The exact coefficient lattice matters: the paper's uniform
degree-only lcm bound throws away precisely the special-family savings an irrationality proof needs.

## 2. Specialized recurrence rigidity

Zudilin's explicit second-order recurrence has rational solutions `u_n`, `v_n` and remainder
`r_n = u_n G - v_n`, with Perron roots

```text
((1-sqrt(5))/2)^5 and ((1+sqrt(5))/2)^5.
```

If `G` were rational, `u_n` and `r_n` would be a rational Perron basis with geometrically growing
common denominators.  Zudilin conjectured that such a basis forces both characteristic roots to be
rational.  Proving that rigidity statement for this one recurrence would immediately prove
`G` irrational.

The direct integer-form criterion cannot do this: the remainder decays with exponent `2.406n`,
while the expected clearance `16^n lcm(1,...,2n)^2` costs about `6.773n`.  The point of the route is
to use arithmetic holonomy instead.  Calegari-Dimitrov-Tang showed that holonomy can prove
irrationality even when explicit approximants miss their elementary inequality.  Their current
numeric criterion explicitly misses both known Catalan families, so the target is a new
conductor-4 symmetry or descent over `Q(i)` in this particular differential module, not a routine
application of their theorem.

## 3. Denominator-first hypergeometric or finite-difference search

The closest old quantitative family is Zagier's case E, as summarized in CDT Remark 11.1.17.  It
has denominator type `lcm(1,...,n)^2` and analytic gain `4^n`, leaving an exponential deficit
`2-log(4) = 0.6137...` per step.  This is much closer than the classical Zudilin family.

Search the full half-integral Rivoal-Zudilin parameter cone.  Use its 120-element transformation
group to compute exact prime-by-prime denominator savings, and optimize those against the Laplace
maximum of the double integral.  Test candidates with exact finite-`n` integers before trusting an
asymptotic ledger.

A Sun-style reconstruction can use integer-valued Newton bases or p-orderings, but termwise
denominator covering must not be required.  Uniformly rescaling Sun's weights is neutralized by the
exact integerizer.  The needed saving must arise after the completed sum or determinant through
index-dependent p-adic cancellation.

## Architectural consequence for Phase 3

W and D remain reusable.  E should eventually generalize from a termwise "covering weight family"
to an **integrality certificate for the completed linear form**.  Termwise covering is one
constructor, but the interface should also admit hypergeometric transformations, cohomological pole
reduction, and p-adic lattice saturation.  This is a future scaffold change, not permission to
change the active `Frame.lean` declarations.

## Primary references

- Zhi-Wei Sun, arXiv:2609.04176v1.
- P. Eskandari, V. K. Murty, Y. Nemoto, arXiv:2510.20648.
- F. Calegari, V. Dimitrov, Y. Tang, arXiv:2408.15403, especially Remark 11.1.17.
- W. Zudilin, arXiv:math/0201024 and arXiv:math/0210423.
- C. Krattenthaler, T. Rivoal, arXiv:0810.1927.

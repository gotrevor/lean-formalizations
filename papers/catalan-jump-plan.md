# Catalan irrationality: the bridge plan

**Research note, 2026-09-04.**  This note deliberately looks between established constructions.
It makes no claim that `G` is known irrational.  The target is an executable program with exact
kill criteria, not a confidence estimate about solving the open problem.

## Core diagnosis

The existing approaches each own one necessary resource:

- Eskandari-Murty-Nemoto (EMN) own a two-period motive and positive real integrals in `1,G`.
- Calegari owns exceptional conductor-4 Frobenius overconvergence and an exact Apéry-like
  recurrence for the 2-adic beta value.
- Rivoal-Zudilin own global hypergeometric symmetry and prime-by-prime denominator accounting.
- Moment theory owns automatic nonvanishing through positivity and Vandermonde determinants.

The next construction should combine resources across those boundaries.  Re-optimizing any one
family in isolation is much less likely to change the ledger.

## Jump 1: Frobenius-saturated EMN lattice

This is the best plan.

EMN's motive becomes an extension of `Q(-2)` by `Q(0)` over `Q(i)`.  Calegari's 2-adic Catalan
constant occurs as the constant term of the conductor-4 negative-weight Eisenstein family and is
distinguished by overconvergence on `X_1(4)`.  The proposed bridge is to identify the two as
realizations of the same conductor-4 extension class, then transport the integral or crystalline
lattice back to EMN's explicit de Rham basis.

That changes the Path-1 computation.  Do not merely LLL-reduce every sigma-invariant polynomial.
For each `(N,t)`:

1. Compute the exact EMN map `F -> (a(F,t),b(F,t))`.
2. Compute Frobenius matrices at `2` and several split and inert odd primes in the same basis.
3. Derive congruence conditions on coefficients of `F` that force extra local divisibility of
   `(a,b)`.  These define a finite-index Frobenius-saturated sublattice `L_(N,t)`.
4. Intersect `L_(N,t)` with the orbit-sum-of-squares cone, then run the weighted shortest-vector
   search there.
5. Score the actual object by
   `log |I(F,t)| + sum_p max(0,-min(v_p(a),v_p(b)))`, never by a uniform lcm bound.

The proof closes if the score tends to `-infinity` along positive nonzero forms.  The experiment is
killed if local saturation produces only `o(N)` savings while the real-place deficit is linear, or
only `o(N^2)` savings against a quadratic deficit, throughout an expanding exact scan.

Why this is a jump: “special sublattices may help” becomes a source-driven prediction.  Frobenius
selects the sublattices; LLL only finds short positive vectors inside them.

### First local Smith measurement

`catalan-emn-smith-profile.py` measures a deliberately weaker proxy before Frobenius has been
identified.  On the full lattice of sigma-invariant integer polynomials it clears the exact EMN
map to an integer `2 x d` matrix, computes its two Smith valuations prime by prime, and obtains the
exact index of the coefficient sublattice on which both output coordinates are divisible by the
common denominator.

The result is encouraging rather than dispositive.  At `(N,t)=(20,0)`, `d=86`,
`log10(D)=14.779`, and `log10(index)=15.080`, so the full-clearance lattice has index about
`D^1.020`.  Along the higher-pole ray `t=N/4`, the measured `log10(index)/d` falls as follows:

```text
(N,t,d)       log10(index)/d
(16,4,17)          0.448
(24,6,34)          0.360
(32,8,57)          0.318
```

At `(32,8)`, `log10(D)=15.405` and `log10(index)=18.114`, an index of about `D^1.176`.  Thus the
observable local saturation does not have an index exponential in the ambient quadratic dimension;
its geometry-of-numbers penalty per dimension is declining on the tested ray.

This does **not** yet validate Frobenius saturation.  It measures the unrestricted linear `F`
lattice, whereas positivity is currently imposed by the nonlinear parameterization
`F=orbit_sum(h^2)`.  The next decisive proxy is to solve the Smith congruences while retaining a
positive certificate.  Failure of that intersection can still kill the jump.

### Positive-cone intersection measurement

`catalan-emn-positive-saturation.py` tests that nonlinear intersection directly by sampling small
ternary coefficient vectors for `h`, evaluating the two exact quadratic congruences, and measuring
the real integral of the certified-positive form `F=orbit_sum(h^2)`.

The first measurements are positive:

```text
(N,t,p)    delta   trials      full hits   observed density exponent
(16,4,2)     13    1,000,000       26              15.23
(20,4,2)     16   20,000,000       58              18.40
(24,6,2)     19   20,000,000        2              23.25
```

Two independent random quadrics would predict exponents `2*delta`, namely `26,32,38`.  The positive
EMN quadrics are therefore much more dependent modulo powers of two than a generic pair.  The larger
`(20,4)` run replaced an unreliable two-hit density estimate.  Its excess exponent
`18.40-16=2.40` agrees closely with the `(16,4)` excess `15.23-13=2.23`; there is no observed drift
toward the generic exponent `2*delta` between those adequately sampled points.  The best `(20,4)`
hit has

```text
a = -380596/51975,  b = 8,  a+bG = 0.00505039074339... .
```

Relative to the best positive form in the same sample, it pays a real factor `22.3` while removing
the complete `2^16` denominator contribution, a net local improvement of about `2938`.

At `(24,6)`, the best fully `2^19`-saturated hit has

```text
a = -12962/4725,  b = 3,  a+bG = 0.00461635925123... .
```

It pays a sampled real factor `113.9` for a local clearance gain `2^19`, a net improvement of about
`4600`.  At the odd primes `3,5,7`, the observed full-saturation densities are approximately
`p^(-delta)`, rather than `p^(-2 delta)`, with sampled real penalties only `2.60,2.41,1.91`.

The last denominator prime at `(24,6)`, `p=11`, has observed exponent `1.17` for `delta=1` and a
sampled real penalty `2.19`.  Multiplying the five separately measured local penalties gives the
screening estimate

```text
log10(D*I_baseline)                  =  6.043
- total available denominator gain  = -10.435
+ sum log10(local real penalties)    =  3.476
screening ledger                     = -0.916
```

This clears the cheap pre-CRT screen by just under one decimal order.  It is not a construction:
local minimizing vectors differ, so multiplying marginal penalties assumes compatibility that must
be tested by the simultaneous solver.

This resolves the first objection: the saturation conditions do intersect the positive
orbit-square cone cheaply at each tested prime.  It does not yet produce a globally integral small
form.  The next exact problem is simultaneous modular quadratic optimization across all primes of
`D`; independent random sampling would be wasteful, so it needs Hensel/CRT construction followed by
a small-representative or lattice reduction step.

## Jump 2: modular-unit Padé basis on `X_1(4)`

Calegari writes the 2-adic Catalan construction in the genus-zero coordinate

```text
z = (Delta(4 tau)/Delta(tau))^(1/3),
```

with a special linear combination `A(z)-eta B(z)`.  Its coefficients satisfy

```text
(n+1)^2 u_(n+1) = (4-32n^2)u_n - 256(n-1)^2u_(n-1).
```

At the real place the limiting characteristic polynomial is `(lambda+16)^2`.  The repeated root
explains why the raw coefficient ratio has no exponential separation: the natural Hauptmodul basis
is arithmetically excellent 2-adically but analytically degenerate over `R`.

Search instead over modular units with divisors supported on the three cusps of `X_1(4)`, and over
Faber or multipoint Padé bases rather than powers of one Hauptmodul.  The desired basis must make
the classical Eichler combination containing `G` analytic across one cusp while a generic rational
combination still sees that cusp.  The divisor lattice is rank two, so bounded searches are finite.

For each modular unit or multipoint basis compute exactly:

- the nearest surviving complex singularity for the special and generic combinations;
- the Eisenstein denominator of its rational coefficients;
- the resulting radius ratio divided by coefficient-height growth.

The proof closes when that ratio exceeds one in Beukers' irrationality criterion.  Kill the branch
if the optimized divisor problem proves the radius gain is always paid back by the modular unit's
height.  This is a sharper, finite version of “prove recurrence rigidity.”

## Jump 3: rank-one positive moment determinants

There is a direct positive moment identity

```text
mu_n = integral_0^1 x^(2n)(-log x)/(1+x^2) dx
     = (-1)^n (G - sum_(j<n) (-1)^j/(2j+1)^2).
```

Hence the Hankel determinant

```text
H_m = det(mu_(i+j))_(0 <= i,j < m)
```

is strictly positive, and is still only `A_m+B_m G`: the matrix of `G` coefficients is the rank-one
matrix `((-1)^(i+j))`.  Andreief rewrites `H_m` as a positive multiple integral with a squared
Vandermonde.  Nonvanishing is therefore free.

The companion `catalan-hankel-probe.py` computes the exact ledger.  The unmodified family fails:
at `m=18`, `log10 H_m` is about `-194.70`, but `log10 D_m` is about `672.37`.  Scanning shifted
moment windows through `0 <= s <= 3m` chooses `s=0` for every `m >= 2`, so monomial shifts are also
killed.

The surviving version is multiple orthogonality.  Replace the monomial rows by Type-I/Type-II
Hermite-Padé forms for the two measures

```text
t^(-1/2) dt/(1+t),       t^(-1/2)(-log t) dt/(1+t).
```

The first measure supplies explicit half-integral Jacobi arithmetic; differentiating its parameter
supplies the logarithmic measure and `G`.  Search multi-indices and Christoffel transforms for which
the determinant remains rank one in `G`, the error remains a positive multiple integral, and the
Jacobi factorials cancel the odd-square lcm.  This is close to Rivoal's Padé construction, so every
candidate must be compared against his 2006 formulas.  The new ingredient is the rank-one positive
determinant and exact reduced denominator, not Padé approximation alone.

Kill the branch if the reduced ledger retains a positive quadratic coefficient for all rational
multi-index rays.

## Execution order

1. Finish the existing exact EMN evaluator and ordinary positive-cone scan as a baseline.
2. Identify the EMN extension with the level-4 Eisenstein/polylogarithm class and compute one local
   Frobenius matrix.  A single prime showing linear-in-degree saturation justifies the full search.
3. In parallel mathematically, derive the classical level-4 Eichler combination and enumerate the
   small cusp-divisor lattice.  This needs no Lean and little large computation.
4. Keep the moment determinant as a controlled third probe; its naive rays are already eliminated.

## Primary sources

- P. Eskandari, V. K. Murty, Y. Nemoto, arXiv:2510.20648.
- F. Calegari, *Irrationality of Certain p-adic Periods for Small p*, IMRN 2005, 1235-1249.
- T. Rivoal, *Nombres d'Euler, approximants de Padé et constante de Catalan*, Ramanujan J. 11
  (2006), 199-214.
- T. Rivoal, W. Zudilin, *Diophantine properties of numbers related to Catalan's constant*, Math.
  Ann. 326 (2003), 705-721.

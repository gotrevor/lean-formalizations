# Probe result: the rank-one positive Hankel family is dead by a capacity-vs-lcm inequality

**2026-09-04.**  Probe: `catalan-hankel-sublattice.py`.  Verdict: **refuted structurally**, not just
numerically.  This closes codex's Jump 3 (`catalan-jump-plan.md`) in its "search bases /
Christoffel / multiple orthogonality" form.

## What is genuinely good about this family

With `μ_n = ∫_0^1 x^{2n}(-log x)/(1+x²) dx = (-1)^n (G - Σ_{j<n} (-1)^j/(2j+1)²)`, the Hankel
matrix `M = (μ_{i+j})` is a Gram matrix of a positive measure, so `H_m = det M > 0`:
**nonvanishing is free.**  That is exactly the property `catalan-annihilation-margin.md` says a
route to `G` needs — smallness that does not come from multi-term cancellation.  And the `G`-part
of `M` is `u uᵀ` with `u_k = (-1)^k`, rank one, so `H_m = A_m + B_m G` is a linear form in `G`
**alone**.  Both properties are robust: they survive every transformation below.

## Three freedoms, all closed

**1. Basis change is provably vacuous.**  For an integer basis `p_i = Σ_k U_{ik} t^k`,
`Gram = U M Uᵀ`, so `det Gram = det(U)² · H_m`.  A unimodular `U` changes nothing at all.  The
`G`-part stays rank one for every `U` (it is `(Uu)(Uu)ᵀ`).  So "search over polynomial bases" is not
a search; the only content is the *lattice*, through `det(U)²` and through the entry denominators.

**2. The lattice buys a constant fraction, not an exponent.**  Measured ledger
`log₁₀(D·|H|)` with `D` the exact reduced clearance of `A_m + B_m G`:

| m | monomial | falling factorial | gain | gain / baseline |
|---|---|---|---|---|
| 4 | 8.59 | 7.38 | 1.21 | 14.1% |
| 6 | 34.11 | 29.30 | 4.81 | 14.1% |
| 8 | 73.02 | 63.39 | 9.63 | 13.2% |
| 10 | 123.95 | 105.88 | 18.07 | 14.6% |
| 12 | 185.13 | 157.44 | 27.69 | 15.0% |

Falling factorials (`= binomial basis`, the integer-valued-polynomial superlattice, `det U = 1/∏k!`)
are the *optimum* in this direction: they divide by exactly as much as integrality absorbs.
Sublattices go the wrong way — shifted Legendre (`det U = ∏C(2k,k)`, the Beukers/Apéry choice) is
**worse** than the baseline at every `m` (80.24 vs 73.02 at `m=8`), because the numerator pays
`2 log|det U|` while the denominator saves less.  The Apéry denominator trick buys a constant
percentage here, and 15% does not close a gap of 185.

**3. Christoffel transforms are strictly harmful.**  Multiplying the measure by `w(t) = t^a(1-t)^b`
(`≥ 0` on `[0,1]`, so positivity survives; `G`-part still rank one, coefficient `w(-1)`) is the one
family the `det(U M Uᵀ)` identity does *not* cover.  Every one tested is worse, monotonically in
`deg w` — at `m=10`: baseline 123.95, `(1-t)` 139.34, `(1-t)²` 151.50, `(1-t)⁴` 180.58.  Reason: a
weight of degree `d` shrinks the moments by `O(1)` but pushes the largest moment index the
determinant reaches from `2m-2` to `2m-2+d`, and the clearance is driven by that index.

## The obstruction, in closed form

Both rates are computable and neither has a free parameter:

* **Numerator.**  `H_m` is a Hankel determinant of a measure supported on `[0,1]`, so
  `H_m^{1/m²} → cap([0,1]) = 1/4`, i.e. `log|H_m| ~ -(log 4)·m² = -1.386 m²`.
  Measured: `log₁₀|H_12|/144 = 0.598`, times `ln 10` = `1.377`.  ✅
* **Denominator.**  An `m × m` determinant necessarily reaches moment index `2m-2`, whose
  denominator is `lcm{(2j+1)² : j < 2m-2} ≈ e^{4m}`; clearing a determinant costs that to the
  `m`-th power, `≈ e^{4m²}`.  Measured `log₁₀ D_12/144 = 1.88`, times `ln 10` = `4.34` (the lcm
  asymptotic converges slowly from above).  ✅

So the ledger rate is `4 - log 4 = 2.61 > 0`, and **no choice of basis, lattice or positive weight
moves either constant**: the numerator rate is fixed by the logarithmic capacity of the support and
the denominator rate by the size of the matrix.  To close, one would need a measure supported on a
set of capacity `< e^{-4} ≈ 0.018` (an interval of length `< 0.073`) — but the support is forced by
the integral representation of `G`.

## The keeper

Free nonvanishing is **necessary but not sufficient**.  The moment/Hankel route wins the property
that killed the annihilation route, and loses on a different axis: its denominators are driven by
the *largest moment index*, which grows with the matrix size, whereas Rivoal–Zudilin's binomial
constructions keep the denominator tied to `d_n` alone.  A live route to `G` needs **both** —
positivity-based nonvanishing **and** a denominator that does not grow with the size of the object.
Neither of the two families probed today has both, and that pair of requirements is a sharper filter
for the next construction than either probe alone.

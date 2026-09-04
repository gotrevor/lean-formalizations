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

---

# Addendum (same day): the fixed-size shifted family closes the moment route entirely

Probe: `catalan-shifted-hankel.py`.

The refutation above is about the determinant's **size**: an `m×m` determinant must reach moment
index `2m`, so clearing costs `e^{4m²}` against a numerator of `e^{-(log 4)m²}`.  That invites an
obvious repair — hold `m` **fixed** and grow the *shift* instead:

    M(n)_{ij} = μ_{n+i+j},  0 ≤ i,j < m.

This looked like the first object with all three of the properties the day's two refutations
demand.  **(A)** nonvanishing is free — `M(n)` is the Gram matrix of the positive measure `xⁿ dμ`.
**(C)** the beam stays narrow — the `G`-part is `(-1)^{n+i+j} = (-1)^n(-1)^i(-1)^j`, rank one, so
`H_m(n) = A + B·G` is a linear form in Catalan's constant **alone**.  **(B)** the denominator index
is `n + 2m - 2`, linear in the growing parameter rather than quadratic.

**It fails, by an infinite margin rather than a constant.**

| `m` | `n` = 2 | 8 | 16 | 32 | 64 | slope |
|---|---|---|---|---|---|---|
| 2 | +0.99 | +7.03 | +21.43 | +46.15 | +100.83 | ≈ **+1.6 per unit `n`** |
| 3 | +6.14 | +16.58 | +26.47 | +51.47 | +111.28 | ≈ **+1.7 per unit `n`** |

The ledger *rises*.  The reason is visible in the two rates:

* **Numerator: polynomial.**  `log₁₀|H_2(n)|` falls by a near-constant `≈ -1.7` per **doubling** of
  `n` — that is `H_m(n) ~ n^{-c}` (measured `c ≈ 5.3` at `m=2`, steeper at `m=3`).  Polynomial,
  because the moments themselves decay polynomially: `μ_n = ±(G - S_n)` with tail `~ 1/(2n)²`.
* **Denominator: exponential.**  `log₁₀ D` grows `≈ 1.75` per unit `n`, since the clearance is
  `lcm{(2j+1)² : j < n+2m}^m ≈ e^{cmn}`.

Polynomial against exponential is not a margin one optimises away.

## Why this closes the family rather than one member of it

The moment construction has exactly two degrees of freedom, the determinant size `m` and the shift
`n`, and **the same quantity governs the numerator's only source of exponential smallness and the
denominator's multiplier**:

* grow `m`: numerator `e^{-1.386 m²}` against denominator `e^{4m²}` — loses by a constant factor;
* grow `n`: numerator polynomial against denominator exponential — loses by an infinite one.

Exponential decay in this family comes *only* from the determinant's size, and the size is *also*
the exponent on the clearance.  The two refutations are therefore one fact seen twice, and there is
no third direction to try.  Whatever eventually works on `G` will not be a moment determinant.

## Where that leaves the three-way filter

The day's honest scoreboard, with `rForm_neg` proved (so Rivoal–Zudilin *does* have positivity-based
nonvanishing — the earlier two-criterion phrasing was too coarse):

| family | (A) positivity nonvanishing | (B) bounded denominators | (C) narrow beam |
|---|---|---|---|
| Rivoal–Zudilin | ✅ | ✅ | ❌ (and `catalan-annihilation-margin.md` says it cannot be narrowed) |
| moment / Hankel, any `m`, any shift | ✅ | ❌ | ✅ |

**No known family has all three, and both of today's candidate repairs are refuted with a
mechanism.**  That is a sharper starting point for the next construction than any of the three
individual probes, and it is a genuinely useful screen: a proposal that does not visibly carry all
three does not need a ledger computed for it.

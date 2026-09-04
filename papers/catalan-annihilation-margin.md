# Probe result: narrowing the Phase 4 beam is refuted (in the natural deformation family)

**2026-09-04.**  Probe: `catalan-annihilation-margin.py`.  Verdict: **refuted, with a mechanism.**

## The idea

Phase 4 proves only a *disjunction* — one of β(2),…,β(20) is irrational — because Zudilin's linear
form is a wide beam:

    r_n = A_0 + Σ_{i even, 2 ≤ i ≤ s-1} A_i β(i).

Zudilin's SIGMA 2018 "twist by half" annihilates unwanted coefficients in the odd-zeta case.  If
some deformation of `R_n` forced `A_4 = … = A_{s-1} = 0`, the form would collapse to `A_0 + A_2·G`
— a linear form in Catalan's constant **alone**, i.e. `G ∉ ℚ`.  So: measure what annihilation costs.

## The family, and why it is the right one

`R_n(-t-n) = R_n(t)` (which kills the odd `i`) survives exactly when the prefactor `(2t+n)` is
replaced by another *antisymmetric* polynomial in `u = 2t+n` — i.e. an odd power.  Keeping the
denominator `∏_{j=0}^{n}(t+j)^s` fixed makes the `d_n^s` clearance uniform across the family, so
integer combinations stay integral.  (The probe **checks** this rather than assuming it: clearance
`= 1` for every basis element in every run.)  So the deformation space is

    Q(t) = Σ_{k=0}^{K} c_k (2t+n)^{2k+1},   c_k ∈ ℤ,

and it is **finite**: convergence needs `deg Q ≤ s(n+1) - 3n - 2`.  Annihilating `A_4,…,A_{s-1}` is
then a *linear* system on `c`, and its solutions form a lattice of dimension `K+1 - (s-1)/2 + 1`.

## Measurement

Score every annihilating `c` by the ledger it produces, exactly:

    LEDGER(c) = ( log|A_0(c) + A_2(c)·G| + s·log d_n + log height(c) ) / n     [need < 0]

against Zudilin's own `LEDGER(full beam)`.  `Δ = LEDGER(annihilated) − LEDGER(full)` is the cost of
narrowing the beam.  LLL runs over the annihilating lattice to minimise `|a+bG|` and `|c|` jointly;
every candidate is re-scored in exact rational arithmetic.

| `n` | `s` | kernel dim | Δ |
|---|---|---|---|
| 2 | 7 | 1 → 4 | **+20.8** |
| 2 | 9 | 1 → 4 | **+34.4** |
| 2 | 13 | 1, 4, 7, 10 | **+65.2** (identical at every dimension) |
| 4 | 7 | 1 → 4 | **+23.3** |
| 4 | 9 | 1 | **+39.2** |

Zudilin's own margin improves by ≈ **0.39 per unit `s`** (`catalan-beta-ledger.py`).  Δ grows by
≈ **7.4 per unit `s`** — nineteen times faster.  Δ also grows in `n`, and is **completely flat in
the dimension of the annihilating lattice**: LLL over a 10-dimensional lattice at `s=13` returns
the same vector as the 1-dimensional kernel, and at `n=4, s=7` it returns a strictly *worse* one.
There is no crossover.

## The mechanism (the part worth keeping)

The annihilated combination is not a *small* form that has become slightly larger.  At `s=13, n=2`
it is `a + b·G ≈ -1.5 × 10^21`.  **Smallness and beam width are the same phenomenon**: `r_n` is
tiny because ten `β` terms and `A_0` nearly cancel each other; force nine of them to vanish and the
survivor has nothing left to cancel against, so the form reverts to the size of its own
coefficients.  Killing a coefficient costs you, roughly, the size of the coefficient you killed.

This is a reason to expect the same failure in any construction where the target's smallness comes
from multi-term cancellation — which is every construction of this type.  A route to `G` alone must
make the form small for a *different* reason (positivity of an integral, as in the Hankel/multiple-
orthogonality family, where nonvanishing is free precisely because it does not come from
cancellation).

## Scope — what this does NOT refute

Only the fixed-denominator, odd-powers-of-`(2t+n)` deformation of Zudilin's `R_n`.  Deforming the
denominator (different pole orders per `j`, other half-integer shifts) is untouched, as is any
construction outside the Rivoal–Zudilin hypergeometric family.  The candidate objection this probe
does answer is "you did not optimise": the annihilating lattice was reduced, up to dimension 10, and
the freedom is worth nothing.  A full SVP enumeration could shave a little; it cannot close 65.

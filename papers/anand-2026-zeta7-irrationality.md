# Anand 2026, "ζ(7) is irrational" — refuted: the load-bearing constant has the wrong sign

**2026-09-23, against Zenodo record 22920911 (`Zeta7 (3).pdf`, posted 2026-09-23).**  Surfaced via
r/mathematics "Zeta 7 proved irrational after zeta 5?" (1wofahc); Elliot Glazer commented that it
"fails Astra's audit".  Local: `anand-2026-zeta7-irrationality.{pdf,txt}` (PDF gitignored).

## What it is

Fauzan's ζ(5) paper with two edits (stated in §1): `D_N⁶ → D_N⁸`, and pole values
`j⁶(X − H_j^{(7)}) + 1/(2j) − 1/6`.  That is exactly `catalan-fauzan-hankel-probe.py K 3K/40 8 --zeta 7`
(our general-S Hermite functional, checked by quadrature and by the S=5 control).  No AI disclosure,
acknowledged dependence on Fauzan.

## The error

Fauzan's race is **A₂₀₀ = +1.3496** (denominator cost) against **U = −1.367** (real decay): a
0.017 margin.  Anand reports **A₂₀₀ = −13.75** and **U = +1.76** (Lemma 6.1, (96)), so the
denominators supposedly *pay* 13.75 per K².  Almost all of it is one number:

    I_out = ∫_{1/3}^{2λ} T(y) dy = −11002997/720000 ≈ −15.28      (122)

Fauzan's `I_out` is **+1.3307**.  It is the outer-range (K/3 < p ≤ K) prime cost of clearing
denominators; a value of −15 would mean those primes contribute a ~e^{15K²} *numerator* factor to
the determinant.  (The integration range also runs to `2λ = 1.85`, i.e. into p > K, where
entries are already p-integral.)

## Measured on the paper's own determinant (exact content, by prime range, `--ranges`)

| | K=40 | K=80 |
|---|---|---|
| ζ(7), outer range K/3 < p ≤ K: `log content/K²` | −1.02 (a cost) | −1.34 (a cost) |
| ζ(7), p > K | 0 | 0 |
| ζ(5) control, outer range | −0.88 | −1.09 (→ Fauzan's +1.33 cost) |
| ζ(7) primitive ledger `log P(ζ(7))/K²` | +0.80 | +0.87 |

The outer range is a *cost* for ζ(7), slightly larger than for ζ(5), and growing — the sign and
magnitude Fauzan's architecture predicts, not a 15-per-K² gain.  Consistent with
`fauzan-hermite-family-scan.md`: the family reaches ζ(5) and stops ~0.9/K² short of ζ(7).

Also internally inconsistent: §B derives `1600(A₂₀₀+U) < −17600` (decay `exp(−17000n²)`) for
M=200 but the abstract and (1) claim `exp(−19000n²)` for M=200.  And U > 0 means the real side
*grows*; the paper's whole margin then rests on the sign-flipped A.

Verdict: **refuted** (~97%).  Not a repairable typo: with a correct `I_out` the family's ζ(7) ledger
is positive by ~0.9/K².

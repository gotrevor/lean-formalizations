# Probe result: the Catalan twin of Fauzan's ζ(5) construction loses, on the REAL side

**2026-09-23.**  Probe: `catalan-fauzan-hankel-probe.py K N c [--quad] [--zeta5]` (exact `Δ_K(X) ∈ ℚ[X]`
via `det(B)·charpoly(−B⁻¹A)`, ~1000× faster than `fauzan-zeta5-hankel-probe.py`).  Verdict: **the
direct twin is closed (~85%)**.  Both of Fauzan's levers were tried; the arithmetic lever is
already present in the twin, the external-field lever works backwards, and the gap is on the
real side by ~0.8 per K².

## The twin

The alternating Abel–Plana formula does for `G` what Hermite's formula does for `ζ(5,a)`.  With
`w(y) = π y² cosh(πy)/sinh²(πy) > 0`:

    ∫ y^{2e} w dy     = (−1)^e (2^{2e+2} − 1) B_{2e+2}                      (rational, cf. (2.2))
    ∫ w/(y²+a²) dy    = a·Σ_{n≥0} (−1)^n/(n+a)² − 1/(2a)
    a = j + 1/2:      = 2(−1)^j (2j+1)(G − T_j) − 1/(2j+1)                  (affine in G, cf. (2.3))

Checked by quadrature to 30 digits.  Poles only at half-integers (integer `a` would bring in
`η(2) = π²/12`).  So the Hankel matrix `μ_X(D_N^c u^{i+k}/D_K)` has everything Fauzan's has:
positive-definite at `X = G`, **full-rank** X-part (unlike the rank-one family of
`catalan-hankel-sublattice.md`), `Δ_K` of degree `h = K − N`.

## Controls

- `--quad`: for `h ≤ 6`, quadrature Gram determinant = exact `Δ_K(G)` to ~1e-39.
- `--zeta5`: same engine on Fauzan's functional reproduces the 2026-09-22 audit ledger
  exactly: `log P_K(ζ(5))/K²` = −0.1657 (K=40), −0.1302 (80), −0.1253 (120), −0.1120 (200).

## The ledger (`log P_K(ξ)/K²`, P = primitive integer polynomial; negative ⇒ irrationality trend)

| family | K=40 | 80 | 120 | 200 | real `logΔ/K²` @120 | clearing `−log cont/K²` @120 |
|---|---|---|---|---|---|---|
| ζ(5), Fauzan field (N=3K/40, c=6) | **−0.166** | **−0.130** | **−0.125** | **−0.112** | (shifted by field) | |
| ζ(5), no field (N=0, c=1) | −0.010 | +0.068 | +0.096 | | −2.993 | 3.089 |
| Catalan, no field | +0.379 | +0.458 | +0.491 | | −2.157 | 2.648 |
| Catalan, Fauzan field | +0.833 | +0.898 | +0.924 | +0.956 | | |

At K=60 every field tried (c ∈ {2,3,4,6}, N/K ∈ {5,10,20,30}%) was worse than no field,
monotonically in both c and N.

## Reading

1. **The external field is a real lever for ζ(5)**: it moves the ledger from +0.10 to −0.13 at
   K=120.  For Catalan it pushes the wrong way.
2. **The arithmetic lever is already in the twin.**  Catalan's clearing (2.65) is *cheaper* than
   ζ(5)'s (3.09): squares, not fifth powers.  Denominators are not the problem.
3. **The real side is the problem: −2.16 vs −2.99.**  Likely mechanism (not proved): the kernel.
   ζ(5)'s weight decays like `e^{−2πy}` (Hermite, `1/(e^{2πy}−1)`), Catalan's like `e^{−πy}`
   (alternating Abel–Plana, `1/sinh(πy)`), at the same pole spacing in `a`.  Weaker external
   field in the equilibrium problem, less Hankel decay.  Rescaling `y` rescales the poles too,
   so the ratio is intrinsic.  The period-1 kernel is available only via `ζ(2,1/4) − ζ(2,3/4)`,
   whose single poles carry `π²` and break the narrow beam.

Small-K caveat: this is not the K² limit.  But the ζ(5) control is negative at every K, and the
Catalan twin is positive by ~0.5–1.0 per K² and *rising* — a different regime from a 1.3% margin.

**What would reopen it:** a positive weight for `G` with rational moments, `G`-affine pole values
and an `e^{−2πy}`-rate kernel.  That is a question about the integral representation, not the
Hankel machinery.

# Fauzan's Hankel family at ζ(7): the family's own knobs cannot close the gap

**2026-10-24.**  Probe: `papers/hermite-pole-lattice-probe.py K N c S {int|half|dense} [--taper] [--ranges] [--quad]`.  It generalizes `catalan-fauzan-hankel-probe.py --zeta S` to arbitrary pole lattices and field profiles.  Prior scan: `fauzan-hermite-family-scan.md`, which found ζ(7) about 0.9/K² short.

## Controls

- **`int` mode reproduces the original probe's ledger exactly:** ζ(5) K=60 no field gives 0.0324386, and Fauzan's K=40 N=3 c=6 gives −0.165706.  The real/clearing split shifts by a common constant from the u = 4t scaling, which cancels in the ledger.
- **`--quad`:** the pole formula μ_X(1/(t+a²)) = a^{S−1}ζ(S,a) − 1/(2a) − 1/(S−1) matches quadrature to about 1e-31, at integer and half-integer a.

## Target

Ledger log P_K(ζ(S))/K², K = 60, no field.  Here "small" means p ≤ K/3 and "middle" means K/3 < p ≤ K.

| S | real | clearing, small primes | clearing, middle primes | ledger |
|---|---|---|---|---|
| 3 | −3.00 | 1.09 | 1.00 | −0.91 |
| 5 | −2.91 | 1.72 | 1.22 | +0.03 |
| 7 | −2.83 | 2.30 | 1.55 | +1.02 |
| 9 | −2.76 | 2.86 | 1.89 | +1.99 |

**Small primes carry two-thirds of the S-growth: +0.30 per unit S, against +0.15 for middle primes.**  If ζ(7) paid only ζ(3)'s small-prime cost, its ledger would be −0.19.  The target was therefore to win back about half of the small-prime clearing.

## Levers tried (ζ(7), K = 60 unless noted)

| Lever | Best ledger | Why |
|---|---|---|
| None | +1.02 | |
| **Half-integer poles a = j + ½** (the only shift keeping the beam narrow: ζ(S, ½) = (2^S−1)ζ(S)) | +4.24 | removes p = 2 (0.34 → 0.09), but odd numbers up to 2K bring primes in (K, 2K] (+1.92) and inflate the middle range |
| **Dense poles a = n/2** | +6.05 | worse on both counts |
| **Uniform field, N × c grid** (N ∈ {4,…,20}, c ∈ {4,…,16}) | **+0.80** (N=8, c=4) | the factorial residues absorb small primes, but the real side pays faster as N·c grows |
| **Tapered field** (multiplicity falls linearly over the small nodes) | **+0.755** (N=8, c=8) | marginal over uniform |
| K trend, uniform best (N ≈ 0.13K, c=4) | +0.78 / +0.84 / +0.83 at K = 40 / 80 / 100 | flat, no K² drift toward zero |

## Verdict (~98% closed)

Within the Hermite/Hankel family, every available knob leaves ζ(7) at least **+0.75/K²** short:

- pole lattice (integer, half-integer, dense);
- external-field size;
- external-field strength;
- external-field profile.

The gap is stable in K.  Field absorption saturates at about 0.25, while the S-growth at small primes costs 0.6 per step S → S+2.

**What would reopen it:** a function space V, other than the factor W·ℙ_{<h} over a pole set, whose Hankel content has small-prime valuation growing sublinearly in S.  Equivalently, a lever acting on the harmonic sums H_{j−1}^{(S)} themselves rather than on the residues.  Nothing in the family supplies one.  ζ(9) and beyond are further out, since the ledger rises about 1 per step.

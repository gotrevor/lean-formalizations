# Fauzan's Hankel family across ζ(3), ζ(5), ζ(7), ζ(9) — and Catalan on the same scale

**2026-09-23.**  Probe: `catalan-fauzan-hankel-probe.py K N c --zeta S` (general-S Hermite weight
`w_S = 2 y^S f^{(S−1)}/(S−1)!`, `f = 1/(e^{2πy}−1)`; moments `(−1)^e B_{2e+2}(2e+S)!/((S−1)!(2e+2)!)`,
poles `j^{S−1}(X − H_j^{(S)}) + 1/(2j) − 1/(S−1)`; identities checked by quadrature at S=3,7;
S=5 reproduces Fauzan (2.2)/(2.3) and the 2026-09-22 audit ledger exactly).

Ledger `log P_K(ξ)/K²` (negative = irrationality trend), best field vs no field, N = 3K/40:

| ξ | real `logΔ/K²` (no field, K=80) | clearing (no field, K=80) | ledger no field K=40 → 80 | best field K=40 → 80 | best c |
|---|---|---|---|---|---|
| ζ(3) | −3.02 | 2.12 | −0.95 → −0.90 | **−1.04 → −1.01** | 4 |
| ζ(5) | −2.95 | 3.02 | −0.01 → +0.07 | **−0.17 → −0.13** | 6 |
| ζ(7) | −2.88 | 3.95 | +0.97 → +1.06 | +0.80 → +0.87 | 8 |
| ζ(9) | −2.83 | 4.87 | +1.86 → +2.05 | +1.81 → +1.90 | 10 |
| G (Catalan twin, `catalan-fauzan-twin.md`) | −2.14 | 2.60 | +0.38 → +0.46 | worse with any field | 1 |

## Reading

- **The real side barely depends on S** (≈ −2.9 per K² with no field): it is set by the kernel
  `1/(e^{2πy}−1)` and the pole spacing, which S does not touch.
- **The clearing cost climbs ~0.9 per step S → S+2**: the pole values carry `H_j^{(S)}`, whose
  denominators are `lcm(1..j)^S`.  The residue-class cancellation removes most of it, not the
  S-dependence.
- **The external field buys ~0.1–0.2**, roughly independent of S.
- So the family proves ζ(3) with a wide margin (a consistency check, not news), ζ(5) with a thin
  one (Fauzan), and **stops**: ζ(7) is short by ~0.9 per K², several times what the field buys.
  Reaching ζ(7) needs a new lever on the arithmetic side, not a retuning.
- **Catalan sits between ζ(3) and ζ(5) on arithmetic** (2.60) but has a much weaker real side
  (−2.14 against −2.9), because its alternating Abel–Plana kernel `1/sinh(πy)` decays at half
  the rate.  With ζ's kernel strength it would clear.  The Catalan question is therefore
  exactly: *is there a positive weight for G with an `e^{−2πy}` kernel, rational moments and
  G-affine pole values?*

Small-K caveat as in the twin write-up: K ≤ 80 is not the K² limit (the ζ(5) ledger at K=200 is
−0.112, the paper's limit margin is −0.017), but the gaps for ζ(7), ζ(9) and G are ~50× that margin.

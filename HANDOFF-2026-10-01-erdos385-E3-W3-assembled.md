# HANDOFF 2026-10-01 — Erdős #385 E3: everything wired; 5 analytic leaves left
Branch `erdos-385`, HEAD = the "W3 variance_small assembled" commit.  Tree clean.
Scope: `src/LeanFormalizations/NumberTheory/Erdos385/AlmostAll.lean` sorry-free.

## Done this lap (all `#print axioms`-clean except where they consume open leaves)
- Graph.lean: 3 edges (`noCarrier_of_bad`, repulsion ⇒ #385(i), FGKMT ⇒ sibling).
- AlmostAll: W0 `exists_admissible` (ContDiffBump), W1 `witness_margin`, W2 `card_badWindow_le`
  (disjoint unit intervals, no overlap count), control `not_shortIntervalPNTUnitWindow`,
  edge `shortIntervalPNT_of_mediumPNT`, W2′ `longAverage_lower` (two ShortIntervalPNT counts,
  NO Mertens), headline `almost_all_F385` (geometric window covering via `Nat.findGreatest`),
  W3a `variance_eq_norm`, W3b `coeffA_facts`, W3c `LSeries_coeffC_eq` (A = PQ/log Z),
  W3 `variance_small` (assembled from MR16 + the leaves).

## Open leaves (the only `sorry`s in AlmostAll.lean)
1. `primeQ_meanSquare` (W3e): MVT with a_q = 1/q on setQ, N = ⌊(1+2δ)√Z⌋; ∑ q⁻² ≤ #/Z ≤ 1/√Z.
   Need primeQ(1+it) = ∑_{n ≤ N} a_n n^{-it} (q^{-(1+it)} = q⁻¹ q^{-it}).  Easy-moderate.
2. `coeffC_meanSquare` (W3f): MVT on a_m/m, N = ⌊2X⌋; LSeries = finite sum (support [X,2X), W3b);
   ∑ (a_m/m)² ≤ (2X)·(1/4)/X² .  Easy-moderate.
3. `primeP_small` (W3d): g0(u) = g(u)/u (ContDiff via local-zero near 0); Lemma VK at P=√Z,
   T=16Z; Mellin decay |mellin g0 (1−it)| ≪ 1/|t| (one integration by parts); prime powers via
   `Chebyshev.psi_sub_theta_le`.  Moderate-hard.
4. `smoothPrimeSumVK_of_VKZ`: contour shift (Mellin inversion + residue).  THE crux; consider
   porting PNT+ smoothed-Chebyshev code (`PrimeNumberTheoremAnd/MediumPNT.lean`).
5. `not_smoothPrimeSumVKMRNorm_of_VK`: control; needs a bump with mellin f (1−i) ≠ 0 and
   P-asymptotics; moderate.

## Gotchas this lap
- maxHeartbeats is per DECLARATION: long proofs time out everywhere at once → `set_option
  maxHeartbeats N in` (W2′ 1.6M, W3 3.2M).  `clear_value` after `set` kills linarith isDefEq blowups.
- `rw [← hZsq]` rewrites Z inside √Z too; use `linear_combination c * hZsq`.

# HANDOFF 2026-10-01 — Erdős #385 E3: ONE sorry left in AlmostAll.lean (V4 prime-sum half)
Branch `erdos-385`, HEAD = "V4: Mellin inversion on Re s=2 + main term" commit.  Tree clean.
Scope: `src/LeanFormalizations/NumberTheory/Erdos385/AlmostAll.lean` sorry-free.

## Done this lap (all green, committed)
W3e `primeQ_meanSquare`, W3f `coeffC_meanSquare`, control `not_smoothPrimeSumVKMRNorm_of_VK`,
W3d `primeP_small` (cutoffDiv_facts, primeP_decomp, mellin decay IBP, primeP_small_params),
crux edge `smoothPrimeSumVK_of_VKZ` assembled from V4/V5/V6; **V5 `vertical_integral_bound`
(VK contour shift) PROVED**; V6 `smoothTwist_smallP` PROVED; V4 main-term half
`mainTerm_eq_vertical` + `mellin_inversion_two` + `mellin_vertical_facts` PROVED.

## The only open sorry: `smoothTwist_sub_main_eq` (V4)
Plan (all ingredients in file):
1. PA: smoothTwist f P t = (1/2π) ∫ F(2+iy) P^{2+iy} · L↗Λ(2+iy+it) dy.
   Per n ≥ 1: f(n/P) via `mellin_inversion_two`, same cpow algebra as `hc1` in
   `mainTerm_eq_vertical` (x := n); swap ∑'/∫ with `integral_tsum_of_summable_integral_norm`
   (∫‖·‖ ≤ Λ(n) n^{-2} P² Kπ, summable by `ArithmeticFunction.LSeriesSummable_vonMangoldt` at 2,
   norms via `LSeries.norm_term_eq`, cf. `zetaH_bound_two`).
2. Combine: zetaH w = −L↗Λ w + 1/(w−1) on Re w = 2
   (`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`); split ∫ with
   integrability (zetaH-integrand integrable as `hgi` in V5; 1/(w−1)-integrand continuous, ≤ K P²/(1+y²)).
   Result: S − M = −(1/2π)∫ F P^s zetaH = (PA) − (mainTerm_eq_vertical).

## Gotchas
- `set_option maxHeartbeats 4000000 in` before V5 docstring (needed).
- `Complex.inv_cpow` + `arg_ofReal_of_nonneg` for (P⁻¹)^(-z) = P^z.
- nested single-step `calc` followed by an outer `calc` mis-parses: use `exact`.
- Fubini on restricted measure: `Measure.ae_prod_iff_ae_ae` + `measurableSet_le`.

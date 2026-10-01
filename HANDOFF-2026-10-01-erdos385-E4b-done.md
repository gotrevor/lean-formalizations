# HANDOFF: Erdős #385 E4b DONE (2026-10-01)

`McDiarmid.lean` is sorry-free; `mcDiarmidFinite_holds : Literature.McDiarmidFinite` is axiom-clean
(`[propext, Classical.choice, Quot.sound]`), commit 3d30f7c, full `lake build` green.

- `Erdos385/McDiarmid/Hoeffding.lean`: finite Hoeffding lemma via mathlib's
  `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` on `PMF.uniformOfFintype`.
- `Erdos385/McDiarmid/Core.lean`: `avgS f s x := avg_z f (s.piecewise z x)`; `sum_update_swap`
  (coordinate-swap involution of Ω×Ω) gives the tower step; `sum_exp_le` = the moment bound.
- Chernoff with λ = −4t/Σc² in `McDiarmid.lean`; Σc² = 0 is the trivial case.

Next: once E4 (`Exceptional.lean`, branch `erdos-385-brun`) merges, its headline depends only on
`ArithLargeSieve` and `LinearSieveIntervalLower`.

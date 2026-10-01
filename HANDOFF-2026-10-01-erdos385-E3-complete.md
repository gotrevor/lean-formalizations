# HANDOFF 2026-10-01 — Erdős #385 E3 COMPLETE (AlmostAll.lean sorry-free)
Branch `erdos-385`, HEAD `e819725` + docs commit.  Tree clean.

## Result
`Erdos385.almost_all_F385 : MR16Lemma14 → MontgomeryVaughanMVT → VKZeroFreeLogDeriv →
MediumPNTStatement → AlmostAllF385`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
Also clean: `smoothPrimeSumVK_of_VKZ`, `vertical_integral_bound`, `variance_small`.

## This lap
V4 `smoothTwist_sub_main_eq` proved via two new lemmas in `AlmostAll.lean`:
- `twist_inversion`: `x^{-it} f(x/P) = (1/2π) ∫ x^{-(2+iy+it)} F(2+iy) P^{2+iy} dy` (extracted from
  the `hc1` step of `mainTerm_eq_vertical`).
- `smoothTwist_eq_vertical`: `S = (1/2π) ∫ F(2+iy) P^{2+iy} L(Λ, 2+iy+it) dy`; Fubini by
  `integral_tsum_of_summable_integral_norm` with `∫‖G n‖ = ‖term Λ 2 n‖ · ∫‖F P^s‖`
  (`LSeries.norm_term_eq` makes the per-`n` norm independent of `y`).
Then `L(Λ, w) = 1/(w−1) − zetaH w` pointwise, `integral_sub`, `mainTerm_eq_vertical`, `ring`.

## Open (outside the E3 scope)
- Five known-false controls in `Literature/Erdos385AlmostAll.lean` (`not_…`, body `sorry`).
- Hypothesis discharge: `MediumPNTStatement` from PNT+ `MediumPNT` (olean unbuilt at this pin).
- E4 is paper-only per `ROADMAP-ERDOS-385.md`.

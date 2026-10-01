# HANDOFF 2026-10-01 — phase 60 (Kronecker lemma) DONE

Branch `main`, HEAD `45339d3` (+ this doc). Build green.

## Done
`src/LeanFormalizations/NumberTheory/Mills/Kronecker.lean` is sorry-free; all 7 frozen statements
(`trace_pow_periodic_of_splits`, `dvd_trace_of_splits_mod`, `not_splits_mod_eventually`,
`splits_of_isSquare_disc`, `not_isSquare_charDisc_mod_eventually`, `composite_of_jacobi_hit`,
`mills_kronecker`) are `#print axioms`-clean (propext, Classical.choice, Quot.sound).
Helpers added (public): `splits_dvd_pow`, `pow_eq_one_of_splits`, `charpoly_three_eq`,
`exists_root_of_not_irreducible`, `charDisc_cast`, `trace_pow_three_mod_three`;
`Projective.exists_companion_root_vieta` (adds distinct complex roots + Vieta; the frozen
`exists_companion_root` is now derived from it, statement unchanged).

## Key trick
Split + det≠0 ⇒ charpoly ∣ (X^(p−1)−1)^n ∣ X^(p^n(p−1))−1 via Frobenius in `(ZMod p)[X]`
(commutative, no matrix CharP/Nonempty case split), then Cayley–Hamilton.

## Next
Per DIRECTION.md (altitude laps own it). Candidate: run the Jacobi certificate
(`composite_of_jacobi_hit`) on concrete cubics from `scripts/mills-residual-probe.py`.

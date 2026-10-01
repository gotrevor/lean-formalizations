# HANDOFF: Erdős #385 E4c DONE (2026-10-01)

`Literature.ArithLargeSieveWeak` discharged: `arithLargeSieveWeak_holds` (constant `3 + 24π`),
`#print axioms` = {propext, Classical.choice, Quot.sound}.  Build green (8844 jobs).

- `LargeSieve/Montgomery.lean`: Parseval over residues mod q, prime case by Cauchy–Schwarz on the
  allowed classes, squarefree induction peeling `minFac`, twisted weights `w n e(n a₁/q₁)`, injective
  CRT map `(a₁,a₂) ↦ a₁p + a₂q₁ mod q` (only an injection is needed, no card count).
- `LargeSieve/Gallagher.lean`: Gallagher pointwise inequality via FTC, disjoint arcs ⊆ [-1,2]
  (`integral_biUnion_finset` + `setIntegral_mono_set`), Parseval on [-1,2], AM-GM in place of
  integral Cauchy–Schwarz.
- `LargeSieve.lean`: Farey separation `1/Q²`, shift `n = M + k`, assembly.

Next: E4 (`Exceptional.lean`, branch `erdos-385-brun`) can now take `arithLargeSieveWeak_holds`
once it is restated against the weak constant.

# HANDOFF: Erdős #385 E4d DONE (2026-10-01)

`badCountExpBound_of_weak` and `badCountExpBound_of_linearSieve` proved, `#print axioms` =
{propext, Classical.choice, Quot.sound}.  So `BadCountExpBound` now rests on
`LinearSieveIntervalLower` alone (E5 targets that on branch `erdos-385`).

- `ExceptionalWeak/Sieve.lean`: `LSWith C` (large sieve at constant C), `exists_lsWith` (WLOG C ≥ 1),
  `sieve_count_weak` (copy of `sieve_count`, RHS `C (X + Q²)`).
- `ExceptionalWeak/Count.lean`: `bad_count_le_weak`.
- `ExceptionalWeak/Main.lean`: `eventually_bad_le_weak`, bound `(3 + 2C) X e^{−L^θ}`.
Full build green (8859 jobs).

Branch `erdos-385-brun`, proof commit `d2223cb`.
Next: once E5 (`linearSieveIntervalLower_holds`, branch `erdos-385`) lands, merge it and compose
`badCountExpBound_of_linearSieve linearSieveIntervalLower_holds : BadCountExpBound` unconditionally.

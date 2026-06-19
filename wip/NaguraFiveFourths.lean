/-
# WIP / quarantined — Nagura `5/4` rung (NOT built; not in `src/`)

Excised from `src/LeanFormalizations/Combinatorics/NoThreeInLine/PrimeGap.lean` on 2026-06-19
(FINISH-AND-STOP wind-down). `nagura_prime` (Nagura 1952: a prime in `(n, 6n/5]` for `n ≥ 25`) is
*proven mathematics* but its formalization needs Nagura's explicit finite inequality — unreachable
from this repo's elementary Chebyshev stack (`A` matches `(6/5)A` with zero slack) and unreachable
from the in-repo PNT (`exists_prime_gap_pnt` fires only *eventually*, at a threshold ≫ 25). Its `5/4`
rung (`maxNoThreeInLine_ge_five_fourths`, the sole consumer) is **superseded** by the unconditional
axiom-clean `6/5` (`maxNoThreeInLine_ge_six_fifths`) and the PNT-driven `3/2 − o(N)`
(`maxNoThreeInLine_ge_three_halves_sub`). Neither declaration is referenced elsewhere.

**This is the genuine parked crux** (vs. the dead-code Wiener island): if FINISH-AND-STOP is lifted and
a `5/4` rung is wanted, finish `nagura_prime` here (the tuned analogue of `bertrand_main_inequality`
for ratio `6/5`, valid `n ≥ N₀`, with `n ∈ [25, N₀)` by `decide`) then paste both back into
`PrimeGap.lean`. NOT part of the build (outside `src/`); will not compile standalone.
-/

theorem nagura_prime {n : ℕ} (hn : 25 ≤ n) : ∃ p, p.Prime ∧ n < p ∧ 5 * p ≤ 6 * n := by
  sorry

theorem maxNoThreeInLine_ge_five_fourths {N : ℕ} (hN : 60 ≤ N) :
    3 * (5 * N / 12) ≤ maxNoThreeInLine N := by
  obtain ⟨p, hp, hlo, hhi⟩ := nagura_prime (n := 5 * N / 12) (by omega)
  have h2p : 2 * p ≤ N := by omega
  have := maxNoThreeInLine_ge_of_two_mul_prime_le hp h2p
  omega

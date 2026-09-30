# HANDOFF — phase 43 COMPLETE (2026-09-30)

HEAD at handoff: `f1d5c3b` (previous green: `81b5ef6`).

## Scope and result

Scoped objective: `sorry-free:src/LeanFormalizations/NumberTheory/Mills/CoveringInstances.lean`.
**Met.**  File is sorry-free, `lake build` green (8762 jobs), `scripts/fact-graph` rerun
(30 edges, 29 hypotheses).  All three frozen statements:

```
LeanFormalizations.Mills.CoveringInstances.fib_five_pow_prime_free
LeanFormalizations.Mills.CoveringInstances.fib_prime_pow_prime_free_all
LeanFormalizations.Mills.CoveringInstances.lucasU_unit_prime_pow_prime_free
```
each `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## The substantive finding: the route was redundant, not broken

**No step of the planted route failed.**  Walking route step 1 revealed that phase 41's own lap had
already carried all three statements to completion inside the files it built:

| phase-43 statement | already proved as |
| --- | --- |
| `fib_five_pow_prime_free` | `FibonacciCoveringAllPrimes.fib_five_pow_prime_free_all` |
| `fib_prime_pow_prime_free_all` | `FibonacciCoveringAllPrimes.fib_prime_pow_prime_free_all` |
| `lucasU_unit_prime_pow_prime_free` | `LucasCoveringAllPrimes.lucasU_prime_pow_prime_free` (hypotheses verbatim) |

Route step 1 (a `Finset`-general `covering_of_good`) was never needed: `CoveringEngine.covering_of_mech`
is *already* stated over an arbitrary `S : Finset ℤ`, and two `Finset`-general covering/prime-free
pairs already exist (`FibonacciCoveringAllPrimes.covering_of_good` / `prime_free_of_covering`;
`LucasCoveringAllPrimes.covering_of_good_seq` / `prime_free_of_covering_seq`).

So `CoveringInstances.lean` is the phase-43 **audit surface** for Theorem C's binary families, not
new mathematics.  Recorded in `ROADMAP-PRIME-TOWERS.md` under Theorem C as
"Phase 43 note (2026-09-30): no failing step — the phase was already subsumed", with the planting
lesson: **grep the existing Mills files for the target statement shape before writing a phase route**
(phase 41's lap overshot its own brief; the c = 5 survivor handling and the Lucas-unit instance were
both finished there).

## Next hardest open obligation (for whoever plants phase 44)

Everything binary in Theorem C is now closed in Lean.  The real wall is **`d ≥ 3`**:

* `ROADMAP-PRIME-TOWERS.md` § "Theorem C′: non-integrality of limit points for `d ≥ 3`".  The
  `d = 2` proofs all route through an *exact composition* (`Φ_J` / `lucasV_mul_odd` /
  `lucasOddPoly`), which has no analogue at `d ≥ 3`.  The reformulated obstruction: the `c`-adic
  limit `Λ` exists with `Λ^(c^(d')−1) = I`, hence is torsion in `GL_d(ℤ_c)` with Teichmüller
  eigenvalues; the needed certificate is "no such torsion element has entry `s − h`".  Candidate
  route in the roadmap: norm/trace relations over `W(𝔽_(c^d))`.  The whole assembly is already
  `d`-generic in Lean (`exists_shift_pow_congr`, `covering_of_good_seq`,
  `prime_free_of_covering_seq`, `CoveringEngine.covering_of_good`), so only the good-prime
  hypothesis is missing — that is the single named crux.
* Concrete first target named in the roadmap: Tribonacci at `c = 3` (`n = 13`, `K ⊃ ℚ(√−11)`,
  linear disjointness from `ℚ(ζ₁₃)`), i.e. prime-free intervals around `T(3^n)`.
* Also open, off this thread and designated-open: the four disclosed sorries in
  `NumberTheory/Transcendence/CorvajaZannier.lean`.

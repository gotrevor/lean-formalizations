# HANDOFF 2026-09-30 — phase 37 COMPLETE (FibonacciAllPrimes sorry-free, axiom-clean)

**Branch** `main` · **HEAD at handoff** `28ce498` (this doc's own commit follows) · treadmill
STOP requested after this lap, so nothing is in flight and no `sorry` was left mid-edit.

`src/LeanFormalizations/NumberTheory/Mills/FibonacciAllPrimes.lean` is sorry-free; all four
frozen statements are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`):
`fib_odd_mul`, `fibOddPoly_far`, `not_dvd_fib_prime_pow`, `fib_prime_pow_add_not_prime_all`.
`lake build` green; `scripts/fact-graph` rerun (30 edges, 29 hypotheses).

**Result.** For **every** prime `c` and every integer `h`, `F(c^n) + h` is composite for
infinitely many `n`.  The split Fibonacci primes `c ≡ ±1 (mod 5)` are closed — no
non-integrality proof needed.

**The idea.** Phase 35 had recorded that the entry family `U` has no composition identity.
That is false at **odd** index: `det(fibM^N) = (−1)^N = −1`, so Cayley–Hamilton on `A = fibM^N`
gives `A² = (tr A)•A + 1` and `A⁴ = T•A² − 1` with `T = 5F(N)² − 2` — a coefficient in `F(N)`
alone.  Hence `F((2j+1)N) = Φ_j(F N)` for odd `N`, and `c^n` is odd for odd `c`.

Full formalization notes, including the six-line `c ∤ F(c^n)` route
(`L(m)² − 5F(m)² = 4(−1)^m` + phase 35's `L(c^n) ≡ 1 (mod c)` ⟹ `c ∣ 3` or `c ∣ 5`) and the
case-split-free endgame, are in `SWEEP-PRIME-MODULUS.md` § Phase 37.

## Reusable lemmas added
`fibOddAux`, `fibOddPoly_eq_mul`, `fibOddPoly_neg`, `fibM_pow_apply`, `one_apply_zero_one`,
`fibM_pow_trace_sq`, `fibM_pow_det_odd`, `fibOddAux_growth`, `fibOddAux_mono`,
`fibOddPoly_far_pos`, `lucas_sq_sub_fib_sq`, `dvd_fibOddPoly_sub`,
`fib_prime_pow_add_not_prime_odd`.

## Exact next steps (for a fresh session)
1. `lake build` should be green at HEAD with zero `sorry` in
   `src/LeanFormalizations/NumberTheory/Mills/FibonacciAllPrimes.lean`; every remaining `sorry`
   in `src/` is designated-open audit surface from earlier phases, untouched by this lap.
2. An **altitude lap must re-own `DIRECTION.md`**: this lap appended a "phase 37 DONE" section and
   renumbered the queued Lucas-entry phase 36 → 38 before the operator rule "altitude laps own
   DIRECTION.md" was surfaced.  Re-derive that file's CURRENT DIRECTIVE rather than trusting my
   edit.
3. Then phase 38 as below.

## Next
Phase 38 (was 36): general Lucas **entries** `U(P,Q)` at odd `c`.  Concrete attack recorded in
the sweep: at odd `N`, `det(A_N) = −Q^N`, so the doubling coefficient is a polynomial in `U(N)`
**and** `Q^N`.  That extra `Q^N` is the whole difficulty; for `Q = ±1` it is a sign and the
phase-37 route should transfer verbatim.

Note: this lap appended a phase-37 DONE section to `DIRECTION.md` before the operator hook's
"altitude laps own DIRECTION.md" rule was surfaced.  An altitude lap should re-own that file.

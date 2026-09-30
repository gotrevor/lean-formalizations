# HANDOFF 2026-09-30 — phase 35 COMPLETE (LucasPrimePow sorry-free, axiom-clean)

HEAD `6b7cd6e`.  `src/LeanFormalizations/NumberTheory/Mills/LucasPrimePow.lean` is sorry-free;
all frozen statements are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`):
`lucasL_eq_fib`, `lucasV_mul_odd`, `lucasV_neg_one_growth`, `lucas_prime_pow_mod`,
`lucasV_prime_pow_add_not_prime`, `lucas_prime_pow_add_not_prime`.  `lake build` green,
`scripts/fact-graph` rerun (30 edges, 29 hypotheses).

**Result.** For every odd prime `c`, every `P` with `c ∤ P`, and every integer `h`,
`V_(c^n)(P,−1) + h` is composite for infinitely many `n`.  `L(c^n) + h` is `P = 1`.

Full formalization notes (what was new, what the route cost) are in
`SWEEP-PRIME-MODULUS.md` § Phase 35.  Headlines:

* `trace_pow_eq_lucasV` is the single algebraic engine: `(B^k).trace = lucasV B.trace B.det k`
  for any 2×2 integer `B`, by `Nat.twoStepInduction` off explicit Cayley–Hamilton.  Reusable.
* Frobenius `V_c(x,−1) ≡ x (mod c)` via `Commute.add_pow` on `!![x,1;1,0]` and `!![0,−1;−1,x]`
  (sum = `diagonal (fun _ => x)`, both trace `x`, det `−1`).  Only glue lemma needed was
  `trace_mul_natCast`.  Strictly shorter than phase 34's `AdjoinRoot` Frobenius — prefer this
  pattern for any future `tr(B^p) ≡ (tr B)^p` obligation.
* `lucasV_neg` (`V_k(−x,−1) = (−1)^k V_k(x,−1)`) gives a sign WLOG to `P ≥ 1`, which is how the
  monotonicity that `SharedConjecture.exists_trace_pow_congr`'s endgame needs is recovered
  without phase 33's iterated-return trick.
* Endgame has **no** case split on `h`.

## Reusable lemmas added
`lucasV_zero/one/succ_succ/two/three`, `sq_eq_trace_smul_sub_det`, `trace_pow_eq_lucasV`,
`lucasV_neg`, `dvd_lucasV_sub`, `lucasM`/`lucasM_trace`/`lucasM_det`/`trace_lucasM_pow`,
`lucasV_two_mul`, `lucasV_pos_lt`, `one_le_lucasV`, `lucasV_strictMono`, `nat_le_lucasV`,
`trace_mul_natCast`, `dvd_two_mul_lucasV_sub_pow`, `lucasV_prime_mod`, `lucasV_prime_pow_mod`,
`exists_lucasV_prime_pow_congr`.

## Next (DIRECTION.md order)
1. **Phase 36 (drafted in the sweep):** general Lucas **entry** family `U(P,Q)` at odd inert `c`
   — the natural generalization of phase 34.  Warning recorded in the sweep: the phase-35 trace
   route does *not* transfer, because `U` has no composition identity `U_(cm) = f(U_m)`; the
   inert Frobenius sign flip is the route there (phase 34 pattern, now with general `P,Q`).
2. **Split Fibonacci primes** `c ≡ ±1 (mod 5)` (11, 19, 29, 31, 41, …) remain the Maze row:
   needs a proof that the single `c`-adic limit point of `F(c^n)` is not an integer.  Phase 35
   is evidence the Dickson/composition idea works when a composition identity exists — for
   entries at split primes there is none, so that row still needs a new idea.

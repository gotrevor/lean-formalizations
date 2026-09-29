# HANDOFF — phase 32 COMPLETE: Saito's Problem 1.8 answered (2026-09-29)

## What landed

`src/LeanFormalizations/NumberTheory/Mills/SaitoFibonacci.lean` — sorry-free, all five frozen
statements `#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound` only):

- `fib_two_pow_odd`
- `two_pow_dvd_fib_two_pow_succ_add`  (the 2-adic sign flip)
- `exists_fib_two_pow_congr`          (the GL₂(𝔽_p) Lagrange mechanism, entrywise)
- `two_pow_dvd_sub_or_add_of_lt_padicValNat`
- `fib_two_pow_add_not_prime`         (**the headline**: ∀ h : ℤ, ∃ᶠ n, ¬ Prime (F(2^n) + h))

This resolves K. Saito, arXiv:2504.14968, **Problem 1.8** affirmatively and unconditionally: no
`Literature/` hypothesis, no conjecture. The math is the one in `PROBE-SAITO-FIBONACCI.md`; nothing
in the route failed. `scripts/fact-graph` re-run (30 edges, 29 hypotheses).

## Formalization notes (also folded into the probe file)

- `lucas m = 2F(m+1) − F(m)` over `ℤ`; `lucas (2m) = lucas m² − 2(−1)^m` from
  `Nat.fib_two_mul_add_one` + a two-line Cassini induction. Only `2^(n+1) ∣ lucas(2^n)+1` is
  needed, so the exact valuation is never computed.
- `F(2^n)` odd from `Nat.fib_gcd` with `gcd(2^n,3)=1`, `F 3 = 2` — no parity induction.
- `v₂|GL₂(𝔽_p)| = 2v₂(p−1)+v₂(p+1)` via `Nat.factorization_mul`; `min = 1` from the `p % 4` split;
  `k/2 ≤ max` in both branches.
- `exists_entry_pow_congr` is a private entrywise clone of `SharedConjecture.exists_trace_pow_congr`
  (same proof, reads entry `(0,1)` of `!![1,1;1,0]^N`). `det = −1` makes `p ∤ det C` free.
- Final contradiction at `n = 4|h| + N + 4`, giving `2^(n/2) > |2h|`.

## Next

`DIRECTION.md` now has no open 🎯. Pick the next target from `PENDING_WORK.md` / `Maze.lean`
`reopenIf` rows. Natural follow-ons from this lap:
- The Lucas analogue `L(2^n) + h`: the same machinery should settle every `h` **except**
  `h ∈ {0, 2}` (`h = 2` is `L(2^(n−1))²`, composite; `h = 0` is the Fermat-hard case). Writing that
  down would sharpen the `DoubleExpTraceComposite` boundary.
- `DoubleExpTraceComposite` itself (phase 30) is still a conjecture; phase 32 shows the
  *non-trace* (matrix-entry) analogue is provable when the sequence alternates 2-adically. That
  dichotomy — converging vs alternating — is the crux to formalize next.

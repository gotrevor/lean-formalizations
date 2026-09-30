# Sweep: what the prime-as-modulus filter settles (2026-09-29)

**The filter** (phases 29, 32, 33).  Let `u(N)` be read off `A^N` for an integer matrix `A`: either an entry or the trace.  Let `c` be a prime.  If `u(c^n) + h = p_n` is prime for all large `n`, then `v_c|GL(𝔽_p)|` must be large; otherwise `p_n ∣ p_(n+j)` for some `j ≥ 1`.  For a 2×2 matrix this means `p_n ≡ ±1 (mod c^(~n/2))`.  So a shift `h` **survives** only if `u(c^n) + h → ±1` `c`-adically along every `n`.

**Instrument.**  `scripts/prime-modulus-sweep.py` computes the `c`-adic limit points of `u(c^n)` at precision `c^6` and `c^9`, and prints the surviving `h`.
- "Integer survivors" means the same small residue at both precisions.
- "Non-integral" means the survivor residues never stabilise.  That is **numerical evidence only**: to settle every `h` you still have to prove the limit is not an integer.
- Known-answer control: the Fermat-type cases come out as integer survivors, as they must.  Examples: `L(2^n)` at `h = 0`, and `a^(2^n) + 1`.

## Freshness
- The 1×1 case `a^(c^n) + h` is **folklore**.  It is olympiad material, e.g. "for every `k > 1`, `k·2^(2^n) + 1` is composite for infinitely many `n`" in the PEN problem collection.  So there is no phase for it.
- The 2×2 **entry** case at a general base is where the new content is.  Saito's Problem 1.8 (the `c = 2` Fibonacci case, now proved in phase 32) is the only instance I found posed in print.

## Results for Fibonacci `F(c^n) + h` (entry `U(1,−1)`), primes `c ≤ 47`

| `c` | how `5` behaves at `c` | limit points of `F(c^n)` | verdict |
|---|---|---|---|
| 2, 3, 7, 13, 17, 23, 37, 43, 47 | inert (`c ≡ ±2 mod 5`) | 2, a sign flip | **all `h` settled** by the filter plus the flip |
| 5 | ramified | 1, namely `0`, since `5^n ∣ F(5^n)` | survivors `h = ±1` only; these are killed by `F(4k+1) ± 1 = F(2k+1)L(2k)`, `F(2k)L(2k+1)` |
| 11, 19, 29, 31, 41 | split (`c ≡ ±1 mod 5`) | 1 | survivors look non-integral (numerics only); proving that needs an algebraic argument |

**Why the inert primes work.**
- Frobenius swaps the roots: `φ^c ≡ ψ = −φ⁻¹ (mod c)`, that is, `A^(c+1) ≡ −I (mod c)`.
- Lifting gives `A^(c^(n+1)) ≡ −A^(−c^n) (mod c^(n+1))`.  Reading off entry `(0,1)`, with `c^n` odd, gives the sign flip `F(c^(n+1)) ≡ −F(c^n) (mod c^(n+1))`.
- The contradiction then runs as in phase 32.  For odd `c` it also kills `h = ±1`, because `F(c^n) ≡ (−1)^n (mod c)` is a unit.

**Conjecture from the sweep** (numerics above): for **every** prime `c` and every integer `h`, `F(c^n) + h` is composite for infinitely many `n`.  Phase 34 proves the inert primes and `c = 5`.  The split primes are a Maze row.

## Other families (full table: run the script)
- **Traces `V(c^n)` (Lucas numbers, etc.).**  There is always a single limit point, because Frobenius fixes a trace.
  - For `c = 2`, the integer survivors are exactly the classical open cases, such as `L(2^n)` (`h = 0`).
  - For odd `c`, the survivors are usually non-integral.  `L(7^n) + h` would then be settled for every `h`, but that needs the non-integrality proof.  A route when `Q = ±1`: `V(c^(n+1)) = D_c(V(c^n), Q)` exactly, where `D_c` is the Dickson polynomial.  An integer limit is then an integer root of `D_c(x, Q) − x`, and there are finitely many to check.
- **Entries at inert `c`** always give two limit points, so every `h` is settled whenever `c ∤ Q` and `c` is inert in `ℚ(√(P² − 4Q))`.  This is the natural general theorem after phase 34.

# HANDOFF 2026-09-30 — phase 41 (CoveringEngine.lean) CLOSED

**Branch** `main` · HEAD `c00ce5e` (this doc). Proof commit `be4d97a`, cleanup `21595a0`.  `lake build` green (8760 jobs).  Target file **sorry-free**.
All four frozen statements `#print axioms`-clean `[propext, Classical.choice, Quot.sound]`.
`scripts/fact-graph`: 29 hypotheses, unchanged.  Nothing in flight; no Aristotle job used.

## What landed — `NumberTheory/Mills/CoveringEngine.lean`

| declaration | content |
|---|---|
| `dvd_linearMap_of_entries` | entrywise divisibility passes through any `ℤ`-linear `ℓ`, via `SmulDvd a M ↔ M = a • B` |
| `dvd_trace_of_entries` | the trace special case (`Finset.dvd_sum` over the diagonal) |
| `covering_of_mech` | the covering assembly with the `glCard 2` hard-coding removed: abstract sequence `t`, abstract good-prime predicate `G : ℕ → ℕ → Prop` |
| `shifts` / `mem_shifts` / `shifts_bound` | the finite shift set `{|h| ≤ H}` |
| **`covering_of_good`** | (D1) along `c^n` for any `A : Matrix (Fin d) (Fin d) ℤ` and any `ℓ` |
| **`prime_free_of_good`** | prime-free intervals of half-width `H` around `ℓ(A^(c^n))`, i.o. |
| `exists_shift_lucasV_prime_pow_congr` | `c^n ∣ V(c^(n+d)) − V(c^n)` — `c`-adic convergence for the **companion** sequence |
| `exists_good_lucasV_prime_factor` | the single-index certificate for `V` |
| `lucasV_prime_pow_prime_free_pos` / **`lucasV_prime_pow_prime_free`** | prime-free intervals around `V(c^n)(P,−1)`, every odd prime `c ∤ P` |
| **`fib_prime_pow_prime_free`** | every prime `c ≠ 5` (`c = 2` from phase 40, odd from phase 41's all-primes file) |

## The mathematical content
Previous laps had `U(P,Q)` uniformly in `h`, but `V` only **one shift at a time**
(`lucasV_prime_pow_add_not_prime`, a `by_contra` at a fixed `h`).  This lap upgrades the companion
tower to the all-shifts-at-once statement, which is what "prime-free interval" actually means.

Two route corrections, both in the direction of *less* machinery:
1. **The Gauss-type descent `V(c^(k+1)) ≡ V(c^k) (mod c^(k+1))` in the header route is not needed.**
   `lucasV_mul_odd` at `m = c^n` gives the *exact* composition `V(c^(n+d)) = V_(c^d)(V(c^n))`, so
   the single-index certificate closes in one comparison, exactly as in the Fibonacci case.
2. **`lucasV_neg_one_growth` applies verbatim at `c^d`** — it only ever used *odd and ≥ 3* of its
   modulus argument.  So `V_(c^d)(x) − x` is a fixed nonzero integer bounded by `B`, while
   `c^(n/2) > B`; `x ≠ 0` comes from `V(c^n) ≡ P ≢ 0 (mod c)`.

## Exact next steps
1. `DIRECTION.md` still lists phase 41 as CURRENT — an **altitude lap owns** marking it DONE and
   picking the next target.  This lap deliberately left it untouched.
2. **Roadmap §1 Theorem B** (2×2 traces, odd `c`, `det ≡ ±1`): `covering_of_mech` +
   `prime_free_of_good` are now the whole assembly; only the certificate is missing.
3. **Roadmap §1 Theorem A** (order `d`, inert primes; Tribonacci): the engine is `d`-generic now
   (`covering_of_good` takes any `Fin d` matrix), so again only the certificate is missing.  The
   `d ≥ 3` wall recorded in the previous handoff is unchanged and still sharp.
4. `c = 5` for the **Lucas** sequences (the ramified case `c ∣ D`) remains untouched.

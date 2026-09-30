# Map: composite values of `u(c^n) + h`, proved with the prime as its own modulus

One page, one row per theorem.  Everything here was proved 2026-09-29/30, unconditionally, in `src/LeanFormalizations/NumberTheory/Mills/`.

## The method in two lines
1. **Filter** (`SharedConjecture.exists_trace_pow_congr`, `SaitoFibonacci.exists_entry_pow_congr`).  Suppose `u(c^n) + h = p` is prime, where `u(N)` is an entry or the trace of `A^N` and `A` is an integer matrix.  Unless the `c`-part of `|GL(𝔽_p)|` exceeds `c^n`, `p` divides a later term.  So if every late term is prime, `p_n ≡ ±1 (mod c^(~n/2))` (for 2×2 matrices).
2. **Kill the `±1` escape** in one of two ways:
   - by a **sign flip** (inert primes: Frobenius swaps the eigenvalues and negates the entry);
   - by an **exact composition** `u(cN) = Φ(u(N))`, which turns the congruences into an integer equation `Φ(x) ∈ {x, x ± 2}` with no admissible solution.

## Theorems

| Sequence | Base `c` | `h` | Lean | Mechanism |
|---|---|---|---|---|
| Fibonacci `F(2^n)`: **Saito's Problem 1.8** (arXiv:2504.14968) | 2 | all | `SaitoFibonacci.fib_two_pow_add_not_prime` | sign flip |
| Lucas `U(P,Q)`, `P, Q` odd | 2 | all | `LucasTwoPow.lucasU_two_pow_add_not_prime` | sign flip |
| Fibonacci | inert (`c ≡ ±2 mod 5`), and `c = 5` | all | `FibonacciPrimePow.fib_prime_pow_add_not_prime`, `fib_five_pow_add_not_prime` | sign flip; `5^n ∣ F(5^n)` plus `F(4k+1) ± 1` factorizations |
| Lucas numbers `L`, and `V(P,−1)` with `c ∤ P` | every odd prime | all | `LucasPrimePow.lucas_prime_pow_add_not_prime`, `lucasV_prime_pow_add_not_prime` | exact composition `V_(cm) = V_c(V_m, −1)` |
| **Fibonacci** | **every prime** | **all** | `FibonacciAllPrimes.fib_prime_pow_add_not_prime_all` | composition `F((2j+1)N) = Φ_j(F N)` |
| Lucas `U(P,Q)`, any `Q` | odd, inert in `ℚ(√(P²−4Q))` | all | `LucasInert.lucasU_prime_pow_add_not_prime` | sign flip |
| Lucas `U(P,±1)` | odd, `c ∤ D` | all | `LucasUnitAllPrimes.lucasU_unit_prime_pow_add_not_prime` (phase 38, in progress) | composition |

## Where it stops (Maze rows, `src/LeanFormalizations/Maze.lean`)
- **Traces at `c = 2`**: `L(2^n)` (`h = 0`) and the Fermat numbers are exactly the survivors.  These are the classical open problems, so the method fails precisely where it should.
- **Mills' constant** (cubic trace at `c = 3`, phase 29): the filter forces the Mills primes `→ ±1` in `ℤ₃`, which leaves 6 of 27 residue classes.  The exact recurrence `t_(k+1) = t_k³ − 3b_k t_k + 3e_k` (Saito 2024, (4.3)) is consistent with the limit `(t, b) → (x, e·x)`, i.e. a root `x = ±1` mod 3, so composition does not help.  The unknown second symmetric function `b_k` is exactly Saito's stated obstacle.
- **Saito's Problem 1.7** (every Pisot `α`): `⌊α^R(n)⌋` is a trace, and residual classes survive.
- The 1×1 case `a^(c^n) + h` is olympiad folklore (PEN).

## Pointers
- Write-up for Saito: `FINDING-SAITO-PROBLEM-1-8.md`.
- Sweep and numerics: `SWEEP-PRIME-MODULUS.md`, `scripts/prime-modulus-sweep.py`, `scripts/saito-fibonacci-probe.py`.

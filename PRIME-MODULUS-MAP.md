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
| Lucas `U(P,±1)` | odd, `c ∤ D` | all | `LucasUnitAllPrimes.lucasU_unit_prime_pow_add_not_prime` (phase 38) | composition |
| **2×2 traces**, `det ≡ ±1 (mod c)`, `c ∤ tr·disc` | odd | all, except the `Φ₃`/`Φ₆` classes (proved to be survivors) | `TraceClassification.trace_prime_pow_add_not_prime`, `trace_phi_survivor` (phase 42) | composition mod `c^(n+1)` |

## Prime-free intervals (Dubickas's (D1) for the non-reversible tower `c^n`)

| Sequence | Base `c` | Lean | Phase |
|---|---|---|---|
| `F(2^n)` | 2 | `FibonacciCovering.fib_two_pow_prime_free`, `fib_two_pow_covering` | 40 |
| any `ℓ(A^(c^n))` given good prime factors (the **engine**) | any | `CoveringEngine.covering_of_good`, `prime_free_of_good` | 41 |
| Lucas `V(c^n)(P, −1)`, `c ∤ P` | odd | `CoveringEngine.lucasV_prime_pow_prime_free` | 41 |
| **`F(c^n)`** | **every prime** | `CoveringInstances.fib_prime_pow_prime_free_all` | 41, 43 |
| `U(c^n)(P, ±1)` | odd, `c ∤ D` | `CoveringInstances.lucasU_unit_prime_pow_prime_free` | 43 |

## Infrastructure proved overnight (phases 44–49)
- `TheoremDGround`: stuck lemma, abstract-exponent filter, `GL_d` window (Theorem D Lemmas 2–4).
- `Literature/Saito2025.lean` + `ShiftedMills.xi_shifted_transcendental`: **Theorem E as a Lean edge**, from Saito's Type B + Prop 3.1(iv) (Literature Prop) and our open node `ShiftedTraceRigidity`.
- `ShiftedWindow` (the 3-adic window sub-node), `TeichmullerCongruence` (`A^(c^n)` eventually periodic `c`-adically), `UnipotentTrace` (the mod-3 kill, sub-node R4).
- **`GaussCongruenceProof.gaussCongruenceTrace_holds`: the Gauss/Dold congruence for traces, PROVED.**  This discharges `Literature.GaussCongruenceTrace`, so phase 29 (`mills_threeAdic'`) no longer rests on it.

## Theorem A route (phases 50–52)
- `ExteriorDold` (phase 50): `χ_(A^(p^(k+1))) ≡ χ_(A^(p^k)) (mod p^(k+1))` coefficientwise, via compound matrices; plus `χ_B(B^p) ≡ 0`.
- `OrbitSum` (phase 51): for `χ_A` irreducible mod `c`, `A^(c^(n+d)) ≡ A^(c^n)` and **`Σ_(k<d) A^(c^(n+k)) ≡ tr(A^(c^n))·I (mod c^(n+1))`**, exact even when `c ∣ d` (factorization over the Galois ring).
- **`TheoremA` (phase 52): `entry_prime_pow_add_not_prime`.**  Order-`d` entries `u(c^n) + h` are composite i.o. for every `h`, given: `χ_A` irreducible mod `c`, odd `d`, `μ_(≤d)(ℤ_c) = {±1}`, and `c ∤ u(c^r)` for some `r < d`.  Corollaries: **Tribonacci `T(3^n) + h` and `T(5^n) + h`** (`trib_three_pow_add_not_prime`, `trib_five_pow_add_not_prime`).
- **`TribonacciCovering` (phase 53):** `[T(3^n) − 3, T(3^n) + 3]` contains no prime for every `n ≡ 95 (mod 1980)` (`trib_three_pow_prime_free`, `trib_three_pow_prime_free_often`).  Certificate primes: 5, 7, 13, 47, 53, 593.

## Paper theorems, not yet in Lean
- **Theorem D** (`PROOF-THEOREM-D.md`): Saito's Problem 1.7 for `R(n) = c^n + s`; every Pisot `α` outside `f ≡ X^d (mod c)` (draft 2 removes the abelian-field exception by a one-automorphism size argument).  Referee pass: Lemmas OK.
- **Theorem E / E+** (`PROOF-THEOREM-E.md`): the least `A` with `⌊A^(3^k + s)⌋` prime `∀k` is **transcendental** for **every `s ≠ 0`** (draft 3e; odd `s` via `g = 2`).  Unshifted Mills (`s = 0`) fails both steps.  Three referee passes, patches applied; ≈72–80%.

## Where it stops (Maze rows, `src/LeanFormalizations/Maze.lean`)
- **Traces at `c = 2`**: `L(2^n)` (`h = 0`) and the Fermat numbers are exactly the survivors.  These are the classical open problems, so the method fails precisely where it should.
- **Mills' constant** (cubic trace at `c = 3`, phase 29): the filter forces the Mills primes `→ ±1` in `ℤ₃`, which leaves 6 of 27 residue classes.  The exact recurrence `t_(k+1) = t_k³ − 3b_k t_k + 3e_k` (Saito 2024, (4.3)) is consistent with the limit `(t, b) → (x, e·x)`, i.e. a root `x = ±1` mod 3, so composition does not help.  The unknown second symmetric function `b_k` is exactly Saito's stated obstacle.
- **Saito's Problem 1.7** (every Pisot `α`).  With `R = c^n` (no shift) the floor is a trace and residual classes survive.  With `R = c^n + s`, Theorem D handles every `α` outside the Mersenne class `f ≡ X^d (mod c)` (with positive conjugate contribution), and Proposition D′ shows that class is invisible to this method for **every** non-reversible `R`.
- The 1×1 case `a^(c^n) + h` is olympiad folklore (PEN).

## Pointers
- Write-up for Saito: `FINDING-SAITO-PROBLEM-1-8.md`.
- Sweep and numerics: `SWEEP-PRIME-MODULUS.md`, `scripts/prime-modulus-sweep.py`, `scripts/saito-fibonacci-probe.py`.

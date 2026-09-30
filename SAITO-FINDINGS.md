# Findings on the open problems in Saito, arXiv:2504.14968

*[ Written by Claude at Trevor Morris's direction.  Lean statements are machine-checked; the items marked "paper proof" have written proofs that no one outside this project has refereed. ]*

K. Saito, *Intervals without primes near an iterated linear recurrence sequence*, [arXiv:2504.14968](https://arxiv.org/abs/2504.14968).

## Problem 1.8: answered (yes, for every `h`)

> Let `F(n)` be the Fibonacci sequence and `h` an arbitrary integer.  Prove or disprove that `F(2^n) + h` is composite for infinitely many `n`.

**Yes.**  If `F(2^n) + h = p` is prime for all large `n`, then Lagrange's theorem in `GL₂(𝔽_p)` forces `p ≡ ±1 (mod 2^(n/2))`.  Separately, `F(2^(n+1)) ≡ −F(2^n) (mod 2^(n+1))`.  Two consecutive terms then give `2h ≡ ±1 ± 1` modulo a growing power of 2, which forces `h = 0`, and `h = 0` is the easy case.
- Write-up: [FINDING-SAITO-PROBLEM-1-8.md](FINDING-SAITO-PROBLEM-1-8.md)
- Lean: [`SaitoFibonacci.fib_two_pow_add_not_prime`](src/LeanFormalizations/NumberTheory/Mills/SaitoFibonacci.lean)

**The same holds more generally, all Lean-checked:**
- `F(c^n) + h` is composite i.o. for **every prime `c`** and every `h` ([`FibonacciAllPrimes`](src/LeanFormalizations/NumberTheory/Mills/FibonacciAllPrimes.lean)).
- The same holds for Lucas sequences: `U(P, Q)` with `P, Q` odd at `c = 2`, and `U(P, ±1)` and `V(P, −1)` at odd `c` ([`LucasTwoPow`](src/LeanFormalizations/NumberTheory/Mills/LucasTwoPow.lean), [`LucasUnitAllPrimes`](src/LeanFormalizations/NumberTheory/Mills/LucasUnitAllPrimes.lean), [`LucasPrimePow`](src/LeanFormalizations/NumberTheory/Mills/LucasPrimePow.lean)).
- **Prime-free intervals** (Dubickas's (D1) from your §1, for the non-reversible tower `c^n`): for every `H`, `[F(c^n) − H, F(c^n) + H]` contains no prime for infinitely many `n` ([`CoveringInstances`](src/LeanFormalizations/NumberTheory/Mills/CoveringInstances.lean)).
- **Order 3:** Tribonacci `T(3^n) + h` is composite i.o. for every `h` ([`TheoremA`](src/LeanFormalizations/NumberTheory/Mills/TheoremA.lean)).

## Problem 1.7: partial

> Find a non-reversible ILRS `R(n)` such that for every Pisot number `α`, especially of degree 3, `⌊α^(R(n))⌋` is composite for infinitely many `n`.

`R(n) = c^n + s`, with `s` large enough in terms of the degree, works for every Pisot `α` whose minimal polynomial is not `≡ X^d (mod c)` (paper proof).  The excluded class is out of reach for this method with *any* non-reversible `R`: a quadratic example such as `α = 2 + √2` at `c = 2` makes every value `≡ −1` to growing `c`-adic precision.  Details: [PROOF-THEOREM-D.md](PROOF-THEOREM-D.md).

## Problem 1.1: not solved

The same argument shows that primes `⌊β^(3^n)⌋` would have to tend to `±1` in `ℤ₃`, which leaves 6 of the 27 residue classes of cubics mod 3.  A trace is Frobenius-invariant, so the sign flip that settles 1.8 is not available.  Details: [FINDING-MILLS-3ADIC.md](FINDING-MILLS-3ADIC.md).

## Related to arXiv:2508.16068 (paper proof)

Combining your Theorem 2.3 and Proposition 3.1 with the method above, the least `ξ > 1` such that `⌊ξ^(3^k + s)⌋` is prime for every `k` is **transcendental for every `s ≠ 0`**.  The case `s = 0` is Mills' constant, and there the method fails exactly as in Problem 1.1.  Details: [PROOF-THEOREM-E.md](PROOF-THEOREM-E.md).

## Everything else
One-page map of every theorem with its Lean name: [PRIME-MODULUS-MAP.md](PRIME-MODULUS-MAP.md).

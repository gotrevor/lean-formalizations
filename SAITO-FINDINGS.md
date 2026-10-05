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

## Problem 1.7: answered outside one residue class

> Find a non-reversible ILRS `R(n)` such that for every Pisot number `α`, especially of degree 3, `⌊α^(R(n))⌋` is composite for infinitely many `n`.

`R(n) = c^n + s` works for every Pisot `α` of degree `d` whose minimal polynomial `f` has `c ∤ f(0)`, as soon as `α^s > d + 1`.  This is **Lean-checked**: [`TheoremDGeneral.floor_pow_prime_pow_add_not_prime_general`](src/LeanFormalizations/NumberTheory/Mills/TheoremDGeneral.lean).
- **Degree 3:** since `κ^5 > 4` for the smallest Pisot number `κ`, `R(n) = c^n + 5` works for **every cubic Pisot `α` with `c ∤ N(α)`**.  For example, `⌊ρ^(c^n + 5)⌋` is composite i.o. for the plastic number `ρ` and every prime `c` (Lean).
- The same holds whenever **some** root is a `c`-unit (`f ≢ X^d (mod c)`), also Lean-checked: [`TheoremDMixed.floor_pow_prime_pow_add_not_prime_full`](src/LeanFormalizations/NumberTheory/Mills/TheoremDMixed.lean).  Paper proof: [PROOF-THEOREM-D.md](PROOF-THEOREM-D.md).  The remaining class `f ≡ X^d (mod c)` is out of reach for this method with *any* non-reversible `R`: `α = 2 + √2` at `c = 2` makes every value `≡ −1` to growing `c`-adic precision.

## Problem 1.1: not solved

The same argument shows that primes `⌊β^(3^n)⌋` would have to tend to `±1` in `ℤ₃`, which leaves 6 of the 27 residue classes of cubics mod 3.  A trace is Frobenius-invariant, so the sign flip that settles 1.8 is not available.  Details: [FINDING-MILLS-3ADIC.md](FINDING-MILLS-3ADIC.md).

## Related to arXiv:2508.16068

Combining your Theorem 2.3 and Proposition 3.1 with the method above, the least `ξ > 1` such that `⌊ξ^(3^k + s)⌋` is prime for every `k` (indexed from where the ratios are `≥ 2`) is **transcendental for every `s ≠ 0`**.  This is **Lean-checked**, with the existence of `ξ` taken as given:
- from your Theorem 2.3 / Proposition 3.1 as a stated hypothesis: [`ShiftedMillsAll.xi_shift_transcendental`](src/LeanFormalizations/NumberTheory/Mills/ShiftedMillsAll.lean);
- or from Baker–Harman–Pintz and Dubickas's Lemma 6 alone, re-proving the needed case of your reduction.  For this family the step that uses Dubickas's Lemma 8 (your Lemma 5.14) is replaced by the Skolem–Mahler–Lech theorem for order-3 recurrences: [`SaitoTypeB.xi_shift_transcendental_classical`](src/LeanFormalizations/NumberTheory/Mills/SaitoTypeB.lean).
- The prime input can be any short-interval exponent `θ < 5/9`, e.g. Heath-Brown–Iwaniec's `θ > 11/20` ([`SaitoTypeBTheta.xi_shift_transcendental_of_shortInterval'`](src/LeanFormalizations/NumberTheory/Mills/SaitoTypeBTheta.lean)).  Up to `θ < 2/3` it holds using Dubickas's Lemma 8 and conditionally on a hit-prime statement for Pisot numbers of degree `≥ 4`, where explicit quartics satisfy every 3-adic constraint ([`ShiftHitPrime`](src/LeanFormalizations/NumberTheory/Mills/ShiftHitPrime.lean)).

The key step is Galois rigidity in the cubic Pisot case ([PROOF-THEOREM-E.md](PROOF-THEOREM-E.md)).

The case `s = 0` is Mills' constant, and there the method fails exactly as in Problem 1.1.

## Paper draft
All of the above with proofs, in one place: [`paper/prime-towers.tex`](paper/prime-towers.tex) (draft 3, not yet refereed by a human).

## Everything else
One-page map of every theorem with its Lean name: [PRIME-MODULUS-MAP.md](PRIME-MODULUS-MAP.md).

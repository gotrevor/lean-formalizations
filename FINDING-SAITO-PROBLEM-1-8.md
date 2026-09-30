# Saito's Problem 1.8: `F(2^n) + h` is composite for infinitely many `n`

**Problem** (K. Saito, *Intervals without primes near an iterated linear recurrence sequence*, [arXiv:2504.14968](https://arxiv.org/abs/2504.14968), Problem 1.8):

> Let `(F(n))` be the Fibonacci sequence.  Let `h` be an arbitrary integer.  Prove or disprove that the numbers `F(2^n) + h` are composite for infinitely many `n`.

**Answer: proved, for every integer `h`.**  The proof is elementary and has been checked in Lean 4 / mathlib with no additional hypotheses:
[`src/LeanFormalizations/NumberTheory/Mills/SaitoFibonacci.lean`](src/LeanFormalizations/NumberTheory/Mills/SaitoFibonacci.lean), theorem `fib_two_pow_add_not_prime`:

```lean
theorem fib_two_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (2 ^ n) : ℤ) + h)
```

## Proof

Write `A = [[1,1],[1,0]]`, so `A^N = [[F(N+1), F(N)], [F(N), F(N−1)]]` and `det A = −1`.  Let `L(m) = F(m−1) + F(m+1)` be the Lucas numbers.

**Odd `h`.**  `2 ∣ F(m)` iff `3 ∣ m`, so `F(2^n)` is odd.  Then `F(2^n) + h` is even and eventually larger than 2.

**`h = 0`.**  `F(2^n) ∣ F(2^(n+1))`, and `1 < F(2^n) < F(2^(n+1))` for `n ≥ 2`.

**Even `h ≠ 0`.**  Suppose, for contradiction, that `p_n := F(2^n) + h` is prime for all `n ≥ n₀`.

1. **The prime is its own modulus.**  Fix a large `n` and set `p = p_n`.  Suppose `v₂|GL₂(𝔽_p)| ≤ n`.  Then `B = A^(2^n) mod p` has odd order `d`, so there is a `j ≥ 1` with `2^j ≡ 1 (mod d)`, and hence `B^(2^j) = B`.  Reading off the `(0,1)` entry gives `F(2^(n+j)) ≡ F(2^n) ≡ −h (mod p)`.  So `p` divides `p_(n+j)`, which is a prime larger than `p`.  That is a contradiction, so `v₂|GL₂(𝔽_p)| > n`.

2. **So `p_n ≡ ±1` 2-adically.**  We have `|GL₂(𝔽_p)| = p(p−1)²(p+1)`, and for odd `p` one of `v₂(p−1)`, `v₂(p+1)` equals 1.  So step 1 gives `p_n ≡ ±1 (mod 2^⌊n/2⌋)`.

3. **The sign flip.**  `F(2^(n+1)) + F(2^n) = F(2^n)·(L(2^n) + 1)`.  From `L(2^(n+1)) + 1 = (L(2^n) − 1)(L(2^n) + 1)` and `L(2^n) ≡ 3 (mod 4)` we get `2^(n+1) ∣ L(2^n) + 1` for `n ≥ 1`.  Therefore
   `F(2^(n+1)) ≡ −F(2^n) (mod 2^(n+1))`.

4. **Contradiction.**  Add step 2 at `n` and at `n+1`, and use step 3: `s + s' ≡ 2h (mod 2^⌊n/2⌋)` with `s, s' ∈ {±1}`.  Since `h` is even, `2h ≡ 0 (mod 4)`, which rules out `s + s' = ±2`.  So `s + s' = 0`, and `2^⌊n/2⌋ ∣ 2h` for every large `n`.  That forces `h = 0`.  ∎

## Relation to Saito's own tools

Step 1 is close kin to the argument Saito uses for condition (C4) in the proof of Theorem 1.9(C) of [arXiv:2508.16068](https://arxiv.org/abs/2508.16068) (§2).  There, with `C_k = r^(3^k) − 1`, Euler's theorem with the term `C_m` itself as the modulus gives `C_m ∣ C_k` for `k = mφ(C_m) + m`.  That works because `3^m` is invertible mod `C_m`.  Here the exponent's prime (2) may divide the relevant group order, and that is the obstruction.  What is new is handling it: step 1 converts the obstruction into the 2-adic condition `p ≡ ±1`, and the sign flip (step 3) makes that condition contradictory.

## Why this does not reach Problem 1.1 / 1.7

Step 1 is the general "the prime is the modulus" argument.  It applies to any sequence read off `C^(c^n)` for an integer matrix `C` and a prime `c`: a prime value `p` forces `v_c|GL(𝔽_p)|` to be large, hence `p ≡ ` a root of unity `c`-adically.

What is special to Fibonacci is step 3, and it holds because `F(N)` is a matrix **entry**.  The entry flips sign 2-adically (`A mod 2` has order 3, so `A^(2^n)` alternates between two limit points).

The sequences in Problems 1.1 and 1.7, and the Fermat numbers, are **traces**, such as `⌊β^(3^n)⌋ = tr C^(3^n)` (+0 or −1).  A trace is invariant under Frobenius.  By the Gauss congruence it converges `c`-adically, and the limit can sit at `±1`.  For Mills' constant (`c = 3`, cubic Pisot `β`) the same argument therefore only shows that the Mills primes tend to `±1` in `ℤ₃`, which leaves 6 of the 27 residue classes of cubics mod 3.  See `FINDING-MILLS-3ADIC.md` and `NumberTheory/Mills/ThreeAdic.lean`.

As a consistency check, the Lucas analogue `L(2^n) + h` escapes the argument exactly at `h ∈ {0, 2}`.  `L(2^n) + 2 = L(2^(n−1))²` is composite, and `L(2^n)` itself is a Fermat-type open problem.

## Extension: every Lucas sequence with `P, Q` odd

The same proof works for every Lucas sequence `U_N(P,Q)` (`U₀ = 0`, `U₁ = 1`, `U_(N+2) = P U_(N+1) − Q U_N`) with `P, Q` odd and `|U(2^n)| → ∞`.  It is also checked in Lean: [`NumberTheory/Mills/LucasTwoPow.lean`](src/LeanFormalizations/NumberTheory/Mills/LucasTwoPow.lean), theorem `lucasU_two_pow_add_not_prime`.  The sign flip becomes `V(2m) = V(m)² − 2Q^m` with `Q^(2^n) ≡ 1 (mod 2^(n+2))`.

## Extension: every prime base

For **every prime `c` and every integer `h`**, `F(c^n) + h` is composite for infinitely many `n`: [`NumberTheory/Mills/FibonacciAllPrimes.lean`](src/LeanFormalizations/NumberTheory/Mills/FibonacciAllPrimes.lean), theorem `fib_prime_pow_add_not_prime_all`.
- For `c ≡ ±2 (mod 5)`, the same sign flip works: `F(c^(n+1)) ≡ −F(c^n) (mod c^(n+1))`.
- For `c = 5`, the fact that `5^n ∣ F(5^n)` together with `F(4k+1) ± 1` factorizations does it.
- For the remaining primes, the exact identity `F((2j+1)N) = Φ_j(F(N))` for odd `N` (`Φ_j` an integer polynomial) turns the 2-adic congruences into an equality `Φ_j(x) ∈ {x, x ± 2}`, which has no nonzero solutions.

The Lucas numbers `L(c^n) + h` are settled for every odd prime `c` the same way (`LucasPrimePow.lean`).  At `c = 2` they are not: `L(2^n)` is a Fermat-type open problem.

## Provenance

The argument was found and formalized by Trevor Morris with Claude (Anthropic), 2026-09-29.  Numerics: `scripts/saito-fibonacci-probe.py`.  Working notes: `PROBE-SAITO-FIBONACCI.md`.

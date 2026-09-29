# PROBE: Saito's Problem 1.8, `F(2^n) + h` composite infinitely often (2026-09-29)

**Source.**  K. Saito, *Intervals without primes near an iterated linear recurrence sequence*, arXiv:2504.14968 (v1, 2025-04-21, still v1 on 2026-09-29).  Problem 1.8 is verbatim: *"Let (F(n)) be the Fibonacci sequence.  Let h be an arbitrary integer.  Prove or disprove that the numbers F(2^n) + h are composite for infinitely many n."*  He poses it because `2^n` is a **non-reversible** LRS, so his Theorem 1.3 (built on Dubickas's periodicity) does not reach it.

**Freshness.**
- `papers followups 2504.14968` returns one citing paper, Saito 2025 (arXiv:2508.16068), and that paper never mentions Fibonacci.
- A web search finds the problem listed as open (emergentmind open-problems index).

## Claim: yes, for every integer `h`

The proof is elementary.  It is the phase-29 mechanism (Lagrange in `GL_2(𝔽_p)`, with the modulus being the prime itself), plus a Fibonacci-specific 2-adic **sign flip** that the Mills and Fermat cases lack.

1. **Odd `h`.**  `F(2^n)` is always odd, since `2 ∣ F(m) ⟺ 3 ∣ m`.  So `F(2^n) + h` is even and eventually `> 2`.

2. **`h = 0`.**  `F(2^n) ∣ F(2^(n+1))`, and `1 < F(2^n) < F(2^(n+1))` for `n ≥ 2`.

3. **Even `h ≠ 0`.**  Suppose `p_n := F(2^n) + h` is prime for all `n ≥ n₀`.
   - **(a) Mechanism.**  Let `A = [[1,1],[1,0]]`, so `F(N) = (A^N)₀₁` and `det A = −1`.
     - If `v₂|GL₂(𝔽_p)| ≤ n` with `p = p_n`, then `B = A^(2^n) mod p` has odd order.  So squaring permutes `⟨B⟩`, and `B^(2^j) = B` for some `j ≥ 1`.
     - Then `p ∣ F(2^(n+j)) − F(2^n)`, hence `p ∣ p_(n+j)`.  This is impossible, since `p_(n+j) > p` is prime.
     - So `n < v₂|GL₂(𝔽_(p_n))|` for all large `n`.
   - **(b) 2-adic form.**  `|GL₂(𝔽_p)| = p(p−1)²(p+1)`.  For odd `p`, one of `v₂(p∓1)` equals 1.  So `n < v₂` gives `2^(n/2) ∣ p − 1` or `2^(n/2) ∣ p + 1`.  That is, `p_n ≡ ±1 (mod 2^(n/2))`.
   - **(c) Sign flip.**  `F(2^(n+1)) + F(2^n) = F(2^n)(L(2^n) + 1)`, and `v₂(L(2^n) + 1) = n + 1` for `n ≥ 1`.  The reason is that `L(2^(n+1)) + 1 = (L(2^n) − 1)(L(2^n) + 1)` and `L(2^n) − 1 ≡ 2 (mod 4)`.  So `F(2^(n+1)) ≡ −F(2^n) (mod 2^(n+1))`.  Checked numerically: `v₂(F(2^(n+1)) + F(2^n)) = n + 1` for `n = 1..12`.
   - **(d) Contradiction.**
     - Adding (b) at `n` and `n+1` and using (c) gives `s + s' ≡ 2h (mod 2^(n/2))` with `s, s' ∈ {±1}`.
     - Since `h` is even, `2h ≡ 0 (mod 4)`.  So `s + s' = 0`, not `±2`.
     - Then `2^(n/2) ∣ 2h` for every large `n`, which forces `h = 0`.

**Why Mills and Fermat resist the same argument while Fibonacci falls.**
- For a trace sequence (`L(2^n)`, Fermat numbers, Mills primes), the Gauss congruence makes the terms *converge* 2-adically (or 3-adically), and the limit can sit at `±1`.  That leaves Fermat-hard residual classes, as in phase 29.
- `F(2^n)` instead *alternates* 2-adically, `F(2^(n+1)) ≈ −F(2^n)`, so it cannot hug `±1 − h` from both sides.
- Sanity check: the Lucas analogue `L(2^n) + h` survives exactly at `h ∈ {0, 2}`.  `L(2^n) + 2 = L(2^(n−1))²` is composite, and `L(2^n)` itself is the Fermat-like open case.  So the trick fails where it must.

## Numerics (`scripts/saito-fibonacci-probe.py`)
- For `h = 2`, `F(8) + 2 = 23` is prime and `23 ∣ F(16) + 2 = 989`, as the `j = 1` mechanism predicts.
- For `h = 4`, `F(16) + 4 = 991` is prime and divides `F(2^(4+30)) + 4`.

## Confidence
90% that the argument is right.  The Lean phase settles it.  Nothing here is Fermat-hard.  The only external input is Lagrange in a finite group, which phase 29 already has.

## Lean plan: phase 32, `NumberTheory/Mills/SaitoFibonacci.lean`
- No `Literature/` hypothesis is needed; the result is unconditional.
- Reuse `glCard` from `ThreeAdic.lean`.
- Adapt `exists_trace_pow_congr` (in `SharedConjecture.lean`) to a matrix entry.  Its proof already shows `D^(c^(m+j)) = D^(c^m)` over `ZMod p`.

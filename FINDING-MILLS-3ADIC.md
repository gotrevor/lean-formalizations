# Finding: a 3-adic obstruction to an algebraic Mills constant

Proved in Lean, phase 29: `src/LeanFormalizations/NumberTheory/Mills/ThreeAdic.lean`.  Working notes and numerics: `PROBE-MILLS-3ADIC.md` and `scripts/mills-3adic-probe.py`.

## The gap in the literature

K. Saito, *Mills' constant is irrational*, arXiv:2404.19461v2.
- Theorem 1.2: Mills' constant ξ is transcendental, or some `β = ξ^(3^m)` is a Pisot number of degree 3.
- Remark 4.4, verbatim (pdftotext of v2, p. 10–11): "To prove the transcendency of Mills' constant, it remains to show that there does not exist m ∈ N such that ξ^{C_m} is a Pisot number of degree 3 when b = 3. In this remark, we describe the difficulty of this case. … (4.3) p_{k+1} = p_k³ − 3b_k p_k + 3e_k … Therefore, we have to investigate properties of b_k and e_k. The author does not have any good ideas on how to treat b_k and e_k simultaneously. Indeed, the method of the proof of Lemma 4.3 does not work."
- Proposition 5.1 extracts the mod-3 content: `p_(k+1) ≡ p_k (mod 3)` eventually.  Saito adds: "it seems to be impossible to classify Mills primes modulo 3."

Saito, arXiv:2504.14968, Problem 1.1: for every cubic Pisot β, are the numbers `⌊β^(3^n)⌋` composite infinitely often?  His periodicity method needs a "reversible" exponent sequence, and `3^n` is not one: `3^n mod L` never returns to 1 once `3 ∣ L`.

## What we proved

Let `C` be a square integer matrix with `det C ≠ 0`, and let `t_k = tr C^(3^k)`.
1. **Unconditional.**  Suppose `t_k` is prime and increasing for all large k.  Then `v₃|GL_n(𝔽_(t_k))| > k` for all large k.  Proof sketch: work mod `p = t_m`.  If the 3-part of `|GL_n(𝔽_p)|` is at most `3^m`, then `g = C^(3^m)` has order prime to 3.  So `3^j ≡ 1` modulo that order, which gives `t_(m+j) ≡ t_m ≡ 0 (mod p)`.  But `t_(m+j)` is a larger prime.
2. **Under the Gauss congruence for matrix traces (Steinlein 2017), entered as a hypothesis Prop.**  `t_k → ±1` in `ℤ₃`.
3. **Mills.**  If the least Mills constant is algebraic, then the Mills primes tend to `±1` in `ℤ₃`.  Equivalently (numerically confirmed; not in Lean), the minimal polynomial of β mod 3 lies in six of the 27 monic classes:
   - `(x−1)²(x+1)` or `(x+1)²(x−1)`;
   - `x²(x∓1)`;
   - `(x∓1)(x²+1)`.

   In Lean this rests on BHP, Matomäki and Dubickas (Saito's inputs) plus the trace congruence.
4. **Contrapositive.**  If for some e infinitely many Mills primes avoid `±1 (mod 3^e)`, then Mills' constant is transcendental.

This is strictly more than Prop. 5.1, since convergence to ±1 implies `p_(k+1) ≡ p_k (mod 3)`.  It also answers "classify Mills primes modulo 3" in the algebraic case: they are eventually `±1 (mod 3^e)` for every e.

## Honest weight

- The core step is one page of elementary group theory.  An expert might call it routine once the modulus is chosen to be the prime itself.  That choice is the whole idea.  My guess: 50% "routine to Saito once shown", 75% not in print.
- **The six residual classes carry the real difficulty.**  In them, `p_m ≡ ±1 (mod 3^(m+1))`, so the 3-Sylow subgroup of `𝔽_p^×` outgrows `3^m`, and the conjugates' 3-parts differ.  So `p_m ∤ p_(m+j)` is expected for every j: the trace sequence behaves like the Fermat numbers.  The modulus-is-the-prime trick has nothing left to say there.

## Burning down the residual classes: small-prime covering (not in Lean)

For a prime `q ≠ 3`, `t_k mod q` is eventually periodic, and whether the cycle contains 0 depends only on f mod q.  If it does, `t_k` is composite infinitely often.  Share of monic cubics mod q killed this way (`covering` check):

| q | killed | surviving product |
|---|---|---|
| 2 | 5/8 | 0.375 |
| 5 | 65/125 | 0.180 |
| 7 | 193/343 | 0.079 |
| 11 | 621/1331 | 0.042 |
| 13 | 1033/2197 | 0.022 |

These conditions are CRT-independent of the mod-3 condition.  So if ξ is algebraic, `minpoly β` avoids a set of residue classes whose density tends to 1.  This excludes almost every cubic, but not every one.  (It kills `2·3^(3^k) + 1`: 5 divides it for every odd k.)  A survivor must have its orbit avoid 0 modulo every prime, which is Fermat-like behaviour.  Nothing in this toolkit rules out a Pisot survivor.

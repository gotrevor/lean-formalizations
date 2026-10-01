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

## Extension: track the matrix up to scalars (Astra, 2026-09-29; checked by Ren)

Full argument and limitations: [PROBE-MILLS-PROJECTIVE.md](PROBE-MILLS-PROJECTIVE.md), including the recurrent-divisor version and the growth hypothesis needed to conclude infinitely many composite terms.

**Lemma (written proof, not yet Lean).**  Let q ≠ 3 be prime, and suppose the cubic f stays **irreducible** mod q, q divides `t_m` for some m ≥ 1, and q ∤ N(β).  Then q divides `t_(m+j)` for some j ≥ 1, and hence for infinitely many j.

**Proof.**
1. Mod q, `α = β^(3^m)` lives in `𝔽_(q³)`.  Its image in `𝔽_(q³)^× / 𝔽_q^×` has order d dividing `q² + q + 1`.
2. `v₃(q² + q + 1)` is 1 if q ≡ 1 (mod 3) and 0 if q ≡ 2 (mod 3).  This holds even when q is 3-adically very close to 1, which is exactly where the `GL₃` argument fails.
3. β's projective 3-part is at most 3, and m ≥ 1 kills it, so 3 ∤ d.
4. Take `j = ord_d(3)`.  Then `α^(3^j) = λα` with λ ∈ `𝔽_q^×`, so `Tr α^(3^j) = λ Tr α ≡ 0`.

**Consequences.**
- If Mills' constant is algebraic, f has a root mod `p_k` for every large k.  Equivalently, Frobenius at the Mills primes eventually avoids the 3-cycles.
- **Sharper target.**  One prime q at which f is irreducible and which divides a single `t_m` (m ≥ 1) makes `t_k` composite infinitely often.  So the six classes are eliminated for any β that has such a q.  Chebotarev supplies plenty of irreducible primes, but nothing forces one to divide this sparse sequence: the same Fermat-type wall as before, only narrower.

**Numerics.**  The `projective` check (`scripts/mills-3adic-probe.py`) found 47 irreducible prime moduli q | `t_m`, and all 47 divide `t_(m+j)` for the predicted j.  In 5 of them the `GL₃` argument is silent, because the 3-part is too big.

**Status.**  Correct, 95%.  It does not eliminate the six classes.  It restricts which primes can be Mills primes, and it gives a one-prime certificate for each individual β.

## Follow-up (2026-09-30): the Kronecker lemma and the hard core

[PROBE-MILLS-RESIDUAL.md](PROBE-MILLS-RESIDUAL.md).  A split prime `T_j ≡ 2 (mod 3)` recurs, so in the three classes with `Tr β ≡ 2 (mod 3)` every large Mills prime has type (1)(2) in K: `(D/p_k) = −1`, a finite congruence check on f, and K cannot be cyclic.  The filter is not Mills-specific, so it is a burn-down, not a mechanism.  The hard core is `τ = +1` with K an S3 field, where no abelian filter exists.  Least-ness, the only Mills-specific lever, is gap-bound limited.

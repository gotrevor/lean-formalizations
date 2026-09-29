# Mills residual classes: projective recurrence

Research note, 2026-09-29.  Derived by Codex/Ren after reading `Maze.lean`, `PROBE-MILLS-3ADIC.md`, `FINDING-MILLS-3ADIC.md`, and Saito 2025 v3.  This is a written mathematical argument, not a Lean result.  Confidence in the lemma: 95%; novelty unassessed.

## The proposed extension

Let f be a monic cubic over Z with companion matrix C, and set t_k = tr(C^(3^k)).  Suppose the t_k are strictly increasing positive primes for all k >= k0.  Then for every k >= max(k0, 1) with t_k != 3, f has a root modulo t_k.

This applies to the eventual trace representation of the algebraic Mills branch.  It adds a splitting restriction at the moving primes t_k.  It does not eliminate any entire one of the six coefficient classes modulo 3.

The useful change is to remember that trace zero is preserved under nonzero scalar multiplication.  Recurrence of the matrix itself is sufficient but unnecessary: recurrence of its projective class suffices.

## Proof

Suppose p = t_k != 3 is prime and f mod p is irreducible.  The algebra F_p[C] is then F_(p^3), with C corresponding to a nonzero element alpha.  Thus the image of C in the quotient F_(p^3)^*/F_p^* has order d dividing

    Q = p^2 + p + 1.

If p = 2 mod 3, Q = 1 mod 3.  If p = 1 mod 3, writing p = 1 + 3u gives

    Q = 3(1 + 3u + 3u^2),

so v_3(Q) = 1.  Consequently v_3(d) <= 1 in either case.  Since k >= 1, the projective class of g = C^(3^k) has order D prime to 3.

Choose j >= 1 with 3^j = 1 mod D; j = phi(D) works, including D = 1.  There is a lambda in F_p^* such that

    g^(3^j) = lambda g.

Taking matrix traces gives

    t_(k+j) = lambda t_k = 0 mod p.

But t_(k+j) > t_k = p, contradicting its primality.  Therefore f mod p is reducible, which for a cubic is equivalent to having a root.

The same argument proves a more general local recurrence lemma: if f mod q is irreducible, q != 3 is prime, and q divides t_k for some k >= 1, then q divides t_(k+rj) for every r >= 0 for a suitable j >= 1.  If the traces tend to positive infinity, this forces infinitely many composite terms.  This version needs no primality assumption on the initial t_k.

## Why the existing obstruction does not give this directly

For an irreducible cubic at p, the scalar part of F_(p^3)^* has order p-1.  Its 3-part can be arbitrarily large when p approaches +1 in Z_3.  Removing scalar matrices replaces p^3-1 by p^2+p+1, whose 3-part is at most 3.  The old bound on the order of GL_3(F_p) retains that irrelevant scalar obstruction.

This is not a universal replacement of GL_3 by a small group: the projective order can still have a large 3-part for split or linear-times-quadratic reductions.  The irreducibility hypothesis does real work.

## The new missing step

A sufficient next theorem would be: for every totally real cubic Pisot beta satisfying Saito's restrictions, some prime q != 3 for which f mod q is irreducible divides tr(beta^(3^k)) at some k >= 1.  More modestly, characterize when such a prime divisor exists, and identify a family where it can be forced.

This is a precise target, not a theorem claimed here.  Chebotarev supplies irreducible reductions among rational primes, but does not say those primes divide this sparse trace subsequence.  Likewise, under the assumption that the trace sequence is eventually prime, it does not force any t_k to be one of those irreducible-reduction primes.

The splitting restriction leaves completely split and linear-times-quadratic primes.  Nothing here prevents all eventual t_k from taking those types.  In a cyclic cubic field the unramified survivors must split completely, but that is still not a contradiction.

## Other routes, and limits

- Higher precision at 3 alone cannot remove a class whose Teichmueller trace is exactly +1 or -1.  These are infinite coefficient families, not six individual candidate numbers.
- The real-place restrictions are essential to a Mills-specific route.  Saito's Theorem 1.7 gives |beta_3| < -beta_2 <= min(|beta_3|^(17/23), beta^(-17/40)).  His accompanying remark supplies infinitely many totally real cubic Pisot examples satisfying those inequalities.  The inequalities alone therefore do not close the problem.
- A second sufficient target is a prime between p_k^3 and p_(k+1) for some sufficiently late k in the hypothetical algebraic branch.  The remaining analytic obstacle is hitting these particular sparse intervals, even after imposing their 3-adic structure.  Saito's Theorem 1.8 closes this under DH, hence RH.
- The finite covering table in FINDING-MILLS-3ADIC.md does not by itself establish its subsequent assertion that the killed density tends to 1 as more primes are included.  That needs an infinite-product estimate.  Even a proved density-one exclusion would still leave exceptional cubics.

Source checked: Kota Saito, *Transcendency of variants of Mills' constant*, arXiv:2508.16068v3, Theorems 1.7 and 1.8, https://arxiv.org/html/2508.16068v3 .  The older v2 does not contain the same Mills conclusion, so use v3.

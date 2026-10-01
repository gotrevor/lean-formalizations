# Probe: Erdős #385 / #430 (composites just below n with large least prime factor)

Opened 2026-09-30.  Status: **wish list, no phase planted.**

## The problem

`F(n) = max{ m + p(m) : m < n composite }`, `p(m)` = least prime factor.

- **#385(i)**: is `F(n) > n` for all large `n`?  (#430 is equivalent, per Adenwalla: #430's sequence
  is exactly the `m < n` with `p(m) > n − m`, listed downward.)
- **#385(ii)**: does `F(n) − n → ∞`?  Variant: `F(n) ≥ n + (1 − o(1))√n` (trivially `≤ n + √n`).
- Formal statements: formal-conjectures `ErdosProblems/385.lean` (parts i, ii, variant lb).  #430 is
  not in formal-conjectures.

Equivalent forms worth keeping:

1. `n` is **bad** (`F(n) ≤ n`) iff no `a ≥ 1` has `n − a` composite with `p(n − a) > a`.
2. Via `m = p·⌊n/p⌋`: `n` is good iff some prime `p` with `p ∤ n`, `p² < n` has `⌊n/p⌋` free of
   primes `< p`.  The "largest multiple of `p` below `n` has least prime factor `p`" form.
3. `a = 1` covers every `n` with `n − 1` composite, so **bad ⇒ n − 1 prime** (so `n` is even).

## What is already known (read before re-deriving)

- **Tao, "Erdős problem #385, the parity problem, and Siegel zeroes"** (blog, 2024-08-19).  Badness
  means: for every `h`, the classes `0 mod p` (`p ≤ h`) cover `[n − h, n]` except primes.
  - `h > √n` is automatic.
  - `h = o(log n)` is defeated by `n ≡ 0 mod ∏_{p≤h} p` with `n − 1` prime (Linnik).
  - So the fight is at `log n ≪ h ≪ √n`.  The key case is `h = n^{1/u}`, `2 < u < 3`, where the
    survivors are primes plus semiprimes with both factors in `[n^{1/u}, n^{1−1/u}]`.
  - "Semiprime gaps `o(x^{1/u})`" would settle both parts.  That is a semiprime Cramér statement,
    out of reach even on RH.
  - Sieve methods are parity-blocked.  A **Siegel zero** gives a coherent across-all-scales
    scenario in which small primes already wipe out `[n − h, n]`.  So he expects no proof without
    a parity breakthrough that at minimum excludes Siegel zeroes.
  - His one stated loophole is a "repulsion" between scales `h, h'`, which he does not see how to
    realise.
- **Computation**: OEIS A322293 lists the bad `n`.  There are 100 (Marcus/Israel to `10^8`), the
  largest **267680**.  CKS (Tao blog comments) found the last three and the "bad ⇒ `q + 1`, `q`
  prime" reduction.  erdosproblems forum: no further bad `n` to `10^11` (Leandre Jack, 2026-09-03),
  then to `1.0011·10^12` (Aleksanndr_NFA, 2026-09-23).  Min `F(n) − n` per shard grows,
  `≈ 0.9√n` beyond `10^11`.
- erdosproblems reactions: Tao marked "Looks difficult".

`scripts/erdos385-probe.py` independently reproduces A322293 to `10^7`: 100 bad `n`, all `q + 1`.
It also tracks the first good distance `g(n)` (record 131 at `n = 33630`) and `min (F(n) − n)/√n`
per dyadic block (0.33 near `5·10^6`).

## Difficulty check (feedback_difficulty_locus)

- **Proved implications**: #430 ⟺ #385(i).  Bad ⇒ `n − 1` prime.  A semiprime-gap hypothesis at
  any `u ∈ (2,3)` ⇒ #385(i) and (ii).
- **Unproved premise**: semiprime gaps (both factors `≥ x^{1/u}`) are `o(x^{1/u})`.
- **Mechanism for the premise**: none known.  The known-false sibling is already in Tao's post.
  Covering an *arbitrary* interval of length `h` by one class per prime `≤ h` IS possible
  (Jacobsthal, FGKMT eq. 1.2).  So any argument that uses only sieve axioms is dead on arrival; it
  must exploit that the classes are `0 mod p` at the specific location `n`.  Any proposed lever
  gets tested against that sibling first.

## Doors worth knocking on (ranked; none planted)

1. **Function-field analogue in `F_q[T]`, where Siegel zeroes cannot exist (Weil).**  Tao names the
   Siegel zero as *the* enemy and says it is not clear it is the only one.  In `F_q[T]` the parity
   barrier has been broken: Sawin–Shusterman for twin primes, Bank–Bary-Soroker–Rosenzweig for
   primes in short intervals as `q → ∞`.  Statement: for monic `f` of large degree, is there a
   composite `g` with every irreducible factor of degree `> deg(f − g)`?
   - The large-`q` limit should be a corollary of BBR-type equidistribution of factorization types
     in short intervals (cycle type `(k, d − k)` with `k > h` has positive density), ~70%.
   - The fixed-`q` case is the real question.  It would say whether Siegel zeroes are the only
     enemy, which is new information either way.
   - First step: a literature search for an existing function-field #385.  Not yet done.
2. **Quantitative exceptional set.**  Trivially `#{bad n ≤ X} ≤ π(X)`.  Sketch:
   - Each position `a ≤ A` forces either a congruence `n ≡ a (mod q)` for some `q ≤ a`, or
     `n − a` prime.
   - An upper-bound (Brun/Selberg) sieve over residue classes mod `∏_{q≤A} q`, with
     `A ≍ B log log X`, should give `≪_B X/(log X)^B`.  A Jacobsthal-type count of the residue
     classes that cover `[2, A]` would push it further.
   - Modest but plausibly new, ~55%.  Elementary enough for Lean, since mathlib has a Selberg
     sieve.  ⚠️ This is an almost-all statement.  It cannot reach finiteness, because the Siegel
     scenario is a measure-zero enemy.
3. **Repulsion between scales** (Tao's loophole).  Form 2 couples scales through one `n`: bad means
   every `⌊n/p⌋` has a prime factor `< p`.  A provable inverse statement would be: "bad `n` with
   no semiprime at scale `h` forces a structured residue pattern at scale `h²`".  Speculative, no
   mechanism, ~10%.  Test on the 100 known bad `n` before theorizing.  The two largest,
   `267672 = 2³·3·19·587` and `267680 = 2⁵·5·7·239`, show no primorial structure.

Not a door: more computation.  `10^12` is done and cannot settle an "eventually" question.

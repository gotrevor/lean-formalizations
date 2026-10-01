/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional
import LeanFormalizations.NumberTheory.Erdos385.Graph

/-!
# Erdős #385: the exceptional-set bound for bad `n` (phase E4, new mathematics)

One frozen statement, `badCountExpBound_of_lit`: from the arithmetic large sieve, the linear-sieve
lower bound and McDiarmid's inequality,
`#{bad n ≤ X} ≪_ε X exp(−(log X)^{1/2−ε})` (`Erdos385.BadCountExpBound`, `Graph.lean`).
No zeros of `ζ` are used, and the exponent `1/2` beats the `1/3` of the almost-all route
(`RateVK.lean`) on the narrower set of bad `n`.  Unpublished as far as we know (60%).

The outline is `DOOR-EXCEPTIONAL-ERDOS-385.md` §A2 on `main` (75% that it closes; constants
unchecked).  A lap that finds a gap has made progress: name the failing step as a sub-lemma and
record why it fails.

## Route

Work on a dyadic block `n ∈ (X/2, X]`, then sum blocks.  Set `y = ⌊(1/4) log X⌋` (so
`primorial y ≤ X^{1/3}`, by Chebyshev) and `Q = ⌊X^{1/3}⌋`.  Condition on `s = n mod primorial y`.
Let `U(s) = {a ∈ [1, y] : n − a has no prime factor ≤ a}` (depends only on `s`); `u(s) = |U(s)|`.

1. **Forbidden classes** (elementary, from `Rigidity.lean`'s `bad_iff_forall_sub`).  For bad `n`,
   each prime `q ∈ (y, Q]` and each `a ∈ U(s) ∪ {1}`: `n ≢ a (mod q)`.  Otherwise `q ∣ n − a`,
   `n − a > q > a`, so `n − a` is composite with `minFac > a`, contradicting badness.  Distinct `a`
   give distinct classes since `a ≤ y < q`.
2. **Large sieve** on `m` with `n = s + primorial(y)·m`, `m ≤ X / primorial y`, classes transported
   through the unit `primorial y mod q`.  Keep `K = min(u(s)+1, ⌈c y/log y⌉)` classes per prime and
   restrict the sum `L` to squarefree `d` that are products of `j = ⌈(log X)^{1/2}⌉` distinct primes
   in `(y, Q^{1/j}]`; then `L ≥ (e K Σ1/p / j)^j/…` gives `L ≥ exp((log X)^{1/2})` when
   `u(s) + 1 ≥ c y/log y` (Mertens on `(y, Q^{1/j}]`: `Σ 1/p ≥ (1/3) log log X`).
3. **Tail of `u(s)`.**  With `z = y^{1/2−ε}`: by `LinearSieveIntervalLower`, the positions
   `T ⊂ (y/2, y]` not blocked by the residues `s mod q`, `q ≤ z`, number `≥ c y/log y`, for every
   choice of those residues.  The residues for `q ∈ (z, y]` are independent and uniform (CRT on
   `ZMod (primorial y)`).  `Y` = positions of `T` blocked by none of them; `E Y ≥ |T| ∏(1 − 1/q)
   ≫ y/log y`; changing `s mod q` moves `Y` by `≤ 2(y/q + 1)`; `McDiarmidFinite` gives
   `P(Y < E Y / 2) ≤ exp(−c y^{1/2−ε}/log y)`; and `u(s) ≥ Y`.
4. **Sum**: `#{bad n ∈ (X/2, X]} ≤ X·P(u small) + Σ_{s} (X/primorial y + Q²)/L
   ≪ X exp(−c (log X)^{1/2−ε}) + X exp(−(log X)^{1/2})`; dyadic blocks sum geometrically.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph
and a confidence; that is an acceptable finish.

Frozen: this statement, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **The bad set is exponentially thin** (DOOR-EXCEPTIONAL A2). -/
theorem badCountExpBound_of_lit (h1 : ArithLargeSieve) (h2 : LinearSieveIntervalLower)
    (h3 : McDiarmidFinite) : BadCountExpBound := by
  sorry

end LeanFormalizations.Erdos385

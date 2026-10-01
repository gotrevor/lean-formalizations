/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Rigidity

/-!
# Erdős #385: the hyperbola criterion and the binary reformulation (phase E9a)

A witness for `n` (a composite `m < n` with `m + p(m) > n`) is determined by its least prime
factor `p`: `m` is the largest multiple of `p` below `n`, so `m = p ⌊n/p⌋` and `p ∤ n`.  Hence:

* `good_iff_exists_prime_floor`: for `n ≥ 5`, `n` is good iff some prime `p` with `p ∤ n` has
  `p ≤ ⌊n/p⌋` and `minFac ⌊n/p⌋ ≥ p`;
* `good_of_prime_pair`: primes `p < q` with `pq < n < pq + p` make `n` good (the case
  `⌊n/p⌋ = q` prime);
* `HyperbolaPrimePairs`, `eventually_not_bad_of_hyperbolaPrimePairs`, `erdos430_of_hyperbolaPrimePairs`:
  if prime pairs on the strip `pq < n < pq + p` exist for all large `n`, then #385(i) and #430
  hold.

**Why the reformulation matters (direction, not a result).**  Near `p ≈ √n` the map
`p ↦ ⌊n/p⌋` is a reflection, `⌊n/p⌋ = 2A + c(p) − p` with `A = ⌊√n⌋` and `c` a slowly increasing
step function.  So `HyperbolaPrimePairs` is a Goldbach problem: some even `2A + 2j` must be
`p + q` with `p` in a window of length `≍ √A/√j` placed at distance `≍ √(Aj)` below `A`.  That is
a binary problem, which is why #385(i) resists every method (Maze row "for every n via the
hyperbola prime pairs").

**Evidence** (`scripts/erdos385-hyperbola-probe.py`, checks against the definition of `F` on
`[5, 20000]` and against the known bad `n` 267672, 267680): the prime-pair count
`W(n) = #{(p, q) : p < q primes, pq < n < pq + p}` vanishes for 491 values `n ≤ 10^8`, the
largest being `267689`, nine above the last bad `n`; `min W = 7` on `[10^6, 10^7)` and `27` on
`[10^7, 10^8)`, and the mean of `W` tracks `3.9 √n / log² n`.  So prime pairs alone, the binary
witnesses, already cover every `n` from just past the last bad one.

Frozen: these statements.  `good_iff_exists_prime_floor` and `good_of_prime_pair` are elementary
(use `bad_iff_forall_sub`, `add_minFac_le_F`, `Nat.minFac_le_of_dvd`).
-/

namespace LeanFormalizations.Erdos385

open Filter

/-- **The hyperbola criterion.**  `n ≥ 5` is good iff some prime `p ∤ n` has `⌊n/p⌋ ≥ p` with no
prime factor below `p`; the witness is `m = p ⌊n/p⌋`. -/
theorem good_iff_exists_prime_floor {n : ℕ} (hn : 5 ≤ n) :
    ¬ Bad n ↔ ∃ p, p.Prime ∧ ¬ p ∣ n ∧ p ≤ n / p ∧ p ≤ (n / p).minFac := by
  sorry

/-- **Prime-pair witnesses.**  Primes `p < q` with `pq < n < pq + p` make `n` good. -/
theorem good_of_prime_pair {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (h1 : p * q < n) (h2 : n < p * q + p) : ¬ Bad n := by
  sorry

/-- **Prime pairs on the hyperbolic strip, eventually** (a binary problem; open).  Believed: the
expected count is `≍ √n / log² n`, and the data above show no failure past `267689`. -/
def HyperbolaPrimePairs : Prop :=
  ∀ᶠ n in atTop, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p * q < n ∧ n < p * q + p

/-- Edge: prime pairs on the strip give #385(i). -/
theorem eventually_not_bad_of_hyperbolaPrimePairs (h : HyperbolaPrimePairs) :
    ∀ᶠ n in atTop, n < F n := by
  sorry

/-- Edge: prime pairs on the strip give #430 (via `erdos430_iff_erdos385_i`). -/
theorem erdos430_of_hyperbolaPrimePairs (h : HyperbolaPrimePairs) :
    ∀ᶠ n in atTop, ¬ ∀ m ∈ terms n, m.Prime := by
  sorry

end LeanFormalizations.Erdos385

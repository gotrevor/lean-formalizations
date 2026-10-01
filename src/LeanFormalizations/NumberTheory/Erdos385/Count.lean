/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Erdos385
import LeanFormalizations.NumberTheory.Erdos385.Rigidity

/-!
# Erdős #385: the elementary count of bad `n` (phase E2, frozen, not yet the active phase)

`DOOR-EXCEPTIONAL-ERDOS-385.md` A1 (90% correct as stated): `#{bad n ≤ X} ≪ X log log X / log² X`.

## Frozen statement

* `card_bad_le`, from `Literature.BrunUniformGap`.

## Route

Pick `y` with `y# ≥ (log X)²` (so `y ≍ log log X`, Chebyshev: mathlib's `primorial_le_4_pow`
bounds the other side).  By `primorial_dvd_or_exists_prime_pair_of_bad`, a bad `n ≤ X` with
`n ≥ y + 2` is either a multiple of `y#` (at most `X / y# + 1 ≤ X / log² X + 1` of them) or has
`n − p`, `n − 1` both prime for a prime `3 ≤ p ≤ y`: a prime pair at gap `h = p − 1`, at most
`C (h/φ(h)) X / log² X` per `p` by Brun.  Sum over the primes `p ≤ y`: with
`h/φ(h) ≪ log log h ≤ log log y` and `π(y) ≪ y / log y`, the total is
`≪ (y / log y) · log log y · X / log² X ≪ X log log X / log² X` (since `y ≍ log log X`).  The crude
`h/φ(h) ≤ h` would lose a factor `y / log log y`, so avoid it.  The `n < y + 2` part is
`O(log log X)`.
-/

namespace LeanFormalizations.Erdos385

open Real LeanFormalizations.Literature

theorem card_bad_le (hB : BrunUniformGap) :
    ∃ C : ℝ, ∀ X : ℕ, 16 ≤ X →
      ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ)
        ≤ C * X * Real.log (Real.log X) / Real.log X ^ 2 := by
  sorry

end LeanFormalizations.Erdos385

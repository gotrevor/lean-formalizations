/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMills

/-!
# Phase 46: the 3-adic window for prime traces along `3^n − 2` (first sub-node of `ShiftedTraceRigidity`)

`PROOF-THEOREM-E.md` Step 3 in Lean, for an arbitrary `3 × 3` integer matrix.  If
`tr C^(3^n − 2)` is prime for all large `n` (and grows), then for all large `n` it is `≡ ±1`
modulo `3^(n/3 − 1)`.

## Route
1. For large `n`, put `p = |tr C^(3^n − 2)|`, a prime.  If `padicValNat 3 (glCard 3 p) ≤ n`, then
   (`exists_entry_pow_congr_mul`-style: the order of `C` mod `p` divides `3^n(3^(kj) − 1)` for a
   suitable `j ≥ 1` and all `k`) `p ∣ tr C^(3^(n+kj) − 2) − tr C^(3^n − 2)`, via
   `TheoremDGround.dvd_trace_sub_of_orderOf_dvd`.  So `p` divides a later prime trace of strictly
   larger absolute value (growth; use a large `k`): contradiction.  Hence
   `n < padicValNat 3 (glCard 3 p)`.
2. `TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard` gives `i ∈ {1, 2, 3}` with
   `3^(n/3) ∣ p^i − 1`.
   - `i = 1`: done.
   - `i = 2`: `3 ∤` one of `p ∓ 1`, since they differ by 2.
   - `i = 3`: `p³ ≡ 1 (mod 3^e)` gives `p ≡ 1 (mod 3^(e−1))`, as `p² + p + 1 ≡ 3 (mod 9)` when `p ≡ 1 (mod 3)`, and `p ≡ 2 (mod 3)` is impossible.
3. Transfer from `p = |t|` to `t` (signs: `±1` is symmetric).

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.ShiftedWindow

open LeanFormalizations.Mills.ThreeAdic Filter Matrix

theorem window_of_eventually_prime (C : Matrix (Fin 3) (Fin 3) ℤ) (hdet : C.det ≠ 0)
    (hgrow : Tendsto (fun n : ℕ => |(C ^ (3 ^ n - 2)).trace|) atTop atTop)
    (hprime : ∀ᶠ n in atTop, Prime (C ^ (3 ^ n - 2)).trace) :
    ∀ᶠ n in atTop, (3 : ℤ) ^ (n / 3 - 1) ∣ (C ^ (3 ^ n - 2)).trace - 1 ∨
      (3 : ℤ) ^ (n / 3 - 1) ∣ (C ^ (3 ^ n - 2)).trace + 1 := by
  sorry

end LeanFormalizations.Mills.ShiftedWindow

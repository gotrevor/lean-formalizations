/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDMixed
import LeanFormalizations.NumberTheory.Mills.ShiftedMills
import LeanFormalizations.Literature.Saito2025
import LeanFormalizations.Literature.Siegel1944

/-!
# Phase 58: shifted Mills constants `ξ(3^k + s)` are transcendental for even `s ≥ 8`, `3 ∤ s`
(conditional only on Saito 2025 Type B and Siegel 1944; no rigidity node)

Let `j` be least-ish with `3^(j+1) ≥ s` and `C_k = 3^(k+j) + s`.  Let `ξ` be the least `A > 1` with
`⌊A^(C_k)⌋` prime for every `k ≥ 1`.

## Route
1. **Saito's hypotheses** for `C` (`Literature.Saito2025TypeBTrace`): `C 1 ≥ 1`; `2 C_k ≤ C_(k+1)`
   (⇔ `s ≤ 3^(k+j)`, from `hj`); ratio `≥ 29/10` for all large `k` (ratios `→ 3`); `(B5′)`: `3 ∤ C_m`
   (`3 ∤ s`), so `C_m ∣ 3^(j+m)·(3^t − 1) = C_(m+t) − C_m` for `t = ord_(C_m)(3)` (or `φ(C_m)`), and
   every multiple `t·i` works, giving a large `k` with ratio `≥ 29/10`.
2. **`IsLeast` is unique**, so Saito's `ξ` is ours.  Branch 1: transcendental, done.
3. **Branch 2: `g = 1`.**  `g ∣ C_k` and `g ∣ C_(k+1)` for large `k` ⇒ `g ∣ 3C_k − C_(k+1) = 2s`;
   `C_k` is odd (`s` even), so `g` is odd, `g ∣ s`; then `g ∣ 3^(k+j)` and `gcd(g, 3) = 1` (as `3 ∤ s`),
   so `g = 1`.  Hence `ξ` is a cubic Pisot number.
4. **Contradiction with Theorem D** (`TheoremDMixed.floor_pow_prime_pow_add_not_prime_full`, `c = 3`,
   `f` = the integer minimal polynomial of `ξ`, `d = 3`):
   - `hs`: `ξ ≥ κ` (Siegel) and `κ^8 > 4`, so `ξ^s > 4 = d + 1`.
   - If `f ≢ X³ (mod 3)`: Theorem D gives infinitely many `n` with `⌊ξ^(3^n + s)⌋` not prime; take
     one with `n ≥ j + 1`, i.e. `n = k + j`, `k ≥ 1`: contradiction.
   - If `f ≡ X³ (mod 3)`: every root is a non-unit above 3, so `powTrace ξ N ≡ 0 (mod 3)` for
     `N ≥ 3` (Newton / `σ₁ ≡ σ₂ ≡ σ₃ ≡ 0`), and by branch 2's trace identity the prime `⌊ξ^(C_k)⌋`
     is divisible by 3 for all large `k`, yet it tends to infinity: contradiction.

Frozen: the statement below; all earlier statements; `Literature/` (the new
`Literature/Siegel1944.lean` def is frozen too).  No `private`.  Decomposing is progress.
-/

namespace LeanFormalizations.Mills.ShiftedMillsLarge

open LeanFormalizations.Literature

/-- **Transcendence of `ξ(3^(k+j) + s)`** for even `s ≥ 8` with `3 ∤ s`. -/
theorem xi_shifted_large_transcendental (hS : Saito2025TypeBTrace)
    (hSieg : Siegel1944SmallestPisot) {s j : ℕ} (hs_even : Even s) (hs3 : ¬ 3 ∣ s) (hs8 : 8 ≤ s)
    (hj : s ≤ 3 ^ (j + 1)) {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ (3 ^ (k + j) + s)⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  sorry

end LeanFormalizations.Mills.ShiftedMillsLarge

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedMillsLarge

/-!
# Phase 59: `ξ(3^k + s)` is transcendental whenever the 3-free part of even `s` is `≥ 8`

Phase 58 (`ShiftedMillsLarge.xi_shifted_large_transcendental`) needs `3 ∤ s`.  Here
`s = 3^a · s'` with `s'` even, `3 ∤ s'`, `s' ≥ 8`, and the conclusion is the same, conditional only
on `Literature.Saito2025TypeBTrace` and `Literature.Siegel1944SmallestPisot`.

Let `C_k = 3^(k+j) + 3^a s'` with `3^a s' ≤ 3^(j+1)`, and `ξ` the least `A > 1` with `⌊A^(C_k)⌋`
prime for every `k ≥ 1`.

## Route
0. **`a < j`**: `8·3^a ≤ 3^a s' ≤ 3^(j+1)` forces `a + 1 < j + 1`.  So for `k ≥ 1`,
   `C_k = 3^a · D_k` with `D_k = 3^(k+j−a) + s'` and `3 ∤ D_k`.
1. **Saito's hypotheses.**  `C 1 ≥ 1`, doubling and the eventual ratio bound exactly as in
   phase 58 (`largeC_two_mul_le`, `largeC_ratio_of_le` with `s := 3^a s'`).  `(B5′)`: Euler on
   `C_m` is unavailable (`3 ∣ C_m` when `a ≥ 1`), so use `D_m`: with `t = φ(D_m)·i`,
   `3^t ≡ 1 (mod D_m)`, hence `D_m ∣ D_(m+t)` (the phase 58 `largeC_dvd_shift` computation with
   `j − a` in place of `j` and `s'` in place of `s`), hence `C_m = 3^a D_m ∣ 3^a D_(m+t) = C_(m+t)`.
2. **`IsLeast` is unique**, so Saito's `ξ` is ours.  Branch 1: transcendental, done.
3. **Branch 2: `g = 3^b` with `b ≤ a`.**  `g ∣ 3C_k − C_(k+1) = 2·3^a s'`; `C_k` is odd, so `g` is
   odd, so `g ∣ 3^a s'`; then `g ∣ C_k − 3^a s' = 3^(k+j)`, and `gcd(3^a s', 3^(k+j)) = 3^a`
   (`3 ∤ s'`, `k + j ≥ a`), so `g ∣ 3^a`, i.e. `g = 3^b` (`Nat.dvd_prime_pow`).
4. **Pass to `β = ξ^g`**, a cubic Pisot number.  `C_k / g = 3^(k+j−b) + σ` with
   `σ = 3^(a−b) s' ≥ s' ≥ 8`, and `⌊ξ^(C_k)⌋ = ⌊β^(C_k / g)⌋` (`pow_mul`, `g ∣ C_k`).
   - `β^σ > 4 = d + 1` (`ShiftedMillsLarge.four_lt_pisot_pow`).
   - If `minpoly ℤ β ≢ X³ (mod 3)`: `TheoremDMixed.floor_pow_prime_pow_add_not_prime_full` at
     `c = 3`, shift `σ`, gives infinitely many `n` with `⌊β^(3^n + σ)⌋` not prime; take `n ≥ j + 1`,
     write `n = k + j − b` with `k ≥ 1`, and `⌊β^(3^n + σ)⌋ = ⌊ξ^(C_k)⌋` is prime: contradiction.
   - If `minpoly ℤ β ≡ X³ (mod 3)`: `ShiftedMillsLarge.dvd_traceSeq_of_map_eq_X_pow` and Saito's
     trace identity `powTrace β (C_k / g) = ⌊ξ^(C_k)⌋` make the prime `⌊ξ^(C_k)⌋` divisible by 3
     for all large `k`, yet it tends to infinity: contradiction (as in phase 58, with `β`).

Phase 58's statement is the case `a = 0`.  Checked: `scripts/shifted-mills-three-pow-probe.py`
(72 `(a, s')` cases; controls `s' = 4` and Euler-on-`C_m` fail as they should).

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.  Decomposing
into named sub-lemmas is progress.
-/

namespace LeanFormalizations.Mills.ShiftedMillsThreePow

open Filter Polynomial LeanFormalizations.Literature
  LeanFormalizations.Mills.TheoremDGeneral LeanFormalizations.Mills.TheoremDMixed
  LeanFormalizations.Mills.ShiftedMillsLarge

/-- **Transcendence of `ξ(3^(k+j) + 3^a s')`** for even `s' ≥ 8` with `3 ∤ s'` and any `a`. -/
theorem xi_shifted_three_pow_transcendental (hS : Saito2025TypeBTrace)
    (hSieg : Siegel1944SmallestPisot) {a s' j : ℕ} (hs_even : Even s') (hs3 : ¬ 3 ∣ s')
    (hs8 : 8 ≤ s') (hj : 3 ^ a * s' ≤ 3 ^ (j + 1)) {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ (3 ^ (k + j) + 3 ^ a * s')⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  sorry

end LeanFormalizations.Mills.ShiftedMillsThreePow

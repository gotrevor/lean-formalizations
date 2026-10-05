/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Theorem E+ from any short-interval exponent `θ < 2/3`

`SaitoTypeB.xi_shift_transcendental_classical` proves `ξ(3^(k+j) + s)` transcendental for every
`s ≠ 0` from `BakerHarmanPintz2001` (`θ = 21/40`) and `Dubickas2022`.  The exponent enters only
through Saito's Lemma 5.3, as `1/(1 − θ) + ε ≤ r` where `r` bounds the exponent ratios
`C(k+1)/C k` from below; for `C = 3^k + s` those ratios tend to `3`, so any `θ < 2/3` should do.

This file restates E+ (and Theorem E, `s = −2`) with the prime input weakened to
`PrimesShortInterval θ` for some `0 < θ < 2/3`, and derives the corollary from Ingham's 1937
exponent `5/8`, which needs no sieve.  The BHP headline and its stress tests stay; this is a
second headline beside them.

Why `2/3` is the natural threshold: Ingham's method turns `ζ(1/2 + it) ≪ t^c` into the exponent
`(1 + 4c)/(2 + 4c) + ε`.  The convexity bound `c = 1/4` gives `2/3 + ε`, which just misses; any
subconvex `c < 1/4` suffices.
-/
import LeanFormalizations.NumberTheory.Mills.SaitoTypeB
import LeanFormalizations.NumberTheory.PrimeIntervals.BHPTests

namespace LeanFormalizations.Mills.SaitoTypeBTheta

open LeanFormalizations.Literature LeanFormalizations.BHPTests Filter
  LeanFormalizations.Mills.ShiftedMillsAll

/-! ## The Ingham input, checked against the family -/

/-- `Ingham1937` is the family statement on `(5/8, 1]`, by definition. -/
theorem ingham_iff :
    Ingham1937 ↔ ∀ θ : ℝ, 5 / 8 < θ → θ ≤ 1 → PrimesShortInterval θ := Iff.rfl

/-- **Sanity**: BHP (`θ = 21/40 < 5/8`) implies Ingham's statement, via monotonicity. -/
theorem ingham_of_bhp (h : BakerHarmanPintz2001) : Ingham1937 := by
  sorry

/-! ## Theorem E+ from `θ < 2/3` -/

/-- **Theorem E+ from a short-interval exponent `θ < 2/3`**: `ξ(3^(k+j) + s)` is transcendental
for every `s ≠ 0`, conditional on `PrimesShortInterval θ` and Dubickas 2022 Lemma 6. -/
theorem xi_shift_transcendental_of_shortInterval {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hP : PrimesShortInterval θ) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  sorry

/-- **Theorem E+ on Ingham 1937**: no sieve input, conditional on Ingham and Dubickas 2022. -/
theorem xi_shift_transcendental_ingham (hI : Ingham1937) (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j s k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  sorry

/-- **Theorem E on Ingham 1937**: `ξ(3^k − 2)` is transcendental. -/
theorem xi_shifted_transcendental_ingham (hI : Ingham1937) (hD : Dubickas2022)
    {ξ : ℝ}
    (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ ShiftedMills.shiftedC k⌋₊).Prime} ξ) :
    Transcendental ℚ ξ := by
  sorry

end LeanFormalizations.Mills.SaitoTypeBTheta

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Stress tests for `Literature.BakerHarmanPintz2001`

Theorem E+ (`Mills/SaitoTypeB.lean`) assumes `BakerHarmanPintz2001`.  A literature `Prop` stated
too strongly is false, and a false hypothesis makes every theorem assuming it vacuous.  This file
checks the definition against known answers, so a typo in the exponent, the interval or the
counting function shows up as a failed proof:

* **`primesIn` unit tests**: hand-counted values, including the clamping quirks (a negative left
  end counts from `0`; a reversed interval is empty).
* **The exponent family** `PrimesShortInterval θ`, with `BakerHarmanPintz2001` the case
  `θ = 21/40` *definitionally* (`bhp_iff`).
* **A false sibling**: `θ = 0` fails, since `[n! + 2, n! + 3]` holds no prime.
* **A true sibling**: `θ = 1` holds, from the Prime Number Theorem (Chebyshev bounds suffice).
* **Monotonicity in `θ`** on `(0, 1]`, so `θ = 21/40` sits inside the family between the false
  and true endpoints, and BHP implies the `θ = 1` statement through the family.
-/
import LeanFormalizations.Literature.Primes
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.PNT

namespace LeanFormalizations.BHPTests

open LeanFormalizations.Literature

/-! ## `primesIn` unit tests (hand-counted) -/

/-- `11, 13, 17, 19`. -/
theorem primesIn_10_20 : primesIn 10 20 = 4 := by
  sorry

/-- Non-integer left end rounds up: `⌈10.5⌉ = 11`, so `11, 13`. -/
theorem primesIn_10_5_13 : primesIn 10.5 13 = 2 := by
  sorry

/-- `24, 25, 26, 27, 28` are all composite. -/
theorem primesIn_24_28 : primesIn 24 28 = 0 := by
  sorry

/-- A degenerate interval at a prime counts it. -/
theorem primesIn_2_2 : primesIn 2 2 = 1 := by
  sorry

/-- A negative left end is clamped to `0` by `⌈·⌉₊`, so this counts `2, 3`. -/
theorem primesIn_neg5_3 : primesIn (-5) 3 = 2 := by
  sorry

/-- A reversed interval is empty. -/
theorem primesIn_reversed : primesIn 5 3 = 0 := by
  sorry

/-! ## The exponent family -/

/-- `[x, x + x^θ]` holds `≫ x^θ / log x` primes for all large `x`. -/
def PrimesShortInterval (θ : ℝ) : Prop :=
  ∃ d₀ > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X,
    d₀ * x ^ θ / Real.log x ≤ (primesIn x (x + x ^ θ) : ℝ)

/-- `BakerHarmanPintz2001` is the `θ = 21/40` member, by definition. -/
theorem bhp_iff : BakerHarmanPintz2001 ↔ PrimesShortInterval ((21 : ℝ) / 40) := Iff.rfl

/-- **False sibling.**  At `θ = 0` the window `[x, x + 1]` is prime-free at `x = n! + 2`
(`n ≥ 3`), while `d₀ / log x > 0`. -/
theorem not_primesShortInterval_zero : ¬ PrimesShortInterval 0 := by
  sorry

/-- **True sibling.**  `[x, 2x]` holds `≫ x / log x` primes: `π(2x) − π(x) ∼ x / log x` by
`prime_number_theorem`. -/
theorem primesShortInterval_one : PrimesShortInterval 1 := by
  sorry

/-- **Monotone in `θ`.**  Tile `[x, x + x^θ']` by about `x^(θ' − θ)` disjoint windows
`[y, y + y^θ]` with `x ≤ y ≤ 2x`; each holds `≥ d₀ y^θ / log y ≫ x^θ / log x` primes. -/
theorem PrimesShortInterval.mono {θ θ' : ℝ} (h0 : 0 < θ) (hle : θ ≤ θ') (h1 : θ' ≤ 1) :
    PrimesShortInterval θ → PrimesShortInterval θ' := by
  sorry

/-- BHP implies the `θ = 1` statement through the family. -/
theorem primesShortInterval_one_of_bhp (h : BakerHarmanPintz2001) : PrimesShortInterval 1 :=
  PrimesShortInterval.mono (by norm_num) (by norm_num) le_rfl (bhp_iff.mp h)

/-- What Theorem E+ consumes: under BHP, every large `x` has a prime in `[x, x + x^(21/40)]`. -/
theorem exists_prime_of_bhp (h : BakerHarmanPintz2001) :
    ∃ X : ℝ, ∀ x ≥ X, ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + x ^ ((21 : ℝ) / 40) := by
  sorry

end LeanFormalizations.BHPTests

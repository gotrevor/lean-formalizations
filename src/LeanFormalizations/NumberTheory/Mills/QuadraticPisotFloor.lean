/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasPrimePow

/-!
# Phase 39: `⌊α^(c^n)⌋ + h` is composite i.o. for quadratic Pisot units of norm `−1`

Saito's Problem 1.1 asks whether `⌊β^(3^n)⌋` is composite infinitely often for cubic Pisot `β`.
The quadratic analogue with any shift follows from phase 35.  Let `α = (P + √(P² + 4))/2`
(`P ≥ 1`) be the Pisot unit of norm `−1`.  For odd `N`, `⌊α^N⌋ = V_N(P, −1)`, because the conjugate
`β = −1/α` satisfies `−1 < β^N < 0`.  Checked numerically for `P ≤ 7`, `N ≤ 81`.  So for every odd prime
`c ∤ P` and every `h`, `⌊α^(c^n)⌋ + h` is composite infinitely often.  The golden ratio `φ`
(`P = 1`) is covered at every odd prime `c`.

For `c = 2`: `⌊φ^(2^n)⌋ = L(2^n) − 1`, and the only open shift is `h = 1` (Fermat-type, `L(2^n)`);
this is not claimed here.

## Route
1. `floor_pow_odd`: `⌊α^N⌋ = lucasV P (−1) N` for odd `N`.  `α^N + β^N = V_N` (induction on
   the recurrence, or `α, β` roots of `X² − PX − 1`), `β = −1/α`, `0 < α⁻¹ < 1` since `α > 1`,
   so `β^N ∈ (−1, 0)` for odd `N ≥ 1`.  Use `Int.floor_eq_iff`.
2. Main: rewrite with step 1 (`c^n` is odd) and apply
   `LucasPrimePow.lucasV_prime_pow_add_not_prime`.
3. `golden_floor_prime_pow_add_not_prime`: `P = 1`; `c ∤ 1` for every prime.

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.QuadraticPisotFloor

open LeanFormalizations.Mills.LucasPrimePow Filter

/-- The Pisot unit of norm `−1` with trace `P`. -/
noncomputable def pisotNegUnit (P : ℤ) : ℝ := (P + Real.sqrt (P ^ 2 + 4)) / 2

theorem floor_pow_odd {P : ℤ} (hP : 1 ≤ P) {N : ℕ} (hN : Odd N) :
    ⌊pisotNegUnit P ^ N⌋ = lucasV P (-1) N := by
  sorry

/-- **`⌊α^(c^n)⌋ + h` is composite infinitely often** for the norm `−1` quadratic Pisot unit
`α` of trace `P ≥ 1`, every odd prime `c ∤ P`, and every integer `h`. -/
theorem floor_pisotNegUnit_prime_pow_add_not_prime {P : ℤ} (hP : 1 ≤ P) {c : ℕ}
    (hc : c.Prime) (hc2 : c ≠ 2) (hcP : ¬ (c : ℤ) ∣ P) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (⌊pisotNegUnit P ^ (c ^ n)⌋ + h) := by
  sorry

/-- The golden ratio: `⌊φ^(c^n)⌋ + h` is composite i.o. for every odd prime `c` and every `h`. -/
theorem golden_floor_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (⌊((1 + Real.sqrt 5) / 2) ^ (c ^ n)⌋ + h) := by
  sorry

end LeanFormalizations.Mills.QuadraticPisotFloor

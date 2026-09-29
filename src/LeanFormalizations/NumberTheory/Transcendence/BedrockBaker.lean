/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# More bedrock: Lindemann–Weierstrass odds and ends, and Baker (phase 22)

Unconditional, like `Bedrock.lean`.  Inputs: `LindemannWeierstrassAlgIndep`, `BakerHomogeneous`
(`Literature/Waldschmidt2023.lean`, `ℚ̄`-linear independence of `1, λ₁, …, λₙ`, checked against
the rendered survey page 4) and `Baker1966` (inhomogeneous).

* LW: `tan a`, `sinh a`, `cosh a` for nonzero algebraic real `a`.
* Baker, the survey's own example (p. 4): `λ₁ = log 2` and `λ₂ = log 2 + 2πi` are `ℚ`-linearly
  independent logarithms of `2`, so `1, log 2, πi` are `ℚ̄`-linearly independent.  Hence
  **`π + log 2` is transcendental**: if it equalled an algebraic `β`, then `β = log 2 + (λ₂−λ₁)/(2i)`
  would be a nontrivial `ℚ̄`-relation among `1, λ₁, λ₂`.
* Baker: **`2^{√2}·3^{√3}` is transcendental**.  If it equalled an algebraic `γ`, then
  `√2 log 2 + √3 log 3 − log γ = 0`; take a `ℚ`-basis of `log 2, log 3, log γ` and apply
  `BakerHomogeneous` (the coefficients `√2, √3` are algebraic and `1, √2, √3` are `ℚ`-independent).

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.NumberTheory.Transcendence.Bedrock
import LeanFormalizations.Literature.Waldschmidt2023

namespace LeanFormalizations.Bedrock

open LeanFormalizations.Literature

theorem transcendental_tan_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.tan a) := by
  sorry

theorem transcendental_sinh_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.sinh a) := by
  sorry

theorem transcendental_cosh_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.cosh a) := by
  sorry

theorem transcendental_pi_add_log_two (hB : BakerHomogeneous) :
    Transcendental ℚ (Real.pi + Real.log 2) := by
  sorry

theorem transcendental_two_rpow_sqrt_two_mul_three_rpow_sqrt_three (hB : BakerHomogeneous) :
    Transcendental ℚ ((2 : ℝ) ^ Real.sqrt 2 * (3 : ℝ) ^ Real.sqrt 3) := by
  sorry

end LeanFormalizations.Bedrock

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Bedrock: the unconditional classics (phase 21)

Trevor, 2026-09-27: *"the more bedrock we have, the better."*  After the Schanuel phases this file
collects consequences of the **theorems**: Lindemann–Weierstrass (mathlib PR #28013, in
`Literature/Lindemann.lean`), Gelfond–Schneider (`Literature/GelfondSchneider.lean`, real form)
and Nesterenko (`Literature/Nesterenko.lean`).  Nothing here rests on a conjecture.

* Hermite–Lindemann: `e^a` for nonzero algebraic `a`; `log α` for algebraic `α > 0`, `α ≠ 1`;
  `sin a`, `cos a` for nonzero algebraic real `a`.  (For `cos`, use `2cos a = e^{ia} + e^{-ia}`
  with the two exponentials algebraically independent, or LW's linear form with `u = ±ia, 0`.)
* Gelfond–Schneider (real form): `2^√2`; `log 3 / log 2` is transcendental (if it were algebraic
  it would be irrational by unique factorization, and then `2^{log 3/log 2} = 3` contradicts GS).
* Nesterenko: `e^π`, `π + e^π`, `π·e^π`, `Γ(1/4)` transcendental; `e^{-π/2}` (`= i^i`).

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Lindemann
import LeanFormalizations.Literature.GelfondSchneider
import LeanFormalizations.Literature.Nesterenko

namespace LeanFormalizations.Bedrock

open LeanFormalizations.Literature

/-! ## Lindemann–Weierstrass -/

theorem transcendental_cexp_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℂ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Complex.exp a) := by
  sorry

theorem transcendental_log_of_algebraic (hL : LindemannWeierstrassAlgIndep) {α : ℝ}
    (hα : IsAlgebraic ℚ α) (hpos : 0 < α) (h1 : α ≠ 1) : Transcendental ℚ (Real.log α) := by
  sorry

theorem transcendental_sin_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.sin a) := by
  sorry

theorem transcendental_cos_of_algebraic (hL : LindemannWeierstrassAlgIndep) {a : ℝ}
    (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Real.cos a) := by
  sorry

/-! ## Gelfond–Schneider -/

theorem transcendental_two_rpow_sqrt_two (hGS : GelfondSchneider1934) :
    Transcendental ℚ ((2 : ℝ) ^ Real.sqrt 2) := by
  sorry

theorem transcendental_log_three_div_log_two (hGS : GelfondSchneider1934) :
    Transcendental ℚ (Real.log 3 / Real.log 2) := by
  sorry

/-! ## Nesterenko -/

theorem transcendental_exp_pi (hN : Nesterenko1996) : Transcendental ℚ (Real.exp Real.pi) := by
  sorry

theorem transcendental_pi_add_exp_pi (hN : Nesterenko1996) :
    Transcendental ℚ (Real.pi + Real.exp Real.pi) := by
  sorry

theorem transcendental_pi_mul_exp_pi (hN : Nesterenko1996) :
    Transcendental ℚ (Real.pi * Real.exp Real.pi) := by
  sorry

theorem transcendental_gamma_quarter (hN : Nesterenko1996) :
    Transcendental ℚ (Real.Gamma (1 / 4)) := by
  sorry

/-- `i^i = e^{-π/2}` is transcendental. -/
theorem transcendental_exp_neg_pi_div_two (hN : Nesterenko1996) :
    Transcendental ℚ (Real.exp (-(Real.pi / 2))) := by
  sorry

end LeanFormalizations.Bedrock

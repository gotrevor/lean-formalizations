/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The ℚ̄-independence variant of the shifted six exponentials statement

Trevor, 2026-09-29: record it.  It is **true** but **weaker**.  Write-up:
`ERRATUM-WALDSCHMIDT-2023-SHARP-SIX.md`.

`SixExponentialsShiftedAlg` is the survey's printed statement with ℚ̄-linear independence
instead of ℚ-linear independence.  This is the lap's "overbar repair".

* **True**: it follows from the sharp theorem.  If every `e^{xᵢyⱼ−βᵢⱼ}` were algebraic, sharp six
  would give `xᵢyⱼ = βᵢⱼ` for all `i, j`.  Then `x₁y₁ = β₁₁` and `x₁y₂ = β₁₂` force
  `β₁₂·y₁ = β₁₁·y₂`, a ℚ̄-relation between `y₁` and `y₂`.  If `β₁₁ = β₁₂ = 0`, then `x₁y₁ = 0` with
  `x₁ ≠ 0` (by independence) gives `y₁ = 0`, which contradicts independence.  ℚ̄-independence
  implies ℚ-independence, so sharp six applies.
* **Weaker**: it does not contain the six exponentials theorem, whose hypotheses are over `ℚ`.
  For example `x = (1, √2)` is ℚ-independent but ℚ̄-dependent, so the variant says nothing there.
  The witness `witness_not_algIndep` makes that precise.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Periods
import LeanFormalizations.Literature.Waldschmidt2023

namespace LeanFormalizations.Periods

open LeanFormalizations.Literature Complex

/-- The survey's shifted statement with independence over `ℚ̄` (the lap's proposed repair). -/
def SixExponentialsShiftedAlg : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (β : Fin 2 → Fin 3 → ℂ),
    LinearIndependent (integralClosure ℚ ℂ) x → LinearIndependent (integralClosure ℚ ℂ) y →
    (∀ i j, IsAlgebraic ℚ (β i j)) → ∃ i j, Transcendental ℚ (exp (x i * y j - β i j))

/-- The ℚ̄ variant is a true consequence of the sharp six exponentials theorem. -/
theorem shiftedAlg_of_sharp (h : SixExponentialsSharp) : SixExponentialsShiftedAlg := by
  sorry

/-- It is strictly narrower in scope: `(1, √2)` is `ℚ`-independent but not `ℚ̄`-independent, so
the six exponentials theorem's instances with algebraic `x` fall outside the variant. -/
theorem witness_not_algIndep :
    LinearIndependent ℚ ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ)] ∧
      ¬ LinearIndependent (integralClosure ℚ ℂ) ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ)] := by
  sorry

end LeanFormalizations.Periods

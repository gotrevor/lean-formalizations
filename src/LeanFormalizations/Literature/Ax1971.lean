/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature input: Ax's theorem (1971), the power-series Schanuel

Statement only, cited, never an `axiom`.  Trevor, 2026-09-29: *"don't formalize the proof.  Just
the statement."*

J. Ax, *On Schanuel's conjectures*, Ann. of Math. **93** (1971), 252–268.  The form used here is
from S. Dasgupta, *Lecture 3: Schanuel's conjecture and Ax's theorem* (Duke Math 790, 2021),
slides 1 and 21.  If `y₁, …, yₙ ∈ tℂ[[t]]` are `ℚ`-linearly independent, then
`trdeg_ℂ ℂ(y₁, …, yₙ, e^{y₁}, …, e^{yₙ}) ≥ n + 1`.  This is equivalent to Dasgupta's
`trdeg_{ℂ(t)} ℂ(t)(y, e^y) ≥ n`.

`n ≥ 1` is needed: for `n = 0` the field is `ℂ` itself and the bound `1` fails.  The hypothesis
"`yᵢ ∈ tℂ[[t]]`" is essential too: with constant `y₁ = 1`, `ℂ(1, e) = ℂ` has transcendence degree 0.
Wikipedia's phrasing ("power series … linearly independent over ℚ", with no zero-constant
condition) omits it.

The ambient field is `FractionRing ℂ⟦X⟧`, and `e^{y}` is `(PowerSeries.exp ℂ).subst y`.
-/
import Mathlib

namespace LeanFormalizations.Literature

open PowerSeries

/-- **Ax (1971)**: `ℚ`-linearly independent power series without constant term, together with
their exponentials, generate a field of transcendence degree at least `n + 1` over `ℂ`. -/
def Ax1971 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (y : Fin n → PowerSeries ℂ), (∀ i, constantCoeff (y i) = 0) →
    LinearIndependent ℚ y →
    ((n + 1 : ℕ) : Cardinal) ≤ Algebra.trdeg ℂ (IntermediateField.adjoin ℂ
      (Set.range (fun i ↦ algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) (y i)) ∪
       Set.range (fun i ↦ algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))
         ((exp ℂ).subst (y i)))))

end LeanFormalizations.Literature

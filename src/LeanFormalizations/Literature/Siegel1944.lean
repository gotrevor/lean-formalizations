/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Pisot

/-!
# Literature input: Siegel (1944), the smallest Pisot number

C. L. Siegel, *Algebraic integers whose conjugates lie in the unit circle*, Duke Math. J. **11**
(1944), 597–602: the smallest Pisot number is the real root `κ ≈ 1.3247` of `x³ − x − 1` (the
plastic number).  Statement only (faithful; never an `axiom`).  Used by phase 58 only through
`κ^8 > 4`, to make the size argument of Theorem D apply to the Pisot branch of Saito's Type B.
-/

namespace LeanFormalizations.Literature

/-- **Siegel (1944).**  Every Pisot number is at least the plastic number. -/
def Siegel1944SmallestPisot : Prop :=
  ∀ β : ℝ, IsPisot β → ∀ κ : ℝ, κ ^ 3 = κ + 1 → 1 < κ → κ ≤ β

end LeanFormalizations.Literature

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature input: Nesterenko's theorem (1996)

Statement only (rules in `Literature/Primes.lean`: faithful or weaker, cited, never an `axiom`).

Yu. V. Nesterenko, *Modular functions and transcendence questions*, Sb. Math. **187** (1996),
1319–1348: `π`, `e^π` and `Γ(1/4)` are algebraically independent over `ℚ`.  This is the strongest
unconditional algebraic-independence result involving `π`.  It is weaker than what Schanuel gives
for `π, e^π` (`Schanuel.algebraicIndependent_pi_exp_pi`), but it is a theorem.
-/
import Mathlib

namespace LeanFormalizations.Literature

/-- **Nesterenko (1996)**: `π`, `e^π`, `Γ(1/4)` are algebraically independent. -/
def Nesterenko1996 : Prop :=
  AlgebraicIndependent ℚ ![Real.pi, Real.exp Real.pi, Real.Gamma (1 / 4)]

end LeanFormalizations.Literature

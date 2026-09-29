/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The implications in Waldschmidt's 2023 survey (phase 19)

Phases 15–17 covered Conjecture 2, Theorems 3–5 and Conjecture 6 (`Schanuel.lean`,
`Exponentials.lean`, `ExponentialsKnown.lean`).  This file adds Conjecture 1 and the survey's own
derivations around it.  The coverage map is `WALDSCHMIDT-2023.md`.

* Schanuel ⇒ Conjecture 1 (survey §7: "Conjecture 1 is the special case of Conjecture 6 where the
  `e^{xᵢ}` are algebraic").
* Conjecture 1 ⇒ four exponentials: the survey's own route (§4; Waldschmidt 2000 Ex. 1.8,
  Roy's reformulation).  Independent of phase 16's route from full Schanuel.
* Conjecture 1 ⇒ Baker's homogeneous conclusion (algebraic independence over `ℚ` gives it over
  `ℚ̄`, since `ℚ̄/ℚ` is algebraic, and a `ℚ̄`-linear relation is a polynomial relation).
* Conjecture 1 ⇒ `log 2` and `π` are algebraically independent (survey p. 4: take `λ₁ = log 2`,
  `λ₂ = log 2 + 2πi`).
* Conjecture 1 for `n = 1` is **known**, by Hermite–Lindemann: from `LindemannWeierstrassAlgIndep`
  (a nonzero logarithm of an algebraic number is transcendental).

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Waldschmidt2023
import LeanFormalizations.NumberTheory.Transcendence.ExponentialsKnown

namespace LeanFormalizations.Waldschmidt2023

open LeanFormalizations.Literature

theorem algIndepLogs_of_schanuel (hS : SchanuelConjecture) : AlgIndepLogsConjecture := by
  sorry

theorem fourExponentials_of_algIndepLogs (h : AlgIndepLogsConjecture) :
    FourExponentialsConjecture := by
  sorry

theorem bakerHomogeneous_of_algIndepLogs (h : AlgIndepLogsConjecture) : BakerHomogeneous := by
  sorry

theorem algebraicIndependent_log_two_pi (h : AlgIndepLogsConjecture) :
    AlgebraicIndependent ℚ ![Real.log 2, Real.pi] := by
  sorry

/-- Conjecture 1 for `n = 1` is known: a nonzero logarithm of an algebraic number is
transcendental (Hermite–Lindemann). -/
theorem transcendental_log_of_lindemann (hL : LindemannWeierstrassAlgIndep) {ℓ : ℂ}
    (hℓ : ℓ ≠ 0) (he : IsAlgebraic ℚ (Complex.exp ℓ)) : Transcendental ℚ ℓ := by
  sorry

end LeanFormalizations.Waldschmidt2023

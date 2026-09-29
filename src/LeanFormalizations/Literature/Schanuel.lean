/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Conjecture input: Schanuel's conjecture

An open conjecture, stated as a hypothesis `Prop` in the same way as `RiemannHypothesis`.  It is
never an `axiom`.  The statement is copied verbatim from google-deepmind/formal-conjectures
`FormalConjectures/Wikipedia/Schanuel.lean` (`Schanuel.schanuel_conjecture`, clone at `5d5832d0`,
Apache 2.0).

S. Lang, *Introduction to Transcendental Numbers* (1966), p. 30–31, where it is attributed to
Schanuel; J. Ax, *On Schanuel's conjectures*, Ann. of Math. **93** (1971) proves the power-series
analogue.

It implies Lindemann–Weierstrass, Gelfond–Schneider and Baker's theorem, and it would make
`e` and `π` algebraically independent.  The consequences are derived in
`NumberTheory/Transcendence/Schanuel.lean`.
-/
import Mathlib

namespace LeanFormalizations.Literature

open IntermediateField

/-- **Schanuel's conjecture**: for complex `z₁, …, zₙ` linearly independent over `ℚ`, the field
`ℚ(z₁, …, zₙ, e^{z₁}, …, e^{zₙ})` has transcendence degree at least `n` over `ℚ`. -/
def SchanuelConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    n ≤ Algebra.trdeg ℚ (adjoin ℚ (Set.range z ∪ Set.range (Complex.exp ∘ z)))

end LeanFormalizations.Literature

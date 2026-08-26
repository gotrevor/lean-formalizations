/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Transcendence of π and e - comparator CHALLENGE (the trusted audit surface)

This file is the **thing a human audits.** It imports *only* Mathlib and states the two headline
theorems with `sorry`. `Solution.lean` (which imports the real development) must prove *these
exact statements*, and `comparator` machine-checks that it did: every declaration appearing in a
statement here must be **identical** in the solution environment, the proofs must be accepted by
the Lean kernel and independently by the `nanoda` kernel, and they may use no axioms beyond
`propext`, `Quot.sound`, `Classical.choice`.

So the trust chain is: *read this file, and only this file* - comparator certifies the rest.

There is deliberately nothing else to read. Both statements are written entirely in Mathlib's own
vocabulary (`Transcendental`, `ℚ`, `Real.pi`, `Real.exp`) - the development contributes **no
definition** to the trusted surface, so there is no project notion whose faithfulness has to be
audited. Mathlib's `Transcendental ℚ x` is `¬ IsAlgebraic ℚ x`: no nonzero polynomial with
rational coefficients has `x` as a root.
-/

-- The statements below are `sorry` by design; keep the disclosed warnings from ever becoming
-- errors, whatever the enclosing package's option set.
set_option warningAsError false

namespace LeanFormalizations.Transcendence

/-- **Transcendence of `π`** over `ℚ` (Lindemann, 1882). -/
theorem transcendental_pi_axiomClean : Transcendental ℚ Real.pi := sorry

/-- **Transcendence of `e`** over `ℚ` (Hermite, 1873). -/
theorem e_transcendental : Transcendental ℚ (Real.exp 1) := sorry

/-- Non-vacuity of the *notion*, proved right here rather than by the solution: `Transcendental ℚ`
is not a predicate everything satisfies - `2` is algebraic over `ℚ`. -/
example : ¬ Transcendental ℚ (2 : ℝ) := fun h =>
  h (by simpa [map_ofNat] using isAlgebraic_algebraMap (2 : ℚ))

end LeanFormalizations.Transcendence

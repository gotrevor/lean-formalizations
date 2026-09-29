/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature input: the Gelfond–Schneider theorem (real form)

Statement only (rules in `Literature/Primes.lean`: faithful or weaker, cited, never an `axiom`).
This is the real special case of Hilbert's seventh problem: `a ^ b` with `a > 0`, `a ≠ 1` and
`b` irrational, both algebraic.  It is weaker than the complex statement, which also covers
`a` complex under a fixed branch of `log`.

A. O. Gelfond, *Sur le septième problème de Hilbert*, Izv. Akad. Nauk SSSR **7** (1934),
623–630; Th. Schneider, *Transzendenzuntersuchungen periodischer Funktionen I*, J. Reine Angew.
Math. **172** (1934), 65–69; A. Baker, *Transcendental Number Theory* (1975), Theorem 2.1.
-/
import Mathlib

namespace LeanFormalizations.Literature

/-- **Gelfond–Schneider (1934), real form**: for algebraic `a > 0` with `a ≠ 1` and algebraic
irrational `b`, the number `a ^ b` is transcendental. -/
def GelfondSchneider1934 : Prop :=
  ∀ a b : ℝ, 0 < a → a ≠ 1 → IsAlgebraic ℚ a → IsAlgebraic ℚ b → Irrational b →
    Transcendental ℚ (a ^ b)

end LeanFormalizations.Literature

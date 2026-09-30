/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature inputs: the Lindemann–Weierstrass theorem

Statements only (rules in `Literature/Primes.lean`: faithful or weaker, cited, never an `axiom`).

🚧 **Pending upstream: mathlib4 PR #28013** "feat: Lindemann-Weierstrass Theorem" (Yuyang Zhao,
`astrainfinita`; <https://github.com/leanprover-community/mathlib4/pull/28013>), file
`Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean`.  The two `Prop`s below are that
PR's `linearIndependent_exp` and `algebraicIndependent_exp`, copied **statement-for-statement**.
**Do not prove these here** - the PR already does, and re-deriving it is wasted work.  When the
PR lands in our mathlib pin, replace each hypothesis use by the mathlib theorem (or add
`theorem lindemannWeierstrass : LindemannWeierstrass := linearIndependent_exp`) and keep the
`Prop` as the stable name.

What is already here without it: `e_transcendental` and `transcendental_pi_axiomClean`
(`NumberTheory/Transcendence/`, proved from scratch 2026-06) and mathlib's `irrational_pi`.
What it adds: `e^a` transcendental for every algebraic `a ≠ 0` (Hermite–Lindemann), hence
`log`, `sin`, `cos`, `tan` at nonzero algebraic points, and algebraic independence of
`e^{a_1}, …, e^{a_n}` for `ℚ`-linearly independent algebraic `a_i`.

F. Lindemann, *Über die Zahl π*, Math. Ann. **20** (1882), 213–225; K. Weierstrass, *Zu
Lindemann's Abhandlung*, Sitzungsber. Preuss. Akad. Wiss. (1885), 1067–1085; A. Baker,
*Transcendental Number Theory* (1975), Theorem 1.4.
-/
import Mathlib

namespace LeanFormalizations.Literature

open Complex

/-- **Lindemann–Weierstrass, Baker's linear form** (mathlib PR #28013, `linearIndependent_exp`):
for distinct algebraic `u i`, the numbers `e^(u i)` are linearly independent over the algebraic
numbers. -/
def LindemannWeierstrass : Prop :=
  ∀ {ι : Type} (u : ι → integralClosure ℚ ℂ), u.Injective →
    LinearIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i)

/-- **Lindemann–Weierstrass, algebraic-independence form** (mathlib PR #28013,
`algebraicIndependent_exp`): for algebraic `u i` linearly independent over `ℕ` (equivalently
`ℚ`), the numbers `e^(u i)` are algebraically independent over the algebraic numbers. -/
def LindemannWeierstrassAlgIndep : Prop :=
  ∀ {ι : Type} (u : ι → integralClosure ℚ ℂ), LinearIndependent ℕ u →
    AlgebraicIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i)

end LeanFormalizations.Literature

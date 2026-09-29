/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature and conjecture inputs: four and six exponentials

Statements only (rules in `Literature/Primes.lean`: faithful or weaker, cited, never an `axiom`).

* `FourExponentialsConjecture` is **open**.  It is copied verbatim from google-deepmind/formal-conjectures
  `FormalConjectures/Wikipedia/Exponentials.lean` (`Exponentials.four_exponentials_conjecture`,
  clone `5d5832d0`, Apache 2.0).  Schneider (1957) and Lang (1966) posed it, and it follows
  from Schanuel's conjecture (Waldschmidt, *Diophantine Approximation on Linear Algebraic
  Groups* (2000), Exercise 1.8, via algebraic independence of logarithms).
* `SixExponentials` is a **theorem**, proved by S. Lang, *Introduction to Transcendental
  Numbers* (1966), Ch. II Thm 1, and K. Ramachandra, Acta Arith. **14** (1968).  It is stated as
  in M. Waldschmidt, *The four exponentials problem and Schanuel's conjecture* (2023), Theorem 3.
-/
import Mathlib

namespace LeanFormalizations.Literature

open Complex

/-- **Four exponentials conjecture** (open): if `x₀, x₁` and `y₀, y₁` are each `ℚ`-linearly
independent, some `e^{xᵢ yⱼ}` is transcendental. -/
def FourExponentialsConjecture : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 2 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j : Fin 2, Transcendental ℚ (exp (x i * y j))

/-- **Six exponentials theorem** (Lang 1966, Ramachandra 1968): if `x₁, x₂` are `ℚ`-linearly
independent and `y₁, y₂, y₃` are `ℚ`-linearly independent, some `e^{xᵢ yⱼ}` is
transcendental. -/
def SixExponentials : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j, Transcendental ℚ (exp (x i * y j))

end LeanFormalizations.Literature

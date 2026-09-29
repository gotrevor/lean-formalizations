/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature inputs: the five exponentials and strong six exponentials theorems

Statements only (rules in `Literature/Primes.lean`: faithful or weaker, cited, never an `axiom`).
All three are **theorems**, stated as in M. Waldschmidt, *The four exponentials problem and
Schanuel's conjecture* (2023), §6.  Trevor, 2026-09-29: *"include as literature quotes."*

* `FiveExponentials`: Waldschmidt, *On the transcendence methods of Gel'fond and Schneider in
  several variables* (1988); survey Theorem 4.
* `SixExponentialsShifted`: Waldschmidt (1988) Cor. 2.1 and (1990) Cor. 2.3.  It covers both the
  five and the six exponentials theorems.
* `StrongSixExponentials`: D. Roy (1990, 1992b Cor. 2); survey Theorem 5; Waldschmidt, *Diophantine
  Approximation on Linear Algebraic Groups* (2000), Cor. 11.16.
-/
import Mathlib

namespace LeanFormalizations.Literature

open Complex

/-- **Five exponentials theorem** (Waldschmidt 1988): with `x₁, x₂` and `y₁, y₂` each
`ℚ`-linearly independent and `γ ≠ 0` algebraic, one of `e^{x₁y₁}, e^{x₁y₂}, e^{x₂y₁}, e^{x₂y₂},
e^{γx₁/x₂}` is transcendental. -/
def FiveExponentials : Prop :=
  ∀ (x y : Fin 2 → ℂ) (γ : ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    IsAlgebraic ℚ γ → γ ≠ 0 →
    (∃ i j : Fin 2, Transcendental ℚ (exp (x i * y j))) ∨ Transcendental ℚ (exp (γ * x 0 / x 1))

/-- **Six exponentials, algebraically shifted** (Waldschmidt 1988 Cor. 2.1): with `x` (two)
and `y` (three) `ℚ`-linearly independent and any six algebraic `βᵢⱼ`, some
`e^{xᵢyⱼ − βᵢⱼ}` is transcendental. -/
def SixExponentialsShifted : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (β : Fin 2 → Fin 3 → ℂ),
    LinearIndependent ℚ x → LinearIndependent ℚ y → (∀ i j, IsAlgebraic ℚ (β i j)) →
    ∃ i j, Transcendental ℚ (exp (x i * y j - β i j))

/-- `𝓛̃`: the `ℚ̄`-span of `1` and all logarithms of nonzero algebraic numbers, i.e. numbers
`β₀ + β₁λ₁ + ⋯ + βₙλₙ` with `βᵢ` algebraic and each `e^{λᵢ}` algebraic.  Stated through
`exp λᵢ`, so it is branch-free. -/
def LogAlgSpan : Set ℂ :=
  {z | ∃ (n : ℕ) (β : Fin (n + 1) → ℂ) (ℓ : Fin n → ℂ), (∀ i, IsAlgebraic ℚ (β i)) ∧
    (∀ i, IsAlgebraic ℚ (exp (ℓ i))) ∧ z = β 0 + ∑ i, β i.succ * ℓ i}

/-- **Strong six exponentials theorem** (D. Roy): with `x` (two) and `y` (three) `ℚ`-linearly
independent, some `xᵢyⱼ` lies outside `LogAlgSpan`. -/
def StrongSixExponentials : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j, x i * y j ∉ LogAlgSpan

end LeanFormalizations.Literature

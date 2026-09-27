/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Challenge support - the literature hypotheses, Mathlib-only

Part of the audit surface: `Challenge.lean` imports this.  It mirrors
`src/LeanFormalizations/Literature/Pisot.lean` as its own module on purpose, so Lean's
auto-generated `_proof_N` names come out the same as in the development (comparator demands
byte-identical declarations).
-/

namespace LeanFormalizations.Literature

/-- A Pisot number: a real algebraic integer `β > 1` whose other conjugates lie in the open unit
disc (conjugates = complex roots of the minimal polynomial, which are distinct). -/
def IsPisot (β : ℝ) : Prop :=
  1 < β ∧ IsIntegral ℤ β ∧ ∀ z ∈ ((minpoly ℚ β).aroots ℂ).erase (β : ℂ), ‖z‖ < 1

/-- Dubickas (2022), Lemma 6: for algebraic `α > 1`, `q ≥ 1` and positive integers
`s₀ < s₁ < ⋯`, either some `α^(s_m)` is Pisot, or `‖q α^(s_k)‖ > e^(−ε s_k)` eventually, for
every `ε > 0` (`‖·‖` = distance to the nearest integer). -/
def Dubickas2022 : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → 1 < α → ∀ q : ℕ, 0 < q → ∀ s : ℕ → ℕ, StrictMono s → 0 < s 0 →
    (∃ m, IsPisot (α ^ s m)) ∨
    ∀ ε > (0 : ℝ), ∃ k₀ : ℕ, ∀ k ≥ k₀,
      Real.exp (-(ε * s k)) < |(q : ℝ) * α ^ s k - round ((q : ℝ) * α ^ s k)|

/-- Dubickas (2022), Lemma 8: for a Pisot `β` of degree `≥ 2`, the `n`-th power sum of its other
conjugates is at least `|β₂|ⁿ n^(−λ)` for large `n`, `|β₂|` their largest modulus. -/
def Dubickas2022PisotGap : Prop :=
  ∀ β : ℝ, IsPisot β → 2 ≤ (minpoly ℚ β).natDegree →
    ∃ lam > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((((minpoly ℚ β).aroots ℂ).erase (β : ℂ)).map (‖·‖)).fold max 0 ^ n * (n : ℝ) ^ (-lam) ≤
        ‖((((minpoly ℚ β).aroots ℂ).erase (β : ℂ)).map (· ^ n)).sum‖

end LeanFormalizations.Literature

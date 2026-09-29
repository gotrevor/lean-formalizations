/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature and conjecture inputs from Waldschmidt's 2023 survey

M. Waldschmidt, *The four exponentials problem and Schanuel's conjecture*, in *Transcendence in
Algebra, Combinatorics, Geometry and Number Theory* (Springer, 2023); author PDF
`webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/FourExponentialsSchanuel.pdf`.  Every
field below (`ℚ` versus `ℚ̄`) was checked against the **rendered** page, not a pdftotext dump
(`pdftotext-drops-overbars` in the KB).  The coverage map is `WALDSCHMIDT-2023.md`.

* `AlgIndepLogsConjecture`: survey Conjecture 1 ("weak Schanuel", Calegari–Mazur Conj. 3.9).  Open.
* `BakerHomogeneous`: Baker (1966), the conclusion as the survey states it on p. 4: `1, λ₁, …, λₙ`
  are `ℚ̄`-linearly independent.  Theorem.
* `StrongFourExponentialsConjecture`: survey §6, "Theorem 5 with only two numbers `y₁, y₂`
  instead of three".  Open.  Independence is over `ℚ̄`, as in Theorem 5.
-/
import LeanFormalizations.Literature.ExponentialsKnown

namespace LeanFormalizations.Literature

open Complex

/-- **Conjecture 1 (algebraic independence of logarithms)**: `ℚ`-linearly independent
`λ₁, …, λₙ` with every `e^{λᵢ}` algebraic are algebraically independent over `ℚ`. -/
def AlgIndepLogsConjecture : Prop :=
  ∀ (n : ℕ) (ℓ : Fin n → ℂ), LinearIndependent ℚ ℓ → (∀ i, IsAlgebraic ℚ (exp (ℓ i))) →
    AlgebraicIndependent ℚ ℓ

/-- **Baker's theorem (1966), homogeneous form**: under the same hypotheses, `1, λ₁, …, λₙ` are
linearly independent over the algebraic numbers. -/
def BakerHomogeneous : Prop :=
  ∀ (n : ℕ) (ℓ : Fin n → ℂ), LinearIndependent ℚ ℓ → (∀ i, IsAlgebraic ℚ (exp (ℓ i))) →
    LinearIndependent (integralClosure ℚ ℂ) (Fin.cons (1 : ℂ) ℓ : Fin (n + 1) → ℂ)

/-- **Strong four exponentials conjecture**: with `x` (two) and `y` (two) linearly independent
over `ℚ̄`, some `xᵢyⱼ` lies outside `LogAlgSpan`. -/
def StrongFourExponentialsConjecture : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 2 → ℂ), LinearIndependent (integralClosure ℚ ℂ) x →
    LinearIndependent (integralClosure ℚ ℂ) y → ∃ i j, x i * y j ∉ LogAlgSpan

end LeanFormalizations.Literature

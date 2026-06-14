/-
# Curtis (1990) — shared definitions

The two small definitions that appear in the load-bearing statements of
`Statement.lean` (the designated audit surface). They live here so the proof
engine (`Engine.lean`) and the audit surface (`Statement.lean`) can both refer
to them without an import cycle.

Audit these against the paper alongside `Statement.lean`:
- `IsAdmissible` is Curtis's set `A` (THEOREM, p. 190).
- `evalPoint` attaches a triple to its Frobenius number as a point of `ℂ⁴`.
-/
import Mathlib

open MvPolynomial

namespace LeanFormalizations.NumericalSemigroups.Curtis

/-- Curtis's admissible family `A`: triples `s₁ < s₂ < s₃` with `s₁, s₂` prime
and `s₁ ∤ s₃`, `s₂ ∤ s₃`. -/
def IsAdmissible (s₁ s₂ s₃ : ℕ) : Prop :=
  s₁ < s₂ ∧ s₂ < s₃ ∧ s₁.Prime ∧ s₂.Prime ∧ ¬ s₁ ∣ s₃ ∧ ¬ s₂ ∣ s₃

/-- Evaluation point in `ℂ⁴` for a polynomial in `X₁, X₂, X₃, Y`, attaching a
triple to its Frobenius number `g`. -/
def evalPoint (s₁ s₂ s₃ g : ℕ) : Fin 4 → ℂ :=
  ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ), (g : ℂ)]

end LeanFormalizations.NumericalSemigroups.Curtis

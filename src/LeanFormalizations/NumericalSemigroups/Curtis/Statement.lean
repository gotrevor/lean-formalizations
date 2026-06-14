/-
# Curtis (1990): the Frobenius number has no closed formula for n ≥ 3

Frank Curtis, *On formulas for the Frobenius number of a numerical semigroup*,
Math. Scand. **67** (1990), 190–192.

This file is the **designated audit surface**: the two load-bearing statements,
written to be checked against the paper. The two definitions they reference
(`IsAdmissible`, `evalPoint`) live in `Defs.lean` — audit those too. The proofs
are delegated to `Engine.lean`; the statements here are definitionally identical
to what is proved.

For n = 2 the Frobenius number is `m*n - m - n` (Sylvester; in mathlib as
`frobeniusNumber_pair`). Curtis proves that for n = 3 — and hence all n ≥ 3 —
no such closed form exists. His theorem is in fact stronger than "not a
polynomial": the Frobenius number of a triple is **not even algebraic** over its
generators (its graph lies on no proper hypersurface). The familiar "no finite
set of formulas" statement is then a one-line corollary.

## Status
- `no_finite_polynomial_formula` — **PROVED** (corollary of the main theorem).
- `no_polynomial_relation` — the main theorem, still `sorry` in `Engine.lean`;
  roadmap there. Multi-lap.
-/
import LeanFormalizations.NumericalSemigroups.Curtis.Engine

open MvPolynomial

namespace LeanFormalizations.NumericalSemigroups.Curtis

/-- **Curtis's theorem (1990).** There is no nonzero polynomial
`F ∈ ℂ[X₁, X₂, X₃, Y]` that vanishes on the graph of the Frobenius number over
the admissible family `A`. Equivalently: the Frobenius number of a triple is not
algebraic over its generators. -/
theorem no_polynomial_relation :
    ¬ ∃ F : MvPolynomial (Fin 4) ℂ, F ≠ 0 ∧
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        eval (evalPoint s₁ s₂ s₃ g) F = 0 :=
  no_polynomial_relation_engine

/-- **Corollary.** No finite list of polynomials `f₀, …, f_{k-1} ∈ ℂ[X₁,X₂,X₃]`
computes the Frobenius number piecewise (some `fᵢ` equal to `g` on every
admissible triple). Curtis's proof: `F = ∏ (fᵢ − Y)` would vanish on the graph,
contradicting `no_polynomial_relation`. -/
theorem no_finite_polynomial_formula :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) ℂ),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] (f i) = (g : ℂ) :=
  no_finite_polynomial_formula_engine

end LeanFormalizations.NumericalSemigroups.Curtis

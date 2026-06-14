/-
# Curtis (1990): the Frobenius number has no closed formula for n ≥ 3

Frank Curtis, *On formulas for the Frobenius number of a numerical semigroup*,
Math. Scand. **67** (1990), 190–192.

This file is the **designated audit surface**: the two load-bearing statements,
written to be checked against the paper. Everything they reference is listed in
the README under "What to audit". Both are `sorry` for now (statements first).

For n = 2 the Frobenius number is `m*n - m - n` (Sylvester; in mathlib as
`frobeniusNumber_pair`). Curtis proves that for n = 3 — and hence all n ≥ 3 —
no such closed form exists. His theorem is in fact stronger than "not a
polynomial": the Frobenius number of a triple is **not even algebraic** over its
generators (its graph lies on no proper hypersurface). The familiar "no finite
set of formulas" statement is then a one-line corollary.

## Proof roadmap (Curtis's argument, for when we discharge the `sorry`s)
1. **Lemma 1** (Dirichlet primes in AP + Farey adjacency): for any target ratio
   α and ε > 0 there are coprime `x` (prime), `y` in prescribed residues mod `p`
   with `|α − y/x| < ε`. mathlib has Dirichlet.
2. **Lemma 2**: an exact closed form for `g⟨s₁,s₂,s₃⟩` on a restricted family,
   via the Brauer–Shockley Apéry-set fact `g(S) = (max of S(s)) − s`.
3. **Finish**: feed infinitely many triples whose ratios → an irrational α; after
   homogenizing, the curve vanishes on a whole line, forcing `deg F ≥ (p−1)/2`
   for every prime `p`. Core is "a nonzero 1-variable polynomial has finitely
   many roots" — solidly in mathlib.
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

/-- **Curtis's theorem (1990).** There is no nonzero polynomial
`F ∈ ℂ[X₁, X₂, X₃, Y]` that vanishes on the graph of the Frobenius number over
the admissible family `A`. Equivalently: the Frobenius number of a triple is not
algebraic over its generators. -/
theorem no_polynomial_relation :
    ¬ ∃ F : MvPolynomial (Fin 4) ℂ, F ≠ 0 ∧
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        eval (evalPoint s₁ s₂ s₃ g) F = 0 := by
  sorry

/-- **Corollary.** No finite list of polynomials `f₀, …, f_{k-1} ∈ ℂ[X₁,X₂,X₃]`
computes the Frobenius number piecewise (some `fᵢ` equal to `g` on every
admissible triple). Curtis's proof: `F = ∏ (fᵢ − Y)` would vanish on the graph,
contradicting `no_polynomial_relation`. -/
theorem no_finite_polynomial_formula :
    ¬ ∃ (k : ℕ) (f : Fin k → MvPolynomial (Fin 3) ℂ),
      ∀ s₁ s₂ s₃ g : ℕ, IsAdmissible s₁ s₂ s₃ →
        FrobeniusNumber g {s₁, s₂, s₃} →
        ∃ i, eval ![(s₁ : ℂ), (s₂ : ℂ), (s₃ : ℂ)] (f i) = (g : ℂ) := by
  sorry

end LeanFormalizations.NumericalSemigroups.Curtis

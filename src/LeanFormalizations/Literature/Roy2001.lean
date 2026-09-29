/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Roy's conjecture, and its equivalence with Schanuel's (Roy 2001)

Waldschmidt 2023, §8, Conjecture 7, transcribed from the **rendered** page 10.  Note that the
degree and range bounds are powers `N^{t₀}`, `N^{t₁}`, `N^{s₀}`, `N^{s₁}`, and that the height bound is
`e^N`.

D. Roy, *An arithmetic criterion for the values of the exponential function*, Acta Arith. **97**
(2001), 183–194, and *Small value estimates for the multiplicative group*, Acta Arith. **135**
(2008).  The equivalence with Schanuel's conjecture is Roy (2001a/b); see also Waldschmidt,
*Diophantine Approximation on Linear Algebraic Groups* (2000), Conjecture 15.36.

The equivalence enters as the literature theorem `Roy2001Equivalence`.  It is the only proposed
strategy toward Schanuel (survey §8: "so far it is the only available strategy towards a proof
of it").
-/
import LeanFormalizations.Literature.Schanuel

namespace LeanFormalizations.Literature

open MvPolynomial Filter

/-- Roy's derivation `𝒟 = ∂/∂X₀ + X₁ ∂/∂X₁` on `ℤ[X₀, X₁]`. -/
noncomputable def royD (P : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 2) ℤ :=
  pderiv 0 P + X 1 * pderiv 1 P

/-- **Conjecture 7 (D. Roy)**, as in Waldschmidt 2023 §8. -/
def RoyConjecture : Prop :=
  ∀ (ℓ : ℕ), 0 < ℓ → ∀ (y α : Fin ℓ → ℂ) (s₀ s₁ t₀ t₁ u : ℝ),
    LinearIndependent ℚ y → (∀ j, α j ≠ 0) →
    0 < s₀ → 0 < s₁ → 0 < t₀ → 0 < t₁ → 0 < u →
    max (max 1 t₀) (2 * t₁) < min s₀ (2 * s₁) → min s₀ (2 * s₁) < u →
    max s₀ (s₁ + t₁) < u → u < (1 + t₀ + t₁) / 2 →
    (∀ᶠ N : ℕ in atTop, ∃ P : MvPolynomial (Fin 2) ℤ, P ≠ 0 ∧
      (P.degreeOf 0 : ℝ) ≤ (N : ℝ) ^ t₀ ∧ (P.degreeOf 1 : ℝ) ≤ (N : ℝ) ^ t₁ ∧
      (∀ d, (|((P.coeff d : ℤ) : ℝ)|) ≤ Real.exp N) ∧
      ∀ (k : ℕ) (m : Fin ℓ → ℕ), (k : ℝ) ≤ (N : ℝ) ^ s₀ → (∀ j, (m j : ℝ) ≤ (N : ℝ) ^ s₁) →
        ‖aeval ![∑ j, (m j : ℂ) * y j, ∏ j, α j ^ m j] (royD^[k] P)‖ ≤
          Real.exp (-(N : ℝ) ^ u)) →
    (ℓ : Cardinal) ≤ Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range y ∪ Set.range α))

/-- **Roy (2001)**: Conjecture 7 is equivalent to Schanuel's conjecture. -/
def Roy2001Equivalence : Prop := RoyConjecture ↔ SchanuelConjecture

end LeanFormalizations.Literature

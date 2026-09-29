/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The ℚ̄-independence variant of the shifted six exponentials statement

Trevor, 2026-09-29: record it.  It is **true** but **weaker**.  Write-up:
`ERRATUM-WALDSCHMIDT-2023-SHARP-SIX.md`.

`SixExponentialsShiftedAlg` is the survey's printed statement with ℚ̄-linear independence
instead of ℚ-linear independence.  This is the lap's "overbar repair".

* **True**: it follows from the sharp theorem.  If every `e^{xᵢyⱼ−βᵢⱼ}` were algebraic, sharp six
  would give `xᵢyⱼ = βᵢⱼ` for all `i, j`.  Then `x₁y₁ = β₁₁` and `x₁y₂ = β₁₂` force
  `β₁₂·y₁ = β₁₁·y₂`, a ℚ̄-relation between `y₁` and `y₂`.  If `β₁₁ = β₁₂ = 0`, then `x₁y₁ = 0` with
  `x₁ ≠ 0` (by independence) gives `y₁ = 0`, which contradicts independence.  ℚ̄-independence
  implies ℚ-independence, so sharp six applies.
* **Weaker**: it does not contain the six exponentials theorem, whose hypotheses are over `ℚ`.
  For example `x = (1, √2)` is ℚ-independent but ℚ̄-dependent, so the variant says nothing there.
  The witness `witness_not_algIndep` makes that precise.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Periods
import LeanFormalizations.Literature.Waldschmidt2023

namespace LeanFormalizations.Periods

open LeanFormalizations.Literature Complex

/-- The survey's shifted statement with independence over `ℚ̄` (the lap's proposed repair). -/
def SixExponentialsShiftedAlg : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (β : Fin 2 → Fin 3 → ℂ),
    LinearIndependent (integralClosure ℚ ℂ) x → LinearIndependent (integralClosure ℚ ℂ) y →
    (∀ i j, IsAlgebraic ℚ (β i j)) → ∃ i j, Transcendental ℚ (exp (x i * y j - β i j))

/-- `ℚ̄`-linear independence in `ℂ` implies `ℚ`-linear independence (restriction of scalars along
the injection `ℚ → ℚ̄`). -/
theorem linearIndependent_rat_of_algClosure {n : ℕ} {v : Fin n → ℂ}
    (hv : LinearIndependent (integralClosure ℚ ℂ) v) : LinearIndependent ℚ v := by
  refine hv.restrict_scalars ?_
  intro a b hab
  simpa [Algebra.smul_def, Subtype.ext_iff] using hab

/-- The ℚ̄ variant is a true consequence of the sharp six exponentials theorem. -/
theorem shiftedAlg_of_sharp (h : SixExponentialsSharp) : SixExponentialsShiftedAlg := by
  intro x y β hx hy hβ
  by_contra hcon
  push Not at hcon
  simp only [Transcendental, not_not] at hcon
  -- Sharp six exponentials collapses the whole matrix: `xᵢ yⱼ = βᵢⱼ`.
  have heq := h x y β (linearIndependent_rat_of_algClosure hx)
    (linearIndependent_rat_of_algClosure hy) hβ hcon
  have hx0 : x 0 ≠ 0 := (linearIndependent_rat_of_algClosure hx).ne_zero 0
  by_cases hb : β 0 0 = 0 ∧ β 0 1 = 0
  · -- Degenerate case: `x₀y₀ = 0` with `x₀ ≠ 0` forces `y₀ = 0`, against independence of `y`.
    have hz : x 0 * y 0 = 0 := by rw [heq 0 0, hb.1]
    exact (linearIndependent_rat_of_algClosure hy).ne_zero 0
      (by rcases mul_eq_zero.mp hz with h' | h' <;> [exact absurd h' hx0; exact h'])
  · -- Otherwise `β₀₁ · y₀ − β₀₀ · y₁ = x₀y₁y₀ − x₀y₀y₁ = 0` is a nontrivial `ℚ̄`-relation.
    apply hb
    have key : ∑ i, (![(⟨β 0 1, (hβ 0 1).isIntegral⟩ : integralClosure ℚ ℂ),
        ⟨-β 0 0, ((hβ 0 0).neg).isIntegral⟩, 0] i) • y i = 0 := by
      simp [Fin.sum_univ_three, Algebra.smul_def]
      rw [← heq 0 1, ← heq 0 0]
      ring
    have hzero := (Fintype.linearIndependent_iff.mp hy) _ key
    exact ⟨by simpa [Subtype.ext_iff] using hzero 1, by simpa [Subtype.ext_iff] using hzero 0⟩

/-- It is strictly narrower in scope: `(1, √2)` is `ℚ`-independent but not `ℚ̄`-independent, so
the six exponentials theorem's instances with algebraic `x` fall outside the variant. -/
theorem witness_not_algIndep :
    LinearIndependent ℚ ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ)] ∧
      ¬ LinearIndependent (integralClosure ℚ ℂ) ![(1 : ℂ), ((Real.sqrt 2 : ℝ) : ℂ)] := by
  have hmem : ((Real.sqrt 2 : ℝ) : ℂ) ∈ integralClosure ℚ ℂ := by
    have h2 : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
      norm_cast; rw [Real.sq_sqrt]; norm_num
    exact ⟨Polynomial.X ^ 2 - Polynomial.C 2, by monicity!, by simp [h2]⟩
  refine ⟨?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Rat.smul_def] at hst
    have hre := congrArg Complex.re hst
    simp at hre
    by_cases ht : t = 0
    · subst ht; simp at hre ⊢; exact hre
    · exfalso
      apply irrational_sqrt_two.ne_rat (-s / t)
      push_cast
      field_simp at hre ⊢
      linarith [hre]
  · rw [LinearIndependent.pair_iff]
    push Not
    refine ⟨⟨_, hmem⟩, -1, ?_, ?_⟩
    · simp [Algebra.smul_def]
    · intro h; simp [Subtype.ext_iff] at h

end LeanFormalizations.Periods

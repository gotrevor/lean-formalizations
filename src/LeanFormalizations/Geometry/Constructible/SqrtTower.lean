/-
# Square-root towers and the degree of a constructible number

The algebraic core of Wantzel's theorem (the "convergence" direction needed for the
classical impossibility proofs).

A real number is *constructible* (by compass and straightedge, starting from the
rationals) iff it lies in some field reached from `ℚ` by repeatedly adjoining a
square root — a *square-root tower*. We capture that lattice-theoretically: an
`IntermediateField ℚ ℝ` is a `IsSqrtTower` if it is `⊥`, or obtained from a tower `K`
by adjoining a real `a` with `a * a ∈ K`.

The key fact (`IsSqrtTower.finrank_eq_pow_two`): every square-root tower has degree a
**power of two** over `ℚ`. Each adjunction step has relative degree `≤ 2` (the
element `a` is a root of `X² - (a*a)`), and the tower law multiplies the degrees.

This is exactly the obstruction that kills the three classical construction problems;
`Statement.lean` applies it to `∛2` (degree 3, not a power of 2) to prove the cube
cannot be doubled.

The geometric faithfulness layer — that compass-and-straightedge constructions yield
*precisely* these quadratic towers — is a separate development (see `PENDING_WORK.md`).
-/
import Mathlib

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-- A *square-root tower* over `ℚ` inside `ℝ`: built from `⊥ = ℚ` by repeatedly
adjoining a real square root `a` of an element `a * a` already present. -/
inductive IsSqrtTower : IntermediateField ℚ ℝ → Prop
  | base : IsSqrtTower ⊥
  | step {K : IntermediateField ℚ ℝ} (hK : IsSqrtTower K) {a : ℝ} (ha : a * a ∈ K) :
      IsSqrtTower ((K⟮a⟯).restrictScalars ℚ)

/-- A real number is *constructible* if it lies in some square-root tower over `ℚ`. -/
def IsConstructible (x : ℝ) : Prop :=
  ∃ K : IntermediateField ℚ ℝ, IsSqrtTower K ∧ x ∈ K

variable {K : IntermediateField ℚ ℝ} {a : ℝ}

/-- If `a * a ∈ K`, then `a` is a root of the monic degree-2 polynomial `X² - (a*a)`
over `K`. -/
lemma aeval_X_sq_sub_C (ha : a * a ∈ K) :
    (aeval a) (X ^ 2 - C (⟨a * a, ha⟩ : K)) = 0 := by
  simp only [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply]
  show a ^ 2 - a * a = 0
  ring

/-- An adjoined square root is integral over the base field. -/
lemma isIntegral_of_sq_mem (ha : a * a ∈ K) : IsIntegral K a :=
  ⟨X ^ 2 - C (⟨a * a, ha⟩ : K), monic_X_pow_sub_C _ (by norm_num), aeval_X_sq_sub_C ha⟩

/-- A square-root adjunction has relative degree at most `2`. -/
lemma finrank_adjoin_le_two (ha : a * a ∈ K) : finrank K K⟮a⟯ ≤ 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_of_sq_mem ha)]
  have hdvd : minpoly K a ∣ (X ^ 2 - C (⟨a * a, ha⟩ : K)) :=
    minpoly.dvd K a (aeval_X_sq_sub_C ha)
  have h := natDegree_le_of_dvd hdvd (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  rwa [natDegree_X_pow_sub_C] at h

/-- **The degree of a square-root tower is a power of two.** -/
theorem IsSqrtTower.finrank_eq_pow_two {K : IntermediateField ℚ ℝ} (h : IsSqrtTower K) :
    ∃ n : ℕ, finrank ℚ K = 2 ^ n := by
  induction h with
  | base => exact ⟨0, by simp [IntermediateField.finrank_bot]⟩
  | @step K hK a ha ih =>
    obtain ⟨n, hn⟩ := ih
    haveI : FiniteDimensional ℚ K := .of_finrank_pos (by rw [hn]; positivity)
    haveI hai : IsIntegral K a := isIntegral_of_sq_mem ha
    haveI : FiniteDimensional K K⟮a⟯ := adjoin.finiteDimensional hai
    have hstep : finrank ℚ ((K⟮a⟯).restrictScalars ℚ) = finrank ℚ K * finrank K K⟮a⟯ :=
      (Module.finrank_mul_finrank ℚ K K⟮a⟯).symm
    have hle : finrank K K⟮a⟯ ≤ 2 := finrank_adjoin_le_two ha
    have hpos : 1 ≤ finrank K K⟮a⟯ := finrank_pos
    have hcases : finrank K K⟮a⟯ = 1 ∨ finrank K K⟮a⟯ = 2 := by omega
    rcases hcases with h1 | h2
    · exact ⟨n, by rw [hstep, hn, h1, mul_one]⟩
    · exact ⟨n + 1, by rw [hstep, hn, h2, pow_succ]⟩

end LeanFormalizations.Constructible

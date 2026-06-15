/-
# Trisecting the 60° angle is impossible — `cos 20°` has degree 3 over ℚ

The arithmetic heart of the second classical problem. To trisect a `60°` angle with
compass and straightedge means constructing `cos 20°` from `cos 60° = 1/2` (which is
rational, hence available). We show `cos 20°` is *not* constructible.

Write `α = 2 cos 20°`. The triple-angle identity `cos 3θ = 4cos³θ - 3cosθ` with
`cos 60° = 1/2` gives `8cos³20° - 6cos20° - 1 = 0`, i.e.
`α³ - 3α - 1 = 0`. The monic cubic `X³ - 3X - 1` is irreducible over `ℚ` (a rational
root would be an integer dividing `1`, and neither `±1` is a root), so it is the
minimal polynomial of `α` and `[ℚ(α) : ℚ] = 3`. As `3` is not a power of `2`, `α`
— and therefore `cos 20°` — is not constructible.
-/
import Mathlib
import LeanFormalizations.Geometry.Constructible.SqrtTower

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-- `cos 20°` (the angle `π/9`). -/
noncomputable def cos20 : ℝ := Real.cos (Real.pi / 9)

/-- `2 cos 20°`, the root of the monic cubic `X³ - 3X - 1`. -/
noncomputable def twoCos20 : ℝ := 2 * cos20

/-- The triple-angle identity, specialised: `8cos³20° - 6cos20° - 1 = 0`, i.e.
`(2cos20°)³ - 3(2cos20°) - 1 = 0`. -/
lemma twoCos20_cubic : twoCos20 ^ 3 - 3 * twoCos20 - 1 = 0 := by
  have h1 : Real.cos (3 * (Real.pi / 9)) = 4 * cos20 ^ 3 - 3 * cos20 := Real.cos_three_mul _
  have h2 : Real.cos (3 * (Real.pi / 9)) = 1 / 2 := by
    rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring, Real.cos_pi_div_three]
  have h3 : 4 * cos20 ^ 3 - 3 * cos20 = 1 / 2 := by rw [← h1, h2]
  unfold twoCos20
  linear_combination 2 * h3

/-- The trisection cubic `X³ - 3X - 1` is monic over `ℚ`. -/
lemma monic_cubic : (X ^ 3 - C 3 * X - C 1 : ℚ[X]).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3 <;> compute_degree!

/-- **`X³ - 3X - 1` is irreducible over `ℚ`.** A rational root of this monic integer
cubic must be an integer dividing the constant term `1` (`±1`), and neither is a root
(`1-3-1=-3`, `-1+3-1=1`). -/
theorem trisection_cubic_irreducible :
    Irreducible (X ^ 3 - C 3 * X - C 1 : ℚ[X]) := by
  have hxeqgen : ∀ x : ℚ, IsRoot (X ^ 3 - C 3 * X - C 1 : ℚ[X]) x →
      x ^ 3 - 3 * x - 1 = 0 := by
    intro x hx
    have := hx
    simp only [IsRoot.def, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at this
    linarith [this]
  have hd : (X ^ 3 - C 3 * X - C 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, hd]; omega
  · intro x hx
    set pℤ : ℤ[X] := X ^ 3 - C 3 * X - C 1 with hpZ
    have hmonic : pℤ.Monic := by
      apply monic_of_natDegree_le_of_coeff_eq_one 3 <;> · rw [hpZ]; compute_degree!
    have haeval : (aeval x) pℤ = 0 := by
      rw [hpZ]
      simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
      have := hxeqgen x hx; linarith [this]
    obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmonic haeval
    have hzx : (z : ℚ) = x := by rw [← hz, eq_intCast]
    have hzeq : z ^ 3 - 3 * z - 1 = 0 := by
      have h := hxeqgen x hx; rw [← hzx] at h; exact_mod_cast h
    have hunit : z * (z ^ 2 - 3) = 1 := by linear_combination hzeq
    obtain ⟨h, -⟩ | ⟨h, -⟩ := Int.eq_one_or_neg_one_of_mul_eq_one' hunit <;>
      subst h <;> norm_num at hzeq

/-- `2 cos 20°` is a root of the monic `X³ - 3X - 1 ∈ ℚ[X]`. -/
lemma aeval_twoCos20 : (aeval twoCos20) (X ^ 3 - C 3 * X - C 1 : ℚ[X]) = 0 := by
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
  linear_combination twoCos20_cubic

/-- `2 cos 20°` is integral over `ℚ`. -/
lemma isIntegral_twoCos20 : IsIntegral ℚ twoCos20 :=
  ⟨X ^ 3 - C 3 * X - C 1, monic_cubic, aeval_twoCos20⟩

/-- The minimal polynomial of `2 cos 20°` over `ℚ` is `X³ - 3X - 1`. -/
lemma minpoly_twoCos20 : minpoly ℚ twoCos20 = X ^ 3 - C 3 * X - C 1 :=
  (minpoly.eq_of_irreducible_of_monic trisection_cubic_irreducible aeval_twoCos20
    monic_cubic).symm

/-- `[ℚ(2cos20°) : ℚ] = 3`. -/
theorem finrank_adjoin_twoCos20 : finrank ℚ ℚ⟮twoCos20⟯ = 3 := by
  rw [IntermediateField.adjoin.finrank isIntegral_twoCos20, minpoly_twoCos20]
  compute_degree!

end LeanFormalizations.Constructible

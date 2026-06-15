/-
# The regular nonagon (9-gon) is not constructible — `cos 40°` has degree 3 over ℚ

A companion to angle trisection (and a case of the Gauss–Wantzel theorem on
constructible polygons). Constructing a regular `9`-gon amounts to constructing
`cos(2π/9) = cos 40°`; we show it is not constructible.

Write `α = 2 cos 40°`. Since `3 · 40° = 120°` and `cos 120° = -1/2`, the triple-angle
identity gives `8cos³40° - 6cos40° + 1 = 0`, i.e. `α³ - 3α + 1 = 0`. The monic cubic
`X³ - 3X + 1` is irreducible over `ℚ` (a rational root would be an integer dividing
`1`, and neither `±1` is a root), so `[ℚ(α) : ℚ] = 3`, not a power of two.
-/
import Mathlib
import LeanFormalizations.Geometry.Constructible.SqrtTower

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-- `cos 40°` (the angle `2π/9`). -/
noncomputable def cos40 : ℝ := Real.cos (2 * Real.pi / 9)

/-- `2 cos 40°`, the root of the monic cubic `X³ - 3X + 1`. -/
noncomputable def twoCos40 : ℝ := 2 * cos40

/-- `8cos³40° - 6cos40° + 1 = 0`, i.e. `(2cos40°)³ - 3(2cos40°) + 1 = 0`. -/
lemma twoCos40_cubic : twoCos40 ^ 3 - 3 * twoCos40 + 1 = 0 := by
  have h1 : Real.cos (3 * (2 * Real.pi / 9)) = 4 * cos40 ^ 3 - 3 * cos40 :=
    Real.cos_three_mul _
  have h2 : Real.cos (3 * (2 * Real.pi / 9)) = -1 / 2 := by
    rw [show 3 * (2 * Real.pi / 9) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]; norm_num
  have h3 : 4 * cos40 ^ 3 - 3 * cos40 = -1 / 2 := by rw [← h1, h2]
  unfold twoCos40
  linear_combination 2 * h3

/-- The nonagon cubic `X³ - 3X + 1` is monic over `ℚ`. -/
lemma monic_nonagon_cubic : (X ^ 3 - C 3 * X + C 1 : ℚ[X]).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3 <;> compute_degree!

/-- **`X³ - 3X + 1` is irreducible over `ℚ`.** A rational root of this monic integer
cubic is an integer dividing the constant `1` (`±1`); neither is a root
(`1-3+1=-1`, `-1+3+1=3`). -/
theorem nonagon_cubic_irreducible :
    Irreducible (X ^ 3 - C 3 * X + C 1 : ℚ[X]) := by
  have hxeqgen : ∀ x : ℚ, IsRoot (X ^ 3 - C 3 * X + C 1 : ℚ[X]) x →
      x ^ 3 - 3 * x + 1 = 0 := by
    intro x hx
    have := hx
    simp only [IsRoot.def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at this
    linarith [this]
  have hd : (X ^ 3 - C 3 * X + C 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, hd]; omega
  · intro x hx
    set pℤ : ℤ[X] := X ^ 3 - C 3 * X + C 1 with hpZ
    have hmonic : pℤ.Monic := by
      apply monic_of_natDegree_le_of_coeff_eq_one 3 <;> · rw [hpZ]; compute_degree!
    have haeval : (aeval x) pℤ = 0 := by
      rw [hpZ]
      simp only [map_add, map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
      have := hxeqgen x hx; linarith [this]
    obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmonic haeval
    have hzx : (z : ℚ) = x := by rw [← hz, eq_intCast]
    have hzeq : z ^ 3 - 3 * z + 1 = 0 := by
      have h := hxeqgen x hx; rw [← hzx] at h; exact_mod_cast h
    have hunit : IsUnit z := isUnit_of_dvd_one ⟨-(z ^ 2 - 3), by linear_combination hzeq⟩
    rcases Int.isUnit_iff.mp hunit with h | h <;> subst h <;> norm_num at hzeq

/-- `2 cos 40°` is a root of the monic `X³ - 3X + 1 ∈ ℚ[X]`. -/
lemma aeval_twoCos40 : (aeval twoCos40) (X ^ 3 - C 3 * X + C 1 : ℚ[X]) = 0 := by
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
  linear_combination twoCos40_cubic

/-- `2 cos 40°` is integral over `ℚ`. -/
lemma isIntegral_twoCos40 : IsIntegral ℚ twoCos40 :=
  ⟨X ^ 3 - C 3 * X + C 1, monic_nonagon_cubic, aeval_twoCos40⟩

/-- The minimal polynomial of `2 cos 40°` over `ℚ` is `X³ - 3X + 1`. -/
lemma minpoly_twoCos40 : minpoly ℚ twoCos40 = X ^ 3 - C 3 * X + C 1 :=
  (minpoly.eq_of_irreducible_of_monic nonagon_cubic_irreducible aeval_twoCos40
    monic_nonagon_cubic).symm

/-- `[ℚ(2cos40°) : ℚ] = 3`. -/
theorem finrank_adjoin_twoCos40 : finrank ℚ ℚ⟮twoCos40⟯ = 3 := by
  rw [IntermediateField.adjoin.finrank isIntegral_twoCos40, minpoly_twoCos40]
  compute_degree!

/-- **The regular nonagon is not constructible.** `2 cos 40°` is not constructible
(`[ℚ(2cos40°):ℚ] = 3`), hence neither is `cos 40°`, so a regular `9`-gon cannot be
drawn with compass and straightedge. -/
theorem twoCos40_not_constructible : ¬ IsConstructible twoCos40 :=
  not_isConstructible_of_finrank_adjoin_eq_three finrank_adjoin_twoCos40

theorem cos40_not_constructible : ¬ IsConstructible cos40 := by
  rintro ⟨K, hK, hmem⟩
  refine twoCos40_not_constructible ⟨K, hK, ?_⟩
  show (2 : ℝ) * cos40 ∈ K
  rw [two_mul]; exact K.add_mem hmem hmem

end LeanFormalizations.Constructible

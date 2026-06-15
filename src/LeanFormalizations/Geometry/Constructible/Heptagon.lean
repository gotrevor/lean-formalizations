/-
# The regular heptagon (7-gon) is not constructible — `cos(2π/7)` has degree 3 over ℚ

Another case of the Gauss–Wantzel theorem. Constructing a regular `7`-gon amounts to
constructing `cos(2π/7)`; we show it is not constructible.

Write `c = cos(2π/7)` and `α = 2c`. From `4·(2π/7) = 2π − 3·(2π/7)` we get
`cos(4θ) = cos(3θ)` with `θ = 2π/7`. Expanding both sides as polynomials in `c` gives
`8c⁴ − 4c³ − 8c² + 3c + 1 = 0`, which factors as `(c − 1)(8c³ + 4c² − 4c − 1) = 0`.
Since `c ≠ 1`, the cubic factor vanishes, and in terms of `α = 2c` this is
`α³ + α² − 2α − 1 = 0`. The monic cubic `X³ + X² − 2X − 1` has no rational root
(an integer root would divide `1`, and neither `±1` works), so it is irreducible and
`[ℚ(α) : ℚ] = 3`, not a power of two.
-/
import Mathlib
import LeanFormalizations.Geometry.Constructible.SqrtTower

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-- `cos(2π/7)`. -/
noncomputable def cosHept : ℝ := Real.cos (2 * Real.pi / 7)

/-- `2 cos(2π/7)`, the root of the monic cubic `X³ + X² − 2X − 1`. -/
noncomputable def twoCosHept : ℝ := 2 * cosHept

/-- `(2cos(2π/7))³ + (2cos(2π/7))² − 2·(2cos(2π/7)) − 1 = 0`. -/
lemma twoCosHept_cubic : twoCosHept ^ 3 + twoCosHept ^ 2 - 2 * twoCosHept - 1 = 0 := by
  unfold twoCosHept cosHept
  set θ := 2 * Real.pi / 7 with hθ
  set c := Real.cos θ with hc
  have hc2 : Real.cos (2 * θ) = 2 * c ^ 2 - 1 := Real.cos_two_mul θ
  have hc3 : Real.cos (3 * θ) = 4 * c ^ 3 - 3 * c := Real.cos_three_mul θ
  have hc4 : Real.cos (4 * θ) = 2 * (Real.cos (2 * θ)) ^ 2 - 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring]; exact Real.cos_two_mul (2 * θ)
  have heq : Real.cos (4 * θ) = Real.cos (3 * θ) := by
    rw [show 4 * θ = 2 * Real.pi - 3 * θ by rw [hθ]; ring, Real.cos_two_pi_sub]
  have hthis : 2 * (2 * c ^ 2 - 1) ^ 2 - 1 = 4 * c ^ 3 - 3 * c := by
    rw [hc4, hc2, hc3] at heq; exact heq
  have hpoly : 8 * c ^ 4 - 4 * c ^ 3 - 8 * c ^ 2 + 3 * c + 1 = 0 := by linear_combination hthis
  have hne1 : c ≠ 1 := by
    intro h
    rw [hc, Real.cos_eq_one_iff_of_lt_of_lt
      (by rw [hθ]; nlinarith [Real.pi_pos]) (by rw [hθ]; nlinarith [Real.pi_pos])] at h
    rw [hθ] at h; nlinarith [Real.pi_pos]
  have hfac : (c - 1) * (8 * c ^ 3 + 4 * c ^ 2 - 4 * c - 1) = 0 := by linear_combination hpoly
  have hcube : 8 * c ^ 3 + 4 * c ^ 2 - 4 * c - 1 = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith [h] : c = 1) hne1
    · exact h
  linear_combination hcube

/-- The heptagon cubic `X³ + X² − 2X − 1` is monic over `ℚ`. -/
lemma monic_heptagon_cubic : (X ^ 3 + X ^ 2 - C 2 * X - C 1 : ℚ[X]).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3 <;> compute_degree!

/-- **`X³ + X² − 2X − 1` is irreducible over `ℚ`.** A rational root of this monic integer
cubic is an integer dividing the constant `1` (`±1`); neither is a root
(`1+1-2-1=-1`, `-1+1+2-1=1`). -/
theorem heptagon_cubic_irreducible :
    Irreducible (X ^ 3 + X ^ 2 - C 2 * X - C 1 : ℚ[X]) := by
  have hxeqgen : ∀ x : ℚ, IsRoot (X ^ 3 + X ^ 2 - C 2 * X - C 1 : ℚ[X]) x →
      x ^ 3 + x ^ 2 - 2 * x - 1 = 0 := by
    intro x hx
    have := hx
    simp only [IsRoot.def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at this
    linarith [this]
  have hd : (X ^ 3 + X ^ 2 - C 2 * X - C 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, hd]; omega
  · intro x hx
    set pℤ : ℤ[X] := X ^ 3 + X ^ 2 - C 2 * X - C 1 with hpZ
    have hmonic : pℤ.Monic := by
      apply monic_of_natDegree_le_of_coeff_eq_one 3 <;> · rw [hpZ]; compute_degree!
    have haeval : (aeval x) pℤ = 0 := by
      rw [hpZ]
      simp only [map_add, map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
      have := hxeqgen x hx; linarith [this]
    obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmonic haeval
    have hzx : (z : ℚ) = x := by rw [← hz, eq_intCast]
    have hzeq : z ^ 3 + z ^ 2 - 2 * z - 1 = 0 := by
      have h := hxeqgen x hx; rw [← hzx] at h; exact_mod_cast h
    have hunit : IsUnit z := isUnit_of_dvd_one ⟨z ^ 2 + z - 2, by linear_combination -hzeq⟩
    rcases Int.isUnit_iff.mp hunit with h | h <;> subst h <;> norm_num at hzeq

/-- `2 cos(2π/7)` is a root of the monic `X³ + X² − 2X − 1 ∈ ℚ[X]`. -/
lemma aeval_twoCosHept : (aeval twoCosHept) (X ^ 3 + X ^ 2 - C 2 * X - C 1 : ℚ[X]) = 0 := by
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
  linear_combination twoCosHept_cubic

/-- `2 cos(2π/7)` is integral over `ℚ`. -/
lemma isIntegral_twoCosHept : IsIntegral ℚ twoCosHept :=
  ⟨X ^ 3 + X ^ 2 - C 2 * X - C 1, monic_heptagon_cubic, aeval_twoCosHept⟩

/-- The minimal polynomial of `2 cos(2π/7)` over `ℚ` is `X³ + X² − 2X − 1`. -/
lemma minpoly_twoCosHept : minpoly ℚ twoCosHept = X ^ 3 + X ^ 2 - C 2 * X - C 1 :=
  (minpoly.eq_of_irreducible_of_monic heptagon_cubic_irreducible aeval_twoCosHept
    monic_heptagon_cubic).symm

/-- `[ℚ(2cos(2π/7)) : ℚ] = 3`. -/
theorem finrank_adjoin_twoCosHept : finrank ℚ ℚ⟮twoCosHept⟯ = 3 := by
  rw [IntermediateField.adjoin.finrank isIntegral_twoCosHept, minpoly_twoCosHept]
  compute_degree!

/-- **The regular heptagon is not constructible.** `2 cos(2π/7)` is not constructible
(`[ℚ(2cos(2π/7)):ℚ] = 3`), hence neither is `cos(2π/7)`, so a regular `7`-gon cannot be
drawn with compass and straightedge. -/
theorem twoCosHept_not_constructible : ¬ IsConstructible twoCosHept :=
  not_isConstructible_of_finrank_adjoin_eq_three finrank_adjoin_twoCosHept

theorem cosHept_not_constructible : ¬ IsConstructible cosHept := by
  rintro ⟨K, hK, hmem⟩
  refine twoCosHept_not_constructible ⟨K, hK, ?_⟩
  show (2 : ℝ) * cosHept ∈ K
  rw [two_mul]; exact K.add_mem hmem hmem

end LeanFormalizations.Constructible

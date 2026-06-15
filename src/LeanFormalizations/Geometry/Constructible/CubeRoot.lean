/-
# The cube root of 2 has degree 3 over ℚ

The arithmetic heart of the "doubling the cube is impossible" theorem: the real
number `∛2` generates a degree-3 extension of `ℚ`.

`minpoly ℚ ∛2 = X³ - 2`, which is irreducible over `ℚ` (Kummer / Eisenstein at 2),
so `[ℚ(∛2) : ℚ] = 3`. Since `3 ∤ 2ⁿ`, no tower of quadratic extensions can contain
`∛2` — see `SqrtTower.lean`.
-/
import Mathlib

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-- The real cube root of `2`, `2^(1/3)`. -/
noncomputable def cbrt2 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

lemma cbrt2_pos : 0 < cbrt2 := Real.rpow_pos_of_pos (by norm_num) _

/-- `(∛2)³ = 2`. -/
lemma cbrt2_cube : cbrt2 ^ 3 = 2 := by
  rw [cbrt2, ← Real.rpow_natCast (_ ^ _) 3, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `∛2` is irrational: from `(∛2)³ = 2` and `2 = 2¹` with `3 ∤ 1`. -/
lemma irrational_cbrt2 : Irrational cbrt2 := by
  have h : cbrt2 ^ 3 = ((2 : ℤ) : ℝ) := by push_cast; exact cbrt2_cube
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact irrational_nrt_of_n_not_dvd_multiplicity 3 (by norm_num) 2 h (by simp [multiplicity_self])

/-- `2` is not a cube in `ℚ`. (Bridge to the real irrationality of `∛2`.) -/
lemma no_rat_cube_two : ∀ b : ℚ, b ^ 3 ≠ 2 := by
  intro b hb
  apply irrational_cbrt2
  refine ⟨b, ?_⟩
  -- `(b:ℝ)` and `∛2` are equal because `· ^ 3` is injective on `ℝ` (odd power).
  have hodd : StrictMono (fun a : ℝ => a ^ 3) := Odd.strictMono_pow (by decide)
  have hbc : (b : ℝ) ^ 3 = cbrt2 ^ 3 := by rw [cbrt2_cube]; exact_mod_cast hb
  exact hodd.injective hbc

/-- `X³ - 2` is irreducible over `ℚ` (Kummer: `2` is not a cube). -/
lemma irreducible_X3_sub_2 : Irreducible (X ^ 3 - C 2 : ℚ[X]) :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) no_rat_cube_two

/-- `∛2` is a root of the monic `X³ - 2 ∈ ℚ[X]`. -/
lemma aeval_cbrt2 : (aeval cbrt2) (X ^ 3 - C 2 : ℚ[X]) = 0 := by
  simp only [map_sub, map_pow, aeval_X, map_ofNat]
  rw [cbrt2_cube]; ring

/-- `∛2` is integral over `ℚ` (root of the monic `X³ - 2`). -/
lemma isIntegral_cbrt2 : IsIntegral ℚ cbrt2 :=
  ⟨X ^ 3 - C 2, monic_X_pow_sub_C 2 (by norm_num), aeval_cbrt2⟩

/-- The minimal polynomial of `∛2` over `ℚ` is `X³ - 2`. -/
lemma minpoly_cbrt2 : minpoly ℚ cbrt2 = X ^ 3 - C 2 :=
  (minpoly.eq_of_irreducible_of_monic irreducible_X3_sub_2 aeval_cbrt2
    (monic_X_pow_sub_C 2 (by norm_num))).symm

/-- `[ℚ(∛2) : ℚ] = 3`. -/
theorem finrank_adjoin_cbrt2 : finrank ℚ ℚ⟮cbrt2⟯ = 3 := by
  rw [IntermediateField.adjoin.finrank isIntegral_cbrt2, minpoly_cbrt2,
    natDegree_X_pow_sub_C]

end LeanFormalizations.Constructible

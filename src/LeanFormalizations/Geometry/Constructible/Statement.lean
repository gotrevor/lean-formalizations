/-
# Doubling the cube is impossible (audit surface)

The classical Greek problem of *doubling the cube*: given a cube, construct with
compass and straightedge a cube of twice the volume — i.e. construct the length
`∛2` from a unit length. This is impossible (Wantzel 1837).

This file is the faithful **audit surface**. The headline:

* `cbrt2_not_constructible` : `¬ IsConstructible (2 ^ (1/3))` — the real cube root of
  `2` lies in no square-root tower over `ℚ`.

stated against the definitions audited in `SqrtTower.lean` (`IsConstructible`,
`IsSqrtTower`) and `CubeRoot.lean` (`cbrt2`). The proof is the two-line classical
argument: a constructible number has degree a power of `2` over `ℚ`
(`IsSqrtTower.finrank_eq_pow_two`), but `[ℚ(∛2) : ℚ] = 3` (`finrank_adjoin_cbrt2`),
and `3` is not a power of `2`.

`#print axioms cbrt2_not_constructible` is `[propext, Classical.choice, Quot.sound]`.
-/
import LeanFormalizations.Geometry.Constructible.CubeRoot
import LeanFormalizations.Geometry.Constructible.SqrtTower

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-- `3` does not divide any power of `2`. -/
lemma three_not_dvd_two_pow (n : ℕ) : ¬ (3 ∣ 2 ^ n) := fun hd => by
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

/-- **Doubling the cube is impossible.** The real cube root of `2` is not
constructible by compass and straightedge: it lies in no tower of quadratic
extensions of `ℚ`.

Proof: any constructible number generates a field of degree `2ⁿ` over `ℚ`
(`IsSqrtTower.finrank_eq_pow_two`), whereas `ℚ(∛2)` has degree `3`
(`finrank_adjoin_cbrt2`), and `3 ∤ 2ⁿ`. -/
theorem cbrt2_not_constructible : ¬ IsConstructible cbrt2 := by
  rintro ⟨K, hK, hmem⟩
  obtain ⟨n, hn⟩ := hK.finrank_eq_pow_two
  haveI : FiniteDimensional ℚ K := .of_finrank_pos (by rw [hn]; positivity)
  -- `ℚ(∛2) ≤ K`, so `[ℚ(∛2):ℚ] ∣ [K:ℚ] = 2ⁿ`
  have hle : ℚ⟮cbrt2⟯ ≤ K := by
    rw [IntermediateField.adjoin_simple_le_iff]; exact hmem
  have hdvd : finrank ℚ ℚ⟮cbrt2⟯ ∣ finrank ℚ K :=
    ⟨_, (IntermediateField.finrank_bot_mul_relfinrank hle).symm⟩
  rw [finrank_adjoin_cbrt2, hn] at hdvd
  exact three_not_dvd_two_pow n hdvd

/-- Restatement: one cannot construct a length whose cube is `2` (the doubled unit
cube). Phrased on the defining property `x ^ 3 = 2` rather than the name `cbrt2`. -/
theorem no_constructible_cube_root_of_two :
    ¬ ∃ x : ℝ, IsConstructible x ∧ x ^ 3 = 2 := by
  rintro ⟨x, hx, hx3⟩
  -- the real cube root of `2` is unique, so `x = cbrt2`
  have : x = cbrt2 := by
    have hmono : StrictMono (fun t : ℝ => t ^ 3) := Odd.strictMono_pow (by decide)
    exact hmono.injective (by rw [hx3, cbrt2_cube])
  exact cbrt2_not_constructible (this ▸ hx)

end LeanFormalizations.Constructible

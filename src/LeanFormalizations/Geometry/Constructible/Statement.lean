/-
# Two classical impossibilities (audit surface)

Two of the three classical Greek construction problems, formalised via the algebraic
core of Wantzel's theorem (`SqrtTower.lean`): a compass-and-straightedge–constructible
real number generates an extension of `ℚ` of degree a power of two.

* **Doubling the cube.** `cbrt2_not_constructible : ¬ IsConstructible (∛2)`.
  `[ℚ(∛2):ℚ] = 3` (`finrank_adjoin_cbrt2`), not a power of two.
* **Trisecting the 60° angle.** `cos20_not_constructible : ¬ IsConstructible (cos 20°)`.
  `[ℚ(2cos20°):ℚ] = 3` (`finrank_adjoin_twoCos20`), not a power of two.

This file is the faithful **audit surface**, stating the headlines against the
audited definitions `IsConstructible` / `IsSqrtTower` (`SqrtTower.lean`) and the
degree computations in `CubeRoot.lean` / `Trisection.lean`.

`#print axioms` on each headline is `[propext, Classical.choice, Quot.sound]`.
-/
import LeanFormalizations.Geometry.Constructible.CubeRoot
import LeanFormalizations.Geometry.Constructible.Trisection

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-! ### Doubling the cube -/

/-- **Doubling the cube is impossible.** The real cube root of `2` is not
constructible by compass and straightedge: it lies in no tower of quadratic
extensions of `ℚ`. (Any constructible number has degree a power of two over `ℚ`,
while `[ℚ(∛2):ℚ] = 3`.) -/
theorem cbrt2_not_constructible : ¬ IsConstructible cbrt2 :=
  not_isConstructible_of_finrank_adjoin_eq_three finrank_adjoin_cbrt2

/-- Restatement: one cannot construct a length whose cube is `2` (the doubled unit
cube), phrased on the defining property `x ^ 3 = 2`. -/
theorem no_constructible_cube_root_of_two :
    ¬ ∃ x : ℝ, IsConstructible x ∧ x ^ 3 = 2 := by
  rintro ⟨x, hx, hx3⟩
  have : x = cbrt2 := by
    have hmono : StrictMono (fun t : ℝ => t ^ 3) := Odd.strictMono_pow (by decide)
    exact hmono.injective (by rw [hx3, cbrt2_cube])
  exact cbrt2_not_constructible (this ▸ hx)

/-! ### Trisecting the 60° angle -/

/-- **Trisecting a 60° angle is impossible.** `2 cos 20°` is not constructible
(`[ℚ(2cos20°):ℚ] = 3`, not a power of two). -/
theorem twoCos20_not_constructible : ¬ IsConstructible twoCos20 :=
  not_isConstructible_of_finrank_adjoin_eq_three finrank_adjoin_twoCos20

/-- Consequently `cos 20°` itself is not constructible: a field containing `cos 20°`
also contains `2 cos 20°`. Since `cos 60° = 1/2` is rational (constructible), the
`60°` angle cannot be trisected with compass and straightedge. -/
theorem cos20_not_constructible : ¬ IsConstructible cos20 := by
  rintro ⟨K, hK, hmem⟩
  refine twoCos20_not_constructible ⟨K, hK, ?_⟩
  show (2 : ℝ) * cos20 ∈ K
  rw [two_mul]; exact K.add_mem hmem hmem

end LeanFormalizations.Constructible

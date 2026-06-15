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
import LeanFormalizations.Geometry.Constructible.Nonagon
import LeanFormalizations.Geometry.Constructible.Heptagon
import LeanFormalizations.Geometry.Constructible.ConstructiblePoint
import LeanFormalizations.Geometry.Constructible.Converse

open Polynomial IntermediateField Module

namespace LeanFormalizations.Constructible

/-! ### Wantzel's theorem: the algebra–geometry equivalence

The headline of the whole module. A real number lies in a tower of quadratic
extensions of `ℚ` **iff** the point `(x,0)` is constructible by compass and straightedge
from `(0,0)` and `(1,0)` — `isConstructible_iff_constructiblePoint`. The forward
direction is the degree obstruction (`SqrtTower.lean`); the geometry→algebra bridge is
`ConstructiblePoint.isConstructible_coords`; the algebra→geometry converse is the
explicit ruler-and-compass arithmetic of `Converse.lean`. -/

/-! ### A positive construction: the regular pentagon

The converse direction (`Converse.lean`) is not vacuous: it actually *builds* numbers.
`cos(π/5) = (1 + √5)/4` is assembled from rationals and `√5` by the compass field
operations, so it is constructible — witnessing the regular pentagon/decagon. -/

/-- **`cos(π/5)` is constructible.** It equals `(1 + √5)/4`; `√5` is a compass square
root and the field operations finish the job (`Converse.lean`). Hence the regular
pentagon is constructible — the positive side of Gauss–Wantzel. -/
theorem isConstructible_cos_pi_div_five : IsConstructible (Real.cos (Real.pi / 5)) := by
  refine isConstructible_iff_constructiblePoint.mpr ?_
  rw [show ConstructiblePoint (Real.cos (Real.pi / 5), 0)
      = AxisConstructible (Real.cos (Real.pi / 5)) from rfl, Real.cos_pi_div_five]
  have h5 : AxisConstructible (Real.sqrt 5) := by
    simpa using (AxisConstructible.natCast 5).sqrt (by positivity)
  have h4 : AxisConstructible (4 : ℝ) := by simpa using AxisConstructible.natCast 4
  exact (AxisConstructible.one.add h5).div h4

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

/-- **Doubling the cube, as a geometric construction.** Via the Layer-2 faithfulness
bridge (`ConstructiblePoint.isConstructible_coords`): the point `(∛2, 0)`, whose
abscissa is the doubled-cube edge length, cannot be obtained from `(0,0)` and `(1,0)`
by any finite sequence of line/circle intersections, since `[ℚ(∛2):ℚ] = 3`. -/
theorem cbrt2_point_not_constructible : ¬ ConstructiblePoint (cbrt2, 0) :=
  ConstructiblePoint.not_of_finrank_fst_eq_three finrank_adjoin_cbrt2

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

/-! ### The regular nonagon (Gauss–Wantzel)

A bonus from the same engine: the regular `9`-gon needs `cos 40°`, which has degree
`3` over `ℚ`. Headlines `cos40_not_constructible` / `twoCos40_not_constructible` live
in `Nonagon.lean`. -/

/-! ### The regular heptagon (Gauss–Wantzel)

The regular `7`-gon needs `cos(2π/7)`, of degree `3` over `ℚ`. Headlines
`cosHept_not_constructible` / `twoCosHept_not_constructible` live in `Heptagon.lean`. -/

/-- **The regular heptagon is not constructible, geometrically.** The point
`(2cos(2π/7), 0)` cannot be constructed by compass and straightedge, since
`[ℚ(2cos(2π/7)):ℚ] = 3`. -/
theorem heptagon_point_not_constructible : ¬ ConstructiblePoint (twoCosHept, 0) :=
  ConstructiblePoint.not_of_finrank_fst_eq_three finrank_adjoin_twoCosHept

/-! ### Squaring the circle (conditional on Lindemann's transcendence of `π`)

`√π` is the side of a square with the same area as the unit circle. Constructing it
is impossible because `√π` is transcendental. mathlib does not yet have the
transcendence of `π` (only the analytic part of Lindemann–Weierstrass), so we take it
as an explicit hypothesis `Transcendental ℚ π`; the rest is unconditional and
axiom-clean. See `PENDING_WORK.md`. -/

/-- **Squaring the circle is impossible** (given that `π` is transcendental over `ℚ`).
If `√π` were constructible it would be algebraic (`IsConstructible.isAlgebraic`),
hence so would `π = (√π)²`, contradicting the transcendence of `π`. -/
theorem squaring_the_circle_impossible (hπ : Transcendental ℚ Real.pi) :
    ¬ IsConstructible (Real.sqrt Real.pi) := by
  intro h
  apply hπ
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  rw [← hsq]
  exact h.isAlgebraic.pow 2

end LeanFormalizations.Constructible

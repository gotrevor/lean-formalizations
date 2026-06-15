/-
# Geometric faithfulness: constructible points

Layer 2 of Wantzel's theorem. Layer 1 (`SqrtTower.lean`) developed the *algebraic*
notion `IsConstructible : ℝ → Prop` (membership in a square-root tower over `ℚ`) and
proved the degree obstruction. This file connects that algebra to the *geometry* of
compass-and-straightedge constructions.

We define `ConstructiblePoint : ℝ × ℝ → Prop` inductively: starting from the two base
points `(0,0)` and `(1,0)`, a point is constructible if it is the intersection of two
lines, a line and a circle, or two circles, each determined by already-constructible
points. Lines pass through two distinct constructible points; circles are centred at a
constructible point with radius equal to the distance between two constructible points.

The main theorem `ConstructiblePoint.isConstructible_coords` shows that every
constructible point has *both coordinates* algebraically constructible. Together with
Layer 1's degree obstruction this gives genuine impossibility statements.

The algebraic heart is two coordinate-solving lemmas, `line_meet_line` and
`line_meet_circle`, which feed the field-closure / quadratic-formula API from Layer 1.
-/
import LeanFormalizations.Geometry.Constructible.SqrtTower

open IntermediateField Module

namespace LeanFormalizations.Constructible

/-! ### Coordinate-solving lemmas

These reduce a geometric intersection to algebra over the constructible field. -/

/-- **Two lines meet in a constructible point.** If `(x, y)` satisfies two linear
equations `α₁x + β₁y = γ₁`, `α₂x + β₂y = γ₂` whose coefficients are constructible and
whose determinant `α₁β₂ − α₂β₁` is nonzero (the lines are not parallel), then both
coordinates are constructible — by Cramer's rule, each is a ratio of constructibles. -/
theorem line_meet_line {α₁ β₁ γ₁ α₂ β₂ γ₂ x y : ℝ}
    (hα₁ : IsConstructible α₁) (hβ₁ : IsConstructible β₁) (hγ₁ : IsConstructible γ₁)
    (hα₂ : IsConstructible α₂) (hβ₂ : IsConstructible β₂) (hγ₂ : IsConstructible γ₂)
    (e₁ : α₁ * x + β₁ * y = γ₁) (e₂ : α₂ * x + β₂ * y = γ₂)
    (hdet : α₁ * β₂ - α₂ * β₁ ≠ 0) :
    IsConstructible x ∧ IsConstructible y := by
  have hx : x * (α₁ * β₂ - α₂ * β₁) = γ₁ * β₂ - γ₂ * β₁ := by
    linear_combination β₂ * e₁ - β₁ * e₂
  have hy : y * (α₁ * β₂ - α₂ * β₁) = α₁ * γ₂ - α₂ * γ₁ := by
    linear_combination α₁ * e₂ - α₂ * e₁
  refine ⟨?_, ?_⟩
  · have hxc : x = (γ₁ * β₂ - γ₂ * β₁) * (α₁ * β₂ - α₂ * β₁)⁻¹ := by
      rw [← hx, mul_inv_cancel_right₀ hdet]
    rw [hxc]
    exact ((hγ₁.mul hβ₂).sub (hγ₂.mul hβ₁)).mul ((hα₁.mul hβ₂).sub (hα₂.mul hβ₁)).inv
  · have hyc : y = (α₁ * γ₂ - α₂ * γ₁) * (α₁ * β₂ - α₂ * β₁)⁻¹ := by
      rw [← hy, mul_inv_cancel_right₀ hdet]
    rw [hyc]
    exact ((hα₁.mul hγ₂).sub (hα₂.mul hγ₁)).mul ((hα₁.mul hβ₂).sub (hα₂.mul hβ₁)).inv

/-- **A line meets a circle in a constructible point.** If `(x, y)` lies on a line
`αx + βy = γ` with `(α, β) ≠ (0,0)` and on a circle `(x − c₁)² + (y − c₂)² = ρ`, all of
whose coefficients are constructible, then both coordinates are constructible.
Eliminating one variable from the line into the circle yields a monic quadratic with
constructible coefficients; `IsConstructible.of_quadratic` (the quadratic formula)
closes it. -/
theorem line_meet_circle {α β γ c₁ c₂ ρ x y : ℝ}
    (hα : IsConstructible α) (hβ : IsConstructible β) (hγ : IsConstructible γ)
    (hc₁ : IsConstructible c₁) (hc₂ : IsConstructible c₂) (hρ : IsConstructible ρ)
    (eline : α * x + β * y = γ)
    (ecirc : (x - c₁) ^ 2 + (y - c₂) ^ 2 = ρ)
    (hαβ : α ≠ 0 ∨ β ≠ 0) :
    IsConstructible x ∧ IsConstructible y := by
  rcases eq_or_ne β 0 with hβ0 | hβ0
  · -- Vertical line: `α ≠ 0`, so `x = γ/α`; the circle is a monic quadratic in `y`.
    have hα0 : α ≠ 0 := by rcases hαβ with h | h; exacts [h, absurd hβ0 h]
    have hxα : α * x = γ := by rw [hβ0] at eline; linear_combination eline
    have hxval : x = γ * α⁻¹ := by rw [← hxα, mul_comm α x, mul_inv_cancel_right₀ hα0]
    have hxc : IsConstructible x := by rw [hxval]; exact hγ.mul hα.inv
    refine ⟨hxc, ?_⟩
    have hquad : y ^ 2 + (-(2 * c₂)) * y + (c₂ * c₂ + ((x - c₁) * (x - c₁) - ρ)) = 0 := by
      linear_combination ecirc
    refine IsConstructible.of_quadratic ?_ ?_ hquad
    · exact (IsConstructible.two.mul hc₂).neg
    · exact (hc₂.mul hc₂).add (((hxc.sub hc₁).mul (hxc.sub hc₁)).sub hρ)
  · -- General line: solve `y` from the line, substitute, monic quadratic in `x`.
    have hSpos : 0 < α ^ 2 + β ^ 2 := by
      have h2 : (0 : ℝ) < β ^ 2 := (sq_nonneg β).lt_of_ne ((pow_ne_zero 2 hβ0).symm)
      nlinarith [sq_nonneg α]
    have hSne : α ^ 2 + β ^ 2 ≠ 0 := ne_of_gt hSpos
    set b := (-(2 * β ^ 2 * c₁) - 2 * α * (γ - β * c₂)) * (α ^ 2 + β ^ 2)⁻¹ with hbdef
    set c := (β ^ 2 * c₁ ^ 2 + (γ - β * c₂) ^ 2 - ρ * β ^ 2) * (α ^ 2 + β ^ 2)⁻¹ with hcdef
    have key : (α ^ 2 + β ^ 2) * x ^ 2 + (-(2 * β ^ 2 * c₁) - 2 * α * (γ - β * c₂)) * x
        + (β ^ 2 * c₁ ^ 2 + (γ - β * c₂) ^ 2 - ρ * β ^ 2) = 0 := by
      linear_combination β ^ 2 * ecirc - (γ - α * x + β * y - 2 * β * c₂) * eline
    have hquad : x ^ 2 + b * x + c = 0 := by
      rw [hbdef, hcdef]; field_simp; linear_combination key
    have hxc : IsConstructible x := by
      refine IsConstructible.of_quadratic ?_ ?_ hquad
      · rw [hbdef]
        exact ((((IsConstructible.two.mul hβ.sq).mul hc₁).neg).sub
          ((IsConstructible.two.mul hα).mul (hγ.sub (hβ.mul hc₂)))).mul
          (hα.sq.add hβ.sq).inv
      · rw [hcdef]
        exact (((hβ.sq.mul hc₁.sq).add (hγ.sub (hβ.mul hc₂)).sq).sub (hρ.mul hβ.sq)).mul
          (hα.sq.add hβ.sq).inv
    refine ⟨hxc, ?_⟩
    have hyβ : β * y = γ - α * x := by linear_combination eline
    have hyval : y = (γ - α * x) * β⁻¹ := by
      rw [← hyβ, mul_comm β y, mul_inv_cancel_right₀ hβ0]
    rw [hyval]; exact (hγ.sub (hα.mul hxc)).mul hβ.inv

/-- **Two circles meet in a constructible point.** If `(x, y)` lies on two distinct
circles (distinct centres) with constructible data, its coordinates are constructible.
Subtracting the two circle equations cancels the quadratic terms, leaving the *radical
axis* — a line with constructible coefficients, nondegenerate because the centres
differ. The point lies on that line and on the first circle, so `line_meet_circle`
closes it. -/
theorem circle_meet_circle {c₁ c₂ ρ₁ d₁ d₂ ρ₂ x y : ℝ}
    (hc₁ : IsConstructible c₁) (hc₂ : IsConstructible c₂) (hρ₁ : IsConstructible ρ₁)
    (hd₁ : IsConstructible d₁) (hd₂ : IsConstructible d₂) (hρ₂ : IsConstructible ρ₂)
    (ecirc₁ : (x - c₁) ^ 2 + (y - c₂) ^ 2 = ρ₁)
    (ecirc₂ : (x - d₁) ^ 2 + (y - d₂) ^ 2 = ρ₂)
    (hne : c₁ ≠ d₁ ∨ c₂ ≠ d₂) :
    IsConstructible x ∧ IsConstructible y := by
  have eline : 2 * (d₁ - c₁) * x + 2 * (d₂ - c₂) * y
      = ρ₁ - ρ₂ - c₁ ^ 2 + d₁ ^ 2 - c₂ ^ 2 + d₂ ^ 2 := by
    linear_combination ecirc₁ - ecirc₂
  have hαβ : (2 * (d₁ - c₁) : ℝ) ≠ 0 ∨ (2 * (d₂ - c₂) : ℝ) ≠ 0 := by
    rcases hne with h | h
    · exact Or.inl (mul_ne_zero two_ne_zero (sub_ne_zero.mpr h.symm))
    · exact Or.inr (mul_ne_zero two_ne_zero (sub_ne_zero.mpr h.symm))
  exact line_meet_circle
    (IsConstructible.two.mul (hd₁.sub hc₁))
    (IsConstructible.two.mul (hd₂.sub hc₂))
    (((((hρ₁.sub hρ₂).sub hc₁.sq).add hd₁.sq).sub hc₂.sq).add hd₂.sq)
    hc₁ hc₂ hρ₁ eline ecirc₁ hαβ

/-! ### The geometric predicate and the faithfulness bridge -/

/-- `p` lies on the line through points `A` and `B`: its displacement from `A` is
parallel to `B − A` (zero cross-product). -/
def OnLine (A B p : ℝ × ℝ) : Prop :=
  (B.1 - A.1) * (p.2 - A.2) = (B.2 - A.2) * (p.1 - A.1)

/-- `p` lies on the circle centred at `C` whose radius is the distance from `P` to `Q`. -/
def OnCircle (C P Q p : ℝ × ℝ) : Prop :=
  (p.1 - C.1) ^ 2 + (p.2 - C.2) ^ 2 = (Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2

/-- **Compass-and-straightedge constructible points.** Starting from `(0,0)` and
`(1,0)`, a point is constructible if it is the intersection of two lines, a line and a
circle, or two circles, each determined by already-constructible points. This is the
faithful geometric definition; `isConstructible_coords` shows its coordinates land in
the algebraic constructible field of Layer 1. -/
inductive ConstructiblePoint : ℝ × ℝ → Prop
  | origin : ConstructiblePoint (0, 0)
  | unit : ConstructiblePoint (1, 0)
  | inter_ll {A B C D p : ℝ × ℝ}
      (hA : ConstructiblePoint A) (hB : ConstructiblePoint B)
      (hC : ConstructiblePoint C) (hD : ConstructiblePoint D)
      (h1 : OnLine A B p) (h2 : OnLine C D p)
      (hnp : (B.1 - A.1) * (D.2 - C.2) - (B.2 - A.2) * (D.1 - C.1) ≠ 0) :
      ConstructiblePoint p
  | inter_lc {A B C P Q p : ℝ × ℝ}
      (hA : ConstructiblePoint A) (hB : ConstructiblePoint B)
      (hC : ConstructiblePoint C) (hP : ConstructiblePoint P) (hQ : ConstructiblePoint Q)
      (hAB : A ≠ B)
      (h1 : OnLine A B p) (h2 : OnCircle C P Q p) :
      ConstructiblePoint p
  | inter_cc {C₁ P₁ Q₁ C₂ P₂ Q₂ p : ℝ × ℝ}
      (hC₁ : ConstructiblePoint C₁) (hP₁ : ConstructiblePoint P₁) (hQ₁ : ConstructiblePoint Q₁)
      (hC₂ : ConstructiblePoint C₂) (hP₂ : ConstructiblePoint P₂) (hQ₂ : ConstructiblePoint Q₂)
      (hne : C₁ ≠ C₂)
      (h1 : OnCircle C₁ P₁ Q₁ p) (h2 : OnCircle C₂ P₂ Q₂ p) :
      ConstructiblePoint p

/-- **Geometric faithfulness.** Every compass-and-straightedge constructible point has
*both* coordinates in the algebraic constructible field. This is the bridge that lets
the Layer-1 degree obstruction rule out actual ruler-and-compass constructions. -/
theorem ConstructiblePoint.isConstructible_coords {p : ℝ × ℝ} (hp : ConstructiblePoint p) :
    IsConstructible p.1 ∧ IsConstructible p.2 := by
  induction hp with
  | origin => exact ⟨by simpa using isConstructible_ratCast 0, by simpa using isConstructible_ratCast 0⟩
  | unit => exact ⟨by simpa using isConstructible_ratCast 1, by simpa using isConstructible_ratCast 0⟩
  | @inter_ll A B C D p hA hB hC hD h1 h2 hnp ihA ihB ihC ihD =>
    obtain ⟨hA1, hA2⟩ := ihA; obtain ⟨hB1, hB2⟩ := ihB
    obtain ⟨hC1, hC2⟩ := ihC; obtain ⟨hD1, hD2⟩ := ihD
    simp only [OnLine] at h1 h2
    refine line_meet_line (hB2.sub hA2) (hA1.sub hB1)
      (((hB2.sub hA2).mul hA1).add ((hA1.sub hB1).mul hA2))
      (hD2.sub hC2) (hC1.sub hD1)
      (((hD2.sub hC2).mul hC1).add ((hC1.sub hD1).mul hC2))
      (by linear_combination -h1) (by linear_combination -h2) ?_
    have hdet : (B.2 - A.2) * (C.1 - D.1) - (D.2 - C.2) * (A.1 - B.1)
        = (B.1 - A.1) * (D.2 - C.2) - (B.2 - A.2) * (D.1 - C.1) := by ring
    rw [hdet]; exact hnp
  | @inter_lc A B C P Q p hA hB hC hP hQ hAB h1 h2 ihA ihB ihC ihP ihQ =>
    obtain ⟨hA1, hA2⟩ := ihA; obtain ⟨hB1, hB2⟩ := ihB; obtain ⟨hC1, hC2⟩ := ihC
    obtain ⟨hP1, hP2⟩ := ihP; obtain ⟨hQ1, hQ2⟩ := ihQ
    have hABc : A.1 ≠ B.1 ∨ A.2 ≠ B.2 := by
      rw [← not_and_or, ← Prod.ext_iff]; exact hAB
    simp only [OnLine] at h1
    refine line_meet_circle (hB2.sub hA2) (hA1.sub hB1)
      (((hB2.sub hA2).mul hA1).add ((hA1.sub hB1).mul hA2))
      hC1 hC2 (((hQ1.sub hP1).sq).add ((hQ2.sub hP2).sq))
      (by linear_combination -h1) h2 ?_
    rcases hABc with h | h
    · exact Or.inr (sub_ne_zero.mpr h)
    · exact Or.inl (sub_ne_zero.mpr h.symm)
  | @inter_cc C₁ P₁ Q₁ C₂ P₂ Q₂ p hC₁ hP₁ hQ₁ hC₂ hP₂ hQ₂ hne h1 h2
      ihC₁ ihP₁ ihQ₁ ihC₂ ihP₂ ihQ₂ =>
    obtain ⟨hC₁1, hC₁2⟩ := ihC₁; obtain ⟨hP₁1, hP₁2⟩ := ihP₁; obtain ⟨hQ₁1, hQ₁2⟩ := ihQ₁
    obtain ⟨hC₂1, hC₂2⟩ := ihC₂; obtain ⟨hP₂1, hP₂2⟩ := ihP₂; obtain ⟨hQ₂1, hQ₂2⟩ := ihQ₂
    have hnec : C₁.1 ≠ C₂.1 ∨ C₁.2 ≠ C₂.2 := by
      rw [← not_and_or, ← Prod.ext_iff]; exact hne
    exact circle_meet_circle hC₁1 hC₁2 (((hQ₁1.sub hP₁1).sq).add ((hQ₁2.sub hP₁2).sq))
      hC₂1 hC₂2 (((hQ₂1.sub hP₂1).sq).add ((hQ₂2.sub hP₂2).sq))
      h1 h2 hnec

/-! ### A positive witness: the predicate is genuinely inhabited

Beyond the two base points, the classic equilateral-triangle construction (two unit
circles centred at `(0,0)` and `(1,0)` meeting at `(1/2, √3/2)`) is captured — evidence
that the definition is faithful to real compass-and-straightedge capability, not
vacuously small. (This is also the construction of a `60°` angle.) -/
theorem constructiblePoint_equilateral_vertex :
    ConstructiblePoint (1 / 2, Real.sqrt 3 / 2) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ConstructiblePoint.inter_cc
    ConstructiblePoint.origin ConstructiblePoint.origin ConstructiblePoint.unit
    ConstructiblePoint.unit ConstructiblePoint.origin ConstructiblePoint.unit
    (by norm_num [Prod.ext_iff]) ?_ ?_
  · show ((1 / 2 : ℝ) - 0) ^ 2 + (Real.sqrt 3 / 2 - 0) ^ 2 = ((1 : ℝ) - 0) ^ 2 + ((0 : ℝ) - 0) ^ 2
    linear_combination hs / 4
  · show ((1 / 2 : ℝ) - 1) ^ 2 + (Real.sqrt 3 / 2 - 0) ^ 2 = ((1 : ℝ) - 0) ^ 2 + ((0 : ℝ) - 0) ^ 2
    linear_combination hs / 4

/-- **The geometric obstruction.** A point whose first coordinate generates a degree-3
extension of `ℚ` cannot be reached by compass and straightedge — its coordinate would
have to be algebraically constructible, hence of degree a power of two. This is the
bridge that turns the Layer-1 degree computations into honest geometric impossibility
statements (e.g. doubling the cube: the point `(∛2, 0)` is not constructible). -/
theorem ConstructiblePoint.not_of_finrank_fst_eq_three {p : ℝ × ℝ}
    (h : Module.finrank ℚ ℚ⟮p.1⟯ = 3) : ¬ ConstructiblePoint p :=
  fun hp => not_isConstructible_of_finrank_adjoin_eq_three h hp.isConstructible_coords.1

/-- Symmetric version for the second coordinate. -/
theorem ConstructiblePoint.not_of_finrank_snd_eq_three {p : ℝ × ℝ}
    (h : Module.finrank ℚ ℚ⟮p.2⟯ = 3) : ¬ ConstructiblePoint p :=
  fun hp => not_isConstructible_of_finrank_adjoin_eq_three h hp.isConstructible_coords.2

end LeanFormalizations.Constructible

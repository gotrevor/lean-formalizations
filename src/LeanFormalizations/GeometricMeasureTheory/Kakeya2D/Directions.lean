/-
# The δ-net of directions on the circle (ladder K3, brick 2)

The Córdoba `L²` estimate (K4) is run against a *finite family of δ-tubes* of distinct
directions inside `Sδ`. This file builds the directions explicitly as points on the unit circle,

  `dir θ := (cos θ, sin θ)`,

and supplies exactly the two facts the `L²` sum consumes:

* `norm_dir` — each `dir θ` is a unit vector, so `exists_tube_subset_thickening` (K3 brick 1)
  places a δ-tube of direction `dir θ` inside `Sδ` (`exists_tube_family` below);
* `dir_det` / `dir_sep` — the **angular-separation lower bound**. The lines-invariant
  separation of two directions is the determinant `det[dir θ, dir φ] = sin(φ−θ)`, and Jordan's
  inequality (`Real.mul_abs_le_abs_sin`) bounds it below by `(2/π)|φ−θ|`. For the arithmetic net
  `θ_k = k·δ` this gives separation `s_{jk} ≥ (2/π)|k−j|δ`, so the K2 overlap bound becomes
  `|T_j ∩ T_k| ≲ δ/(|k−j|+1)` — the summable tail that makes the Córdoba sum `≈ δ·log(1/δ)`.

Reference: A. Córdoba (1977); R. O. Davies (1971). See `PLAN.md` (K3, K4).
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Discretize
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Set MeasureTheory Metric RealInnerProductSpace Matrix
open scoped Real

namespace LeanFormalizations.Kakeya2D

/-- The unit direction at angle `θ` on the circle: `dir θ = (cos θ, sin θ)`. -/
noncomputable def dir (θ : ℝ) : Plane := !₂[Real.cos θ, Real.sin θ]

@[simp] theorem dir_zero (θ : ℝ) : dir θ 0 = Real.cos θ := rfl
@[simp] theorem dir_one (θ : ℝ) : dir θ 1 = Real.sin θ := rfl

/-- Each `dir θ` is a **unit vector** (`cos²θ + sin²θ = 1`). -/
theorem norm_dir (θ : ℝ) : ‖dir θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, dir_zero, dir_one,
    show ‖Real.cos θ‖ ^ 2 = (Real.cos θ) ^ 2 by simp [Real.norm_eq_abs, sq_abs],
    show ‖Real.sin θ‖ ^ 2 = (Real.sin θ) ^ 2 by simp [Real.norm_eq_abs, sq_abs],
    Real.cos_sq_add_sin_sq]
  exact Real.sqrt_one

/-- **The directional determinant is the sine of the angle gap.** The lines-invariant separation
of `dir θ` and `dir φ` used by the K2 overlap bound `volume_inter_tube_le` is exactly
`det[dir θ, dir φ] = cos θ · sin φ − sin θ · cos φ = sin(φ − θ)`. -/
theorem dir_det (θ φ : ℝ) :
    dir θ 0 * dir φ 1 - dir θ 1 * dir φ 0 = Real.sin (φ - θ) := by
  rw [dir_zero, dir_one, dir_zero, dir_one, Real.sin_sub]; ring

/-- **Angular-separation lower bound (Jordan's inequality).** For angle gaps within `[-π/2, π/2]`
the directional separation `|det[dir θ, dir φ]|` is at least `(2/π)|φ − θ|`. This is the lower
bound on the K2 denominator that turns the overlap sum into the convergent `δ·log(1/δ)` tail. -/
theorem dir_sep {θ φ : ℝ} (h : |φ - θ| ≤ π / 2) :
    2 / π * |φ - θ| ≤ |dir θ 0 * dir φ 1 - dir θ 1 * dir φ 0| := by
  rw [dir_det]; exact Real.mul_abs_le_abs_sin h

/-- **K3 brick 2 — the tube family.** For a Kakeya set `S`, a single choice of base points places
a δ-tube of *every* direction `dir θ` inside the δ-neighbourhood `Sδ`. Restricting `θ` to an
arithmetic net `{k·δ}` then yields the δ-separated family of `≈ δ⁻¹` tubes that the Córdoba `L²`
estimate (K4) consumes; the separation of its members is controlled by `dir_sep`. -/
theorem exists_tube_family {S : Set Plane} (h : IsKakeya S) (δ : ℝ) :
    ∃ a : ℝ → Plane, ∀ θ : ℝ, tube (a θ) (dir θ) δ ⊆ thickening S δ := by
  choose a ha using fun θ : ℝ => exists_tube_subset_thickening h (dir θ) (norm_dir θ)
  exact ⟨a, ha⟩

/-- **The K2↔K3 interface: indexed overlap bound.** Two δ-tubes whose directions are the
arithmetic-net angles `j·δ` and `k·δ` overlap in area `≤ 6π δ / (|k − j| + 1)`. This is the
*convergent tail* that the Córdoba `L²` denominator sums: combining the K2 area bound
`volume_inter_tube_le` (`≤ 12δ²/(s+δ)`) with the Jordan separation `dir_sep`
(`s ≥ (2/π)|k−j|δ`) collapses the geometric overlap to the harmonic profile `δ/(|k−j|+1)`.
Summing it over the `≈ δ⁻¹ × δ⁻¹` index pairs gives the `δ·log(1/δ)` `L²` mass (K4). -/
theorem volume_inter_dirTube_le {a b : Plane} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (c : ℝ) {j k : ℕ} (hsep : |(k : ℝ) - j| * δ ≤ π / 2) :
    volume (tube a (dir (c + (j : ℝ) * δ)) δ ∩ tube b (dir (c + (k : ℝ) * δ)) δ)
      ≤ ENNReal.ofReal (6 * π * δ / (|(k : ℝ) - j| + 1)) := by
  have hπ := Real.pi_pos
  have hm0 : 0 ≤ |(k : ℝ) - j| := abs_nonneg _
  -- the base angle `c` cancels in the gap: `(c+kδ)-(c+jδ) = (k-j)δ` (shift invariance)
  have hgap : |(c + (k : ℝ) * δ) - (c + (j : ℝ) * δ)| = |(k : ℝ) - j| * δ := by
    rw [show (c + (k : ℝ) * δ) - (c + (j : ℝ) * δ) = ((k : ℝ) - j) * δ from by ring,
      abs_mul, abs_of_pos hδ]
  have hov := volume_inter_tube_le (a := a) (b := b)
      (norm_dir (c + (j : ℝ) * δ)) (norm_dir (c + (k : ℝ) * δ)) hδ hδ1
  have hslow : 2 / π * (|(k : ℝ) - j| * δ)
      ≤ |dir (c + (j : ℝ) * δ) 0 * dir (c + (k : ℝ) * δ) 1
          - dir (c + (j : ℝ) * δ) 1 * dir (c + (k : ℝ) * δ) 0| := by
    have h := dir_sep (θ := c + (j : ℝ) * δ) (φ := c + (k : ℝ) * δ) (by rw [hgap]; exact hsep)
    rwa [hgap] at h
  refine hov.trans (ENNReal.ofReal_le_ofReal ?_)
  set s := |dir (c + (j : ℝ) * δ) 0 * dir (c + (k : ℝ) * δ) 1
      - dir (c + (j : ℝ) * δ) 1 * dir (c + (k : ℝ) * δ) 0| with hs_def
  set m := |(k : ℝ) - j| with hm_def
  have hs0 : 0 ≤ s := abs_nonneg _
  have hden1 : 0 < s + δ := by linarith
  have hden2 : 0 < m + 1 := by linarith
  have h2 : 2 * (m * δ) ≤ s * π := by
    have h := hslow
    rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at h
    exact h
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [h2, hδ, mul_pos hδ hδ, Real.two_le_pi, hm0,
    mul_le_mul_of_nonneg_left h2 hδ.le]

end LeanFormalizations.Kakeya2D

/-
# Planar Kakeya set conjecture (Davies 1971) — audit surface

This is the faithful **audit surface** for the formalization. To check faithfulness, read
exactly two things against the literature:

* the definitions `IsKakeya` and `KakeyaSetConjectureDim` in `Defs.lean` — these mirror
  `google-deepmind/formal-conjectures`' `FormalConjectures/Wikipedia/Kakeya.lean` verbatim;
* the headline `davies_kakeya_2d` below, which states exactly `KakeyaSetConjectureDim 2`.

The proof splits into the two inequalities, both **proven and axiom-clean**
(`#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound]`):

* `dimH_le_two` (the `≤ 2` half) — trivial, `Engine.lean`;
* `two_le_dimH` (the `≥ 2` half — Davies' actual theorem) — `Selection.lean`, via the SOUND,
  axiom-clean *elementary open-cover / measurable-selection* route
  (`kakeya_hausdorffContentBound_elementary`), which needs no descriptive set theory.

Reference: R. O. Davies, *Some remarks on the Kakeya problem*, Math. Proc. Cambridge
Philos. Soc. **69** (1971), 417–421.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Selection

namespace LeanFormalizations.Kakeya2D

/-- **The planar Kakeya set conjecture (Davies 1971).** Every Kakeya set in `ℝ²` — a set
containing a unit line segment in every direction — has Hausdorff dimension `2`. -/
theorem davies_kakeya_2d : KakeyaSetConjectureDim 2 := by
  intro S h
  exact le_antisymm (dimH_le_two S) (two_le_dimH S h)

/-! ### Anti-vacuity / faithfulness anchors

`KakeyaSetConjectureDim 2` is a `∀`-statement; the anchors below certify it is **not vacuously true**
and that it yields the **correct value** on a concrete witness — guarding against a mis-stated `IsKakeya`
or a degenerate `dimH`. The class of Kakeya sets is non-empty: the closed unit disc contains a unit
segment in every direction (from the centre). Feeding it to the headline gives `dimH = 2` exactly,
end-to-end and axiom-clean. -/

/-- The closed unit disc in `ℝ²` is a Kakeya set (it contains, from the centre, a unit segment in every
direction). The non-vacuity witness for `davies_kakeya_2d`. -/
theorem isKakeya_closedBall :
    IsKakeya (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  rintro v hv
  refine ⟨0, ?_⟩
  rintro _ ⟨t, ⟨ht₀, ht₁⟩, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right, AffineMap.lineMap_apply, zero_add,
    vadd_eq_add, vsub_eq_sub, sub_zero, add_zero, norm_smul, hv, mul_one, Real.norm_eq_abs]
  rwa [abs_of_nonneg ht₀]

/-- **Anti-vacuity anchor.** The headline applied to a concrete Kakeya set (the closed unit disc) gives
the correct value: `dimH (closedBall 0 1) = 2`. Axiom-clean — `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. This certifies `davies_kakeya_2d` is not vacuously true and
that `IsKakeya` / `dimH` are the intended, non-degenerate notions. -/
theorem davies_kakeya_2d_disc_anchor :
    dimH (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) = 2 :=
  davies_kakeya_2d _ isKakeya_closedBall

/-- **Discriminating anti-triviality anchor.** A single straight line — here the `x`-axis
`{p : ℝ² | p 1 = 0}` — is **not** a Kakeya set: it contains a unit segment only in its own direction,
not in the perpendicular direction `e₁`. This guards the most dangerous possible mis-statement of
`IsKakeya` — a `∃`-direction (or otherwise too-weak) form in place of the intended `∀`-direction one,
which would make `davies_kakeya_2d` vacuous on thin sets. Together with `isKakeya_closedBall` it pins
`IsKakeya` from both sides: a genuinely 2-dimensional set satisfies it, a 1-dimensional one does not. -/
theorem not_isKakeya_xAxis :
    ¬ IsKakeya {p : EuclideanSpace ℝ (Fin 2) | p 1 = 0} := by
  intro h
  -- the perpendicular unit direction `e₁`
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ) with hv
  obtain ⟨a, ha⟩ := h v (by rw [hv, PiLp.norm_single]; exact norm_one)
  -- both endpoints of the segment must lie on the axis
  have h0 : a ∈ {p : EuclideanSpace ℝ (Fin 2) | p 1 = 0} :=
    ha (left_mem_affineSegment ℝ a (a + v))
  have h1 : a + v ∈ {p : EuclideanSpace ℝ (Fin 2) | p 1 = 0} :=
    ha (right_mem_affineSegment ℝ a (a + v))
  simp only [Set.mem_setOf_eq] at h0 h1
  -- but `(a + e₁) 1 = a 1 + 1 = 0 + 1 = 1 ≠ 0`
  rw [PiLp.add_apply, hv, PiLp.single_apply, if_pos rfl, h0, zero_add] at h1
  exact one_ne_zero h1

end LeanFormalizations.Kakeya2D

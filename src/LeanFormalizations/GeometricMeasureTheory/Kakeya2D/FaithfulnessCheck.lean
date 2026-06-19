/-
# Independent NL→Lean faithfulness cross-check for the planar-Kakeya headline

This file hardens the *faithfulness* of `davies_kakeya_2d` with an **independent** check that does
not rely on reading our own `Defs.lean`. The natural-language statement of the planar Kakeya
conjecture (Davies 1971) was handed — as prose, deliberately NOT our Lean phrasing — to Harmonic's
Aristotle auto-formalizer (`formalize` mode, 2026-06-19, project `4addbb42-…`). Given only the prose,
it produced the statement reproduced below as `IsKakeyaSet_Aristotle` /
`dimH_eq_two_of_isKakeyaSet`.

We then **machine-check** that this independent formalization is logically equivalent to our headline
`KakeyaSetConjectureDim 2`. The only surface difference is that Aristotle wrote the unit segment with
`segment ℝ a (a + v)` (the convex-combination segment) where our `IsKakeya` uses
`affineSegment ℝ a (a + v)`; these are equal in mathlib (`affineSegment_eq_segment`), so the predicates
— and hence the full theorems — coincide. This is an independent corroboration that our Lean statement
faithfully captures the prose theorem: a second formalizer, with no sight of our definitions, landed on
a provably-equivalent statement, and our proven headline discharges its goal.

All three results below are axiom-clean (`#print axioms = [propext, Classical.choice, Quot.sound]`).
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Statement

open Set

namespace LeanFormalizations.Kakeya2D

/-- **Aristotle's independent formalization of the planar-Kakeya prose** (verbatim, `formalize` mode):
a Kakeya set is one containing a unit `segment` in every direction. (Reproduced here so the equivalence
is self-contained and re-checkable; the original is in the project download `4addbb42-…`.) -/
def IsKakeyaSet_Aristotle (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 →
    ∃ a : EuclideanSpace ℝ (Fin 2), segment ℝ a (a + v) ⊆ S

/-- The independent Kakeya predicate coincides with ours: the sole difference (`segment` vs
`affineSegment`) is the mathlib equality `affineSegment_eq_segment`. -/
theorem kakeya_pred_equiv (S : Set (EuclideanSpace ℝ (Fin 2))) :
    IsKakeya S ↔ IsKakeyaSet_Aristotle S := by
  unfold IsKakeya IsKakeyaSet_Aristotle
  simp_rw [affineSegment_eq_segment]

/-- **Headline faithfulness, machine-checked.** Our `KakeyaSetConjectureDim 2` is logically equivalent
to Aristotle's independent formalization of the same prose. -/
theorem headline_faithful :
    KakeyaSetConjectureDim 2 ↔
      (∀ S : Set (EuclideanSpace ℝ (Fin 2)), IsKakeyaSet_Aristotle S → dimH S = 2) := by
  unfold KakeyaSetConjectureDim
  simp_rw [kakeya_pred_equiv]
  norm_num

/-- Our proven headline discharges Aristotle's `sorry`-shaped goal directly. -/
theorem dimH_eq_two_of_isKakeyaSet
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : IsKakeyaSet_Aristotle S) : dimH S = 2 :=
  davies_kakeya_2d S ((kakeya_pred_equiv S).mpr hS)

end LeanFormalizations.Kakeya2D

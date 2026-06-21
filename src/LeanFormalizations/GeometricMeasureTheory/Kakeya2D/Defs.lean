/-
# Planar Kakeya / Besicovitch set conjecture — faithful definitions (Davies 1971)

These definitions mirror `google-deepmind/formal-conjectures`'
`FormalConjectures/Wikipedia/Kakeya.lean` (`Kakeya.IsKakeya`,
`Kakeya.KakeyaSetConjectureDim`) **verbatim**, so a proof of `davies_kakeya_2d`
in this repo is drop-in portable to that repo's `kakeya_2d` `sorry`.

Reference: R. O. Davies, *Some remarks on the Kakeya problem*, Math. Proc. Cambridge
Philos. Soc. **69** (1971), no. 3, 417–421.
-/
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension

open Set

namespace LeanFormalizations.Kakeya2D

/-- A set `S` in `ℝⁿ` is a **Kakeya set** if it contains a unit line segment in every
direction. (No compactness assumption, matching `formal-conjectures`; for the equivalence
of the definitions with and without compactness see arXiv:2203.15731.) -/
def IsKakeya {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∃ a, affineSegment ℝ a (a + v) ⊆ S

/-- The **Kakeya set conjecture** in dimension `n`: every Kakeya set in `ℝⁿ` has Hausdorff
dimension `n`. Davies (1971) settled `n = 2`; Wang–Zahl (2025) settled `n = 3`. -/
def KakeyaSetConjectureDim (n : ℕ) : Prop :=
  ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsKakeya S → dimH S = n

end LeanFormalizations.Kakeya2D

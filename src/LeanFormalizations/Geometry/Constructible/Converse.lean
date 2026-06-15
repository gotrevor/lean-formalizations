/-
# The converse direction: algebraically constructible ⟹ geometrically constructible

Layer 2 (`ConstructiblePoint.lean`) proved the *forward* faithfulness bridge: every
compass-and-straightedge point has algebraically-constructible coordinates. This file
develops the *converse* — that every `IsConstructible` real is actually realised as a
coordinate of a `ConstructiblePoint` — which upgrades Wantzel's theorem to a genuine
equivalence between the algebra and the geometry.

The strategy: let `AxisConstructible x := ConstructiblePoint (x, 0)` be the reals
appearing on the constructed `x`-axis. We show this set is a subfield of `ℝ` closed
under real square roots, by giving the explicit ruler-and-compass construction for each
field operation. A square-root-tower induction (built on those closure lemmas) then
shows every constructible number lands on the axis.

This is the genuine geometric content of "you can add, multiply, invert and take square
roots with compass and straightedge". It is being developed incrementally; the additive
constructions are in place, with multiplication / inversion / square root and the final
tower induction to follow.
-/
import LeanFormalizations.Geometry.Constructible.ConstructiblePoint

namespace LeanFormalizations.Constructible

open ConstructiblePoint IntermediateField

/-- A real number is *axis-constructible* if the point `(x, 0)` can be constructed by
compass and straightedge. The forward bridge shows `AxisConstructible x → IsConstructible
x`; the goal of this file is the converse. -/
def AxisConstructible (x : ℝ) : Prop := ConstructiblePoint (x, 0)

/-- `0` is on the axis: it is the origin. -/
theorem AxisConstructible.zero : AxisConstructible 0 := ConstructiblePoint.origin

/-- `1` is on the axis: it is the unit point. -/
theorem AxisConstructible.one : AxisConstructible 1 := ConstructiblePoint.unit

/-- **Addition by compass.** Given `(a,0)` and `(b,0)`, the point `(a+b, 0)` is the
intersection of the `x`-axis with the circle centred at `(a,0)` of radius `|b|` (the
distance from the origin to `(b,0)`). -/
theorem AxisConstructible.add {a b : ℝ} (ha : AxisConstructible a) (hb : AxisConstructible b) :
    AxisConstructible (a + b) :=
  ConstructiblePoint.inter_lc ConstructiblePoint.origin ConstructiblePoint.unit
    ha ConstructiblePoint.origin hb
    (by norm_num [Prod.ext_iff])
    (by simp only [OnLine]; ring)
    (by simp only [OnCircle]; ring)

/-- **Negation by compass.** Given `(a,0)`, the point `(-a, 0)` is the second
intersection of the `x`-axis with the circle centred at the origin through `(a,0)`. -/
theorem AxisConstructible.neg {a : ℝ} (ha : AxisConstructible a) :
    AxisConstructible (-a) :=
  ConstructiblePoint.inter_lc ConstructiblePoint.origin ConstructiblePoint.unit
    ConstructiblePoint.origin ConstructiblePoint.origin ha
    (by norm_num [Prod.ext_iff])
    (by simp only [OnLine]; ring)
    (by simp only [OnCircle]; ring)

/-- **Subtraction.** `a - b = a + (-b)`. -/
theorem AxisConstructible.sub {a b : ℝ} (ha : AxisConstructible a) (hb : AxisConstructible b) :
    AxisConstructible (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

/-! ### Erecting the `y`-axis and the unit perpendicular `(0,1)`

To construct products and square roots we must leave the `x`-axis. The classic move:
two circles of radius `2` centred at `(±1, 0)` meet at `(0, ±√3)`; the line through
those is the `y`-axis; it meets the unit circle at `(0, ±1)`. -/

/-- `(-1, 0)` is constructible. -/
theorem cp_neg_one : ConstructiblePoint (-1, 0) :=
  AxisConstructible.neg AxisConstructible.one

/-- `(0, √3)` is constructible: the upper apex of the two radius-`2` circles centred at
`(1,0)` and `(-1,0)`. -/
theorem cp_zero_sqrt3 : ConstructiblePoint (0, Real.sqrt 3) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ConstructiblePoint.inter_cc
    AxisConstructible.one cp_neg_one AxisConstructible.one
    cp_neg_one cp_neg_one AxisConstructible.one
    (by norm_num [Prod.ext_iff])
    (by show ((0:ℝ) - 1) ^ 2 + (Real.sqrt 3 - 0) ^ 2 = ((1:ℝ) - (-1)) ^ 2 + ((0:ℝ) - 0) ^ 2
        linear_combination hs)
    (by show ((0:ℝ) - (-1)) ^ 2 + (Real.sqrt 3 - 0) ^ 2 = ((1:ℝ) - (-1)) ^ 2 + ((0:ℝ) - 0) ^ 2
        linear_combination hs)

/-- `(0, -√3)` is constructible: the lower apex of the same two circles. -/
theorem cp_zero_neg_sqrt3 : ConstructiblePoint (0, -Real.sqrt 3) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ConstructiblePoint.inter_cc
    AxisConstructible.one cp_neg_one AxisConstructible.one
    cp_neg_one cp_neg_one AxisConstructible.one
    (by norm_num [Prod.ext_iff])
    (by show ((0:ℝ) - 1) ^ 2 + (-Real.sqrt 3 - 0) ^ 2 = ((1:ℝ) - (-1)) ^ 2 + ((0:ℝ) - 0) ^ 2
        linear_combination hs)
    (by show ((0:ℝ) - (-1)) ^ 2 + (-Real.sqrt 3 - 0) ^ 2 = ((1:ℝ) - (-1)) ^ 2 + ((0:ℝ) - 0) ^ 2
        linear_combination hs)

/-- **The unit perpendicular `(0, 1)`** — the `y`-axis (through `(0,±√3)`) meets the
unit circle. This is the seed that lets us erect perpendiculars and hence build
products and square roots. -/
theorem cp_zero_one : ConstructiblePoint (0, 1) := by
  refine ConstructiblePoint.inter_lc
    cp_zero_sqrt3 cp_zero_neg_sqrt3
    ConstructiblePoint.origin ConstructiblePoint.origin AxisConstructible.one
    (by
      intro h
      have h2 : Real.sqrt 3 = -Real.sqrt 3 := (Prod.ext_iff.mp h).2
      have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      linarith)
    (by simp only [OnLine]; ring)
    (by simp only [OnCircle]; ring)

/-- **Lift an axis value to the `y`-axis.** From `(a,0)` build `(0,a)` — the `y`-axis
(through `(0,0)` and `(0,1)`) meets the circle centred at the origin through `(a,0)`. -/
theorem cp_zero_of_axis {a : ℝ} (ha : AxisConstructible a) : ConstructiblePoint (0, a) :=
  ConstructiblePoint.inter_lc ConstructiblePoint.origin cp_zero_one
    ConstructiblePoint.origin ConstructiblePoint.origin ha
    (by norm_num [Prod.ext_iff])
    (by simp only [OnLine]; ring)
    (by simp only [OnCircle]; ring)

/-- **Parallelogram translate.** Given constructible `A`, `B`, `P` with `P ≠ B`, the
fourth parallelogram vertex `Q = P + (B − A)` is constructible. It lies on the circle
centred at `P` of radius `|B − A|` and on the circle centred at `B` of radius `|P − A|`,
so `inter_cc` applies — we need only that `Q` satisfies both equations, not that it is
the unique intersection. This is the compass primitive for copying a direction (drawing
a parallel). -/
theorem cp_translate {A B P : ℝ × ℝ}
    (hA : ConstructiblePoint A) (hB : ConstructiblePoint B) (hP : ConstructiblePoint P)
    (hPB : P ≠ B) :
    ConstructiblePoint (P.1 + (B.1 - A.1), P.2 + (B.2 - A.2)) :=
  ConstructiblePoint.inter_cc hP hA hB hB hA hP hPB
    (by simp only [OnCircle]; ring)
    (by simp only [OnCircle]; ring)

/-- **Multiplication by compass** (the intercept theorem). To form `a·b`: lift `a` to
`(0,a)`; the line through `(1,0)` and `(0,a)` has the line through `(b,0)` parallel to
it (translate by `(b−1, a)`) meeting the `y`-axis at `(0, a·b)`; rotate that onto the
`x`-axis. -/
theorem AxisConstructible.mul {a b : ℝ} (ha : AxisConstructible a) (hb : AxisConstructible b) :
    AxisConstructible (a * b) := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simpa using AxisConstructible.zero
  have h0a : ConstructiblePoint (0, a) := cp_zero_of_axis ha
  have hPB : ((b, 0) : ℝ × ℝ) ≠ (0, a) := by
    rw [Ne, Prod.ext_iff, not_and_or]; exact Or.inl hb0
  have hQ : ConstructiblePoint (b + (0 - 1), 0 + (a - 0)) :=
    cp_translate AxisConstructible.one h0a hb hPB
  have hab : ConstructiblePoint (0, a * b) := by
    refine ConstructiblePoint.inter_ll hb hQ
      ConstructiblePoint.origin cp_zero_one
      (by simp only [OnLine]; ring) (by simp only [OnLine]; ring) ?_
    show ((b + (0 - 1)) - b) * ((1 : ℝ) - 0) - ((0 + (a - 0)) - 0) * ((0 : ℝ) - 0) ≠ 0
    norm_num
  exact ConstructiblePoint.inter_lc ConstructiblePoint.origin AxisConstructible.one
    ConstructiblePoint.origin ConstructiblePoint.origin hab
    (by norm_num [Prod.ext_iff])
    (by simp only [OnLine]; ring)
    (by simp only [OnCircle]; ring)

/-- **Inversion by compass** (intercept theorem). For `a ≠ 0`: the line through `(a,0)`
and `(0,1)`, copied parallel through `(1,0)`, meets the `y`-axis at `(0, a⁻¹)`. -/
theorem AxisConstructible.inv {a : ℝ} (ha : AxisConstructible a) : AxisConstructible a⁻¹ := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simpa using AxisConstructible.zero
  have hPB : ((1, 0) : ℝ × ℝ) ≠ (0, 1) := by norm_num [Prod.ext_iff]
  have hQ : ConstructiblePoint (1 + (0 - a), 0 + (1 - 0)) :=
    cp_translate ha cp_zero_one AxisConstructible.one hPB
  have hinv : ConstructiblePoint (0, a⁻¹) := by
    refine ConstructiblePoint.inter_ll AxisConstructible.one hQ
      ConstructiblePoint.origin cp_zero_one
      ?_ (by simp only [OnLine]; ring) ?_
    · show ((1 + (0 - a)) - 1) * (a⁻¹ - 0) = ((0 + (1 - 0)) - 0) * ((0 : ℝ) - 1)
      field_simp; ring
    · show ((1 + (0 - a)) - 1) * ((1 : ℝ) - 0) - ((0 + (1 - 0)) - 0) * ((0 : ℝ) - 0) ≠ 0
      have h : ((1 + (0 - a)) - 1) * ((1 : ℝ) - 0)
          - ((0 + (1 - 0)) - 0) * ((0 : ℝ) - 0) = -a := by ring
      rw [h]; exact neg_ne_zero.mpr ha0
  exact ConstructiblePoint.inter_lc ConstructiblePoint.origin AxisConstructible.one
    ConstructiblePoint.origin ConstructiblePoint.origin hinv
    (by norm_num [Prod.ext_iff])
    (by simp only [OnLine]; ring)
    (by simp only [OnCircle]; ring)

/-- **Division.** `a / b = a · b⁻¹`. -/
theorem AxisConstructible.div {a b : ℝ} (ha : AxisConstructible a) (hb : AxisConstructible b) :
    AxisConstructible (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

/-- Every natural number is axis-constructible. -/
theorem AxisConstructible.natCast : ∀ n : ℕ, AxisConstructible (n : ℝ)
  | 0 => by simpa using AxisConstructible.zero
  | (n + 1) => by rw [Nat.cast_succ]; exact (AxisConstructible.natCast n).add AxisConstructible.one

/-- Every integer is axis-constructible. -/
theorem AxisConstructible.intCast (n : ℤ) : AxisConstructible (n : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using AxisConstructible.natCast m
  · simpa using (AxisConstructible.natCast m).neg

/-- Every rational is axis-constructible (`q = q.num / q.den`). -/
theorem AxisConstructible.ratCast (q : ℚ) : AxisConstructible (q : ℝ) := by
  rw [Rat.cast_def]
  exact (AxisConstructible.intCast q.num).div (AxisConstructible.natCast q.den)

/-- **Square root by compass** (Thales / geometric mean). For `a ≥ 0`: the circle on
the diameter `[(-1,0), (a,0)]`, equivalently centred at `((a−1)/2, 0)` through `(a,0)`,
meets the `y`-axis at `(0, √a)`; rotate onto the `x`-axis. This is the characteristic
compass-and-straightedge power: adjoining a square root. -/
theorem AxisConstructible.sqrt {a : ℝ} (ha : AxisConstructible a) (ha0 : 0 ≤ a) :
    AxisConstructible (Real.sqrt a) := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0
  have h2 : AxisConstructible (2 : ℝ) := by
    have h := AxisConstructible.one.add AxisConstructible.one; norm_num at h; exact h
  have hc : AxisConstructible ((a - 1) / 2) := by
    rw [div_eq_mul_inv]; exact (ha.sub AxisConstructible.one).mul h2.inv
  have hsqrt : ConstructiblePoint (0, Real.sqrt a) := by
    refine ConstructiblePoint.inter_lc ConstructiblePoint.origin cp_zero_one
      hc hc ha
      (by norm_num [Prod.ext_iff])
      (by simp only [OnLine]; ring)
      ?_
    show ((0 : ℝ) - (a - 1) / 2) ^ 2 + (Real.sqrt a - 0) ^ 2
        = (a - (a - 1) / 2) ^ 2 + ((0 : ℝ) - 0) ^ 2
    linear_combination hsa
  exact ConstructiblePoint.inter_lc ConstructiblePoint.origin AxisConstructible.one
    ConstructiblePoint.origin ConstructiblePoint.origin hsqrt
    (by norm_num [Prod.ext_iff])
    (by simp only [OnLine]; ring)
    (by simp only [OnCircle]; ring)

/-! ### The full equivalence via a square-root-tower induction

The axis-constructible reals form a subfield of `ℝ` closed under square roots; every
square-root tower over `ℚ` therefore lands inside it, giving the converse of the
faithfulness bridge. -/

/-- The axis-constructible reals as a subfield of `ℝ`. -/
noncomputable def axisSubfield : Subfield ℝ where
  carrier := {x | AxisConstructible x}
  mul_mem' := AxisConstructible.mul
  one_mem' := AxisConstructible.one
  add_mem' := AxisConstructible.add
  zero_mem' := AxisConstructible.zero
  neg_mem' := AxisConstructible.neg
  inv_mem' := fun _ hx => AxisConstructible.inv hx

/-- The axis-constructible reals as an intermediate field `ℚ ≤ · ≤ ℝ`. -/
noncomputable def axisField : IntermediateField ℚ ℝ :=
  axisSubfield.toIntermediateField (fun q => by simpa using AxisConstructible.ratCast q)

@[simp] theorem mem_axisField {x : ℝ} : x ∈ axisField ↔ AxisConstructible x := Iff.rfl

/-- **The compass step, algebraically.** If `a² = a·a` is axis-constructible then so is
`a` (it is `±√(a²)`). This is what makes `axisField` closed under the tower's
square-root adjunctions. -/
theorem axisField_mem_of_sq_mem {a : ℝ} (ha : AxisConstructible (a * a)) : a ∈ axisField := by
  rw [mem_axisField]
  have hs : AxisConstructible (Real.sqrt (a * a)) := ha.sqrt (mul_self_nonneg a)
  rw [show a * a = a ^ 2 by ring, Real.sqrt_sq_eq_abs] at hs
  rcases abs_choice a with hab | hab
  · rwa [hab] at hs
  · rw [hab] at hs; have h := hs.neg; rwa [neg_neg] at h

/-- Every square-root tower over `ℚ` lies inside the axis-constructible field. -/
theorem isSqrtTower_le_axisField {K : IntermediateField ℚ ℝ} (hK : IsSqrtTower K) :
    K ≤ axisField := by
  induction hK with
  | base => exact bot_le
  | @step K hK a ha ih =>
    have haA : a ∈ axisField := axisField_mem_of_sq_mem (mem_axisField.mp (ih ha))
    have e : (K⟮a⟯).restrictScalars ℚ = adjoin ℚ (↑K ∪ {a}) :=
      IntermediateField.restrictScalars_adjoin ℚ K {a}
    rw [e, IntermediateField.adjoin_le_iff]
    exact Set.union_subset (SetLike.coe_subset_coe.mpr ih) (Set.singleton_subset_iff.mpr haA)

/-- **Converse faithfulness.** Every algebraically-constructible real number is realised
on the constructed `x`-axis. -/
theorem isConstructible_imp_axis {x : ℝ} (hx : IsConstructible x) : AxisConstructible x := by
  obtain ⟨K, hK, hmem⟩ := hx
  exact mem_axisField.mp (isSqrtTower_le_axisField hK hmem)

/-- **Wantzel's theorem, both directions.** A real number is algebraically constructible
(lies in a tower of quadratic extensions of `ℚ`) **iff** the point `(x, 0)` can be
constructed by compass and straightedge from `(0,0)` and `(1,0)`. This is the full
equivalence between the algebra of `SqrtTower.lean` and the geometry of
`ConstructiblePoint.lean`. -/
theorem isConstructible_iff_constructiblePoint {x : ℝ} :
    IsConstructible x ↔ ConstructiblePoint (x, 0) :=
  ⟨isConstructible_imp_axis, fun h => (ConstructiblePoint.isConstructible_coords h).1⟩

end LeanFormalizations.Constructible

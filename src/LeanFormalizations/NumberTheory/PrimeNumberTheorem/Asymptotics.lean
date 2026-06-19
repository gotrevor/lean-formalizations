/-
# Prime Number Theorem port — Asymptotics / Log prerequisites

Faithful verbatim port of two `PrimeNumberTheoremAnd` mathlib patches (Apache-2.0), required by the
Wiener tower that discharges `weakPNT` (the flagship no-three-in-line headline
`Combinatorics/NoThreeInLine/PrimeGap.maxNoThreeInLine_ge_three_halves_sub` rests on the cited
`axiom weakPNT : Chebyshev.psi ~[atTop] (·)`, i.e. the Prime Number Theorem):

* `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean`
* `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`

Names and namespaces are kept **exactly** as upstream (`Asymptotics.*`, `Filter.Eventually.natCast`,
`IsBigO.natCast`, `Real.tendsto_pow_log_div_pow_atTop`) so the downstream `Wiener` port resolves them
without edits. All dependencies exist in our pin `v4.29.1`; the patch layer ports with zero API drift.
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics

open Real in
/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

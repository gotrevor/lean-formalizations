/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.McDiarmid.Hoeffding

/-!
# McDiarmid: the exponential-moment bound (phase E4b helper)

`f_s x := avg_z f (s.piecewise z x)` averages `f` over the coordinates in `s`, using the whole
product as the averaging space so no sub-products appear.  Adding one coordinate costs a factor
`exp(λ² c_i² / 8)` by Hoeffding's lemma; the only combinatorial input is that swapping
coordinate `i` between two points is an involution of `(∀ i, α i) × (∀ i, α i)` (`sum_update_swap`).
-/

namespace LeanFormalizations.Erdos385.McDiarmid

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)]

/-- Swapping coordinate `i` between `x` and `z` is an involution, so averaging `F` over the
`i`-th coordinate first changes nothing. -/
theorem sum_update_swap (i : ι) (F : (∀ i, α i) → ℝ) :
    ∑ x : ∀ i, α i, ∑ z : ∀ i, α i, F (Function.update x i (z i)) = Fintype.card (∀ i, α i) * ∑ x, F x := by
  let e : (∀ i, α i) × (∀ i, α i) → (∀ i, α i) × (∀ i, α i) := fun p =>
    (Function.update p.1 i (p.2 i), Function.update p.2 i (p.1 i))
  have he : Function.Involutive e := by
    rintro ⟨x, z⟩
    simp only [e, Function.update_self, Function.update_idem, Function.update_eq_self]
  rw [show ∑ x : ∀ i, α i, ∑ z : ∀ i, α i, F (Function.update x i (z i)) =
      ∑ p : (∀ i, α i) × (∀ i, α i), F (Function.update p.1 i (p.2 i)) by
    rw [Fintype.sum_prod_type]]
  have := Fintype.sum_equiv he.toPerm (fun p : (∀ i, α i) × (∀ i, α i) => F (Function.update p.1 i (p.2 i)))
    (fun p => F p.1) (fun p => rfl)
  rw [this, Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

/-- Average of `f` over the coordinates in `s`. -/
noncomputable def avgS (f : (∀ i, α i) → ℝ) (s : Finset ι) (x : (∀ i, α i)) : ℝ :=
  (∑ z : ∀ i, α i, f (s.piecewise z x)) / Fintype.card (∀ i, α i)

variable [∀ i, Nonempty (α i)]

theorem card_pos' : (0 : ℝ) < Fintype.card (∀ i, α i) := by exact_mod_cast Fintype.card_pos

theorem avgS_empty (f : (∀ i, α i) → ℝ) (x : (∀ i, α i)) : avgS f ∅ x = f x := by
  have := (card_pos' (α := α)).ne'
  simp [avgS, Finset.sum_const, Finset.card_univ]
  field_simp

theorem avgS_univ (f : (∀ i, α i) → ℝ) (x : (∀ i, α i)) :
    avgS f Finset.univ x = (∑ z, f z) / Fintype.card (∀ i, α i) := by
  simp [avgS]

theorem avgS_insert_update (f : (∀ i, α i) → ℝ) (s : Finset ι) (i : ι) (x : (∀ i, α i)) (a : α i) :
    avgS f (insert i s) (Function.update x i a) = avgS f (insert i s) x := by
  unfold avgS
  congr 2 with z
  congr 1
  funext j
  by_cases hj : j ∈ insert i s
  · simp [Finset.piecewise_eq_of_mem _ _ _ hj]
  · have : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
    simp [Finset.piecewise_eq_of_notMem _ _ _ hj, Function.update_of_ne this]

theorem avgS_insert (f : (∀ i, α i) → ℝ) (s : Finset ι) (i : ι) (hi : i ∉ s) (x : (∀ i, α i)) :
    avgS f (insert i s) x =
      (∑ z : ∀ i, α i, avgS f s (Function.update x i (z i))) / Fintype.card (∀ i, α i) := by
  have hN := (card_pos' (α := α)).ne'
  have key : ∀ z w : ∀ i, α i, s.piecewise w (Function.update x i (z i)) =
      (insert i s).piecewise (Function.update w i (z i)) x := by
    intro z w
    funext j
    by_cases hjs : j ∈ s
    · have : j ≠ i := fun h => hi (h ▸ hjs)
      simp [Finset.piecewise_eq_of_mem _ _ _ hjs, Function.update_of_ne this,
        Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_of_mem hjs)]
    · by_cases hji : j = i
      · subst hji
        simp [Finset.piecewise_eq_of_notMem _ _ _ hjs]
      · have : j ∉ insert i s := by simp [hji, hjs]
        simp [Finset.piecewise_eq_of_notMem _ _ _ hjs, Finset.piecewise_eq_of_notMem _ _ _ this,
          Function.update_of_ne hji]
  unfold avgS
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_comm,
    sum_update_swap i (fun w => f ((insert i s).piecewise w x))]
  field_simp

theorem avgS_osc (f : (∀ i, α i) → ℝ) (c : ι → ℝ)
    (hf : ∀ x y : (∀ i, α i), ∀ i, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (s : Finset ι) (i : ι) (hi : i ∉ s) (x : (∀ i, α i)) (a b : α i) :
    |avgS f s (Function.update x i a) - avgS f s (Function.update x i b)| ≤ c i := by
  have hN := card_pos' (α := α)
  unfold avgS
  rw [← sub_div, abs_div, abs_of_pos hN, div_le_iff₀ hN, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ z : ∀ i, α i, |f (s.piecewise z (Function.update x i a)) -
        f (s.piecewise z (Function.update x i b))| ≤ ∑ _z : ∀ i, α i, c i := by
        refine Finset.sum_le_sum fun z _ => hf _ _ i fun j hj => ?_
        by_cases hjs : j ∈ s
        · simp [Finset.piecewise_eq_of_mem _ _ _ hjs]
        · simp [Finset.piecewise_eq_of_notMem _ _ _ hjs, Function.update_of_ne hj]
    _ = c i * Fintype.card (∀ i, α i) := by simp [Finset.card_univ, mul_comm]

theorem step (f : (∀ i, α i) → ℝ) (c : ι → ℝ)
    (hf : ∀ x y : (∀ i, α i), ∀ i, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (m l : ℝ) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    ∑ x : ∀ i, α i, Real.exp (l * (avgS f s x - m)) ≤
      Real.exp (l ^ 2 * c i ^ 2 / 8) * ∑ x : ∀ i, α i, Real.exp (l * (avgS f (insert i s) x - m)) := by
  have hN := card_pos' (α := α)
  have h1 := sum_update_swap i (fun x => Real.exp (l * (avgS f s x - m)))
  refine le_of_mul_le_mul_left ?_ hN
  rw [← h1]
  refine (Finset.sum_le_sum (g := fun x => Fintype.card (∀ i, α i) *
    Real.exp (l ^ 2 * c i ^ 2 / 8) * Real.exp (l * (avgS f (insert i s) x - m)))
    fun x _ => ?_).trans (le_of_eq ?_)
  swap
  · rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  set g : (∀ i, α i) → ℝ := fun z => avgS f s (Function.update x i (z i)) - avgS f (insert i s) x
  have hsplit : ∀ z : ∀ i, α i, Real.exp (l * (avgS f s (Function.update x i (z i)) - m)) =
      Real.exp (l * (avgS f (insert i s) x - m)) * Real.exp (l * g z) := by
    intro z; rw [← Real.exp_add]; congr 1; simp only [g]; ring
  simp_rw [hsplit]
  rw [← Finset.mul_sum]
  have hmean : ∑ z, g z = 0 := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [avgS_insert f s i hi x]
    field_simp
    ring
  have hosc : ∀ z w, |g z - g w| ≤ c i := by
    intro z w; simp only [g, sub_sub_sub_cancel_right]; exact avgS_osc f c hf s i hi x _ _
  have hH := hoeffding_finite g (c i) l hmean hosc
  calc Real.exp (l * (avgS f (insert i s) x - m)) * ∑ z, Real.exp (l * g z)
      ≤ Real.exp (l * (avgS f (insert i s) x - m)) *
          (Fintype.card (∀ i, α i) * Real.exp (l ^ 2 * c i ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
    _ = _ := by ring

/-- **The exponential-moment bound** behind McDiarmid. -/
theorem sum_exp_le (f : (∀ i, α i) → ℝ) (c : ι → ℝ)
    (hf : ∀ x y : (∀ i, α i), ∀ i, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) (l : ℝ) :
    ∑ x : ∀ i, α i, Real.exp (l * (f x - (∑ z, f z) / Fintype.card (∀ i, α i))) ≤
      Fintype.card (∀ i, α i) * Real.exp (l ^ 2 * (∑ i, c i ^ 2) / 8) := by
  set m := (∑ z, f z) / Fintype.card (∀ i, α i)
  have H : ∀ s : Finset ι, ∑ x : ∀ i, α i, Real.exp (l * (f x - m)) ≤
      Real.exp (l ^ 2 * (∑ i ∈ s, c i ^ 2) / 8) * ∑ x : ∀ i, α i, Real.exp (l * (avgS f s x - m)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [avgS_empty]
    | insert i s hi ih =>
      refine ih.trans ?_
      rw [Finset.sum_insert hi]
      calc _ ≤ Real.exp (l ^ 2 * (∑ i ∈ s, c i ^ 2) / 8) * (Real.exp (l ^ 2 * c i ^ 2 / 8) *
            ∑ x : ∀ i, α i, Real.exp (l * (avgS f (insert i s) x - m))) :=
            mul_le_mul_of_nonneg_left (step f c hf m l s i hi) (Real.exp_pos _).le
        _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  refine (H Finset.univ).trans (le_of_eq ?_)
  simp [avgS_univ, m, Finset.card_univ, mul_comm]

end LeanFormalizations.Erdos385.McDiarmid

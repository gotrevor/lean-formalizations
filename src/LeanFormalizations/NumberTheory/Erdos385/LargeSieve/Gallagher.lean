/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.LargeSieve.Montgomery

/-!
# Gallagher's analytic large sieve (phase E4c)

`analytic_large_sieve`: for `δ`-separated points of `[0, 1]` and `T(x) = Σ_{k ≤ N} c_k e(kx)`,
`Σ_x |T(x)|² ≤ (3/δ + 12π(N + 1)) Σ |c_k|²`.

Gallagher's pointwise inequality `δ f(x) ≤ ∫_{arc} f + δ ∫_{arc} |f'|` for `f = |T|²`, summed over
the disjoint arcs (all inside `[-1, 2]`), Parseval on `[-1, 2]`, and `2|T||T'| ≤ λ|T|² + λ⁻¹|T'|²`
with `λ = 2π(N + 1)` in place of Cauchy–Schwarz.
-/

namespace LeanFormalizations.Erdos385.LargeSieve
open Complex Finset MeasureTheory

lemma hasDerivAt_ee_mul (m x : ℝ) :
    HasDerivAt (fun t : ℝ => ee (m * t)) (2 * Real.pi * I * m * ee (m * x)) x := by
  unfold ee
  have h : HasDerivAt (fun t : ℝ => (2 * Real.pi * I * ((m * t : ℝ) : ℂ))) (2 * Real.pi * I * m) x := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul (2 * Real.pi * I * m)).comp_ofReal
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have := h.cexp
  convert this using 1; ring

lemma continuous_ee : Continuous ee := by unfold ee; fun_prop

lemma integral_ee_int (m : ℤ) :
    ∫ x in (-1:ℝ)..2, ee (m * x) = if m = 0 then 3 else 0 := by
  split_ifs with hm
  · subst hm; simp [ee]; norm_num
  · have hm' : (2 * Real.pi * I * (m:ℝ) : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero, hm]
    have hd : ∀ x ∈ Set.uIcc (-1:ℝ) 2, HasDerivAt (fun t : ℝ => ee (m * t) / (2 * Real.pi * I * (m:ℝ)))
        (ee (m * x)) x := by
      intro x _
      have := (hasDerivAt_ee_mul m x).div_const (2 * Real.pi * I * (m:ℝ))
      exact this.congr_deriv (mul_div_cancel_left₀ _ hm')
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_ee.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
    have h1 : ee ((m:ℝ) * 2) = 1 := by
      rw [show (m:ℝ) * 2 = ((2 * m : ℤ) : ℝ) by push_cast; ring]; exact ee_int _
    have h2 : ee ((m:ℝ) * (-1)) = 1 := by
      rw [show (m:ℝ) * (-1) = ((-m : ℤ) : ℝ) by push_cast; ring]; exact ee_int _
    show ee ((m:ℝ) * 2) / _ - ee ((m:ℝ) * (-1)) / _ = 0
    rw [h1, h2, sub_self]

lemma continuous_expSum (S : Finset ℕ) (b : ℕ → ℂ) : Continuous (expSum S b) := by
  unfold expSum
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id))

/-- Parseval on `[-1, 2]`. -/
lemma integral_norm_expSum_sq (S : Finset ℕ) (b : ℕ → ℂ) :
    ∫ x in (-1:ℝ)..2, ‖expSum S b x‖ ^ 2 = 3 * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [normSq_eq_mul_conj]
  have e : ∀ x : ℝ, expSum S b x * (starRingEnd ℂ) (expSum S b x)
      = ∑ n ∈ S, ∑ m ∈ S, b n * (starRingEnd ℂ) (b m) * ee (((n:ℤ) - m : ℤ) * x) := by
    intro x
    simp_rw [expSum, map_sum, Finset.sum_mul, Finset.mul_sum, map_mul, conj_ee]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [show (((n:ℤ) - m : ℤ) : ℝ) * x = n * x + -(m * x) by push_cast; ring, ee_add]; ring
  simp_rw [e]
  have hint : ∀ n m : ℕ, IntervalIntegrable
      (fun x : ℝ => b n * (starRingEnd ℂ) (b m) * ee (((n:ℤ) - m : ℤ) * x)) volume (-1) 2 := by
    intro n m
    exact (continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun n _ => by
    exact (continuous_finsetSum _ fun m _ =>
      (continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun m _ => hint _ m), intervalIntegral.integral_const_mul,
    integral_ee_int]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_eq_single n]
  · simp only [sub_self, if_true]; rw [← normSq_eq_mul_conj]; push_cast; ring
  · intro m _ hmn
    rw [if_neg (by omega)]; ring
  · intro h; exact absurd hn h

/-- One-variable step: `f x ≤ f t + ∫_a^b |f'|` for `t, x ∈ [a, b]`. -/
lemma le_add_integral_abs_deriv {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') {a b x t : ℝ} (hxa : a ≤ x) (hxb : x ≤ b) (hta : a ≤ t) (htb : t ≤ b) :
    f x ≤ f t + ∫ u in a..b, |f' u| := by
  have hint : ∀ c d, IntervalIntegrable f' volume c d := fun c d => hf'.intervalIntegrable c d
  have habs : ∀ c d, IntervalIntegrable (fun u => |f' u|) volume c d :=
    fun c d => hf'.abs.intervalIntegrable c d
  rcases le_total t x with h | h
  · have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hf u) (hint t x)
    have h1 : ∫ u in t..x, f' u ≤ ∫ u in t..x, |f' u| :=
      intervalIntegral.integral_mono_on h (hint t x) (habs t x) fun u _ => le_abs_self _
    have h2 : ∫ u in t..x, |f' u| ≤ ∫ u in a..b, |f' u| :=
      intervalIntegral.integral_mono_interval hta h hxb (Filter.Eventually.of_forall fun u => abs_nonneg _) (habs a b)
    linarith
  · have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hf u) (hint x t)
    have h1 : -∫ u in x..t, f' u ≤ ∫ u in x..t, |f' u| := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_mono_on h (hint x t).neg (habs x t) fun u _ => neg_le_abs _
    have h2 : ∫ u in x..t, |f' u| ≤ ∫ u in a..b, |f' u| :=
      intervalIntegral.integral_mono_interval hxa h htb (Filter.Eventually.of_forall fun u => abs_nonneg _) (habs a b)
    linarith

/-- **Gallagher's inequality**: `(b − a) f x ≤ ∫_a^b f + (b − a) ∫_a^b |f'|`. -/
lemma gallagher {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    {a b x : ℝ} (hxa : a ≤ x) (hxb : x ≤ b) :
    (b - a) * f x ≤ (∫ u in a..b, f u) + (b - a) * ∫ u in a..b, |f' u| := by
  have hab : a ≤ b := hxa.trans hxb
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have := intervalIntegral.integral_mono_on hab (g := fun t => f t + ∫ u in a..b, |f' u|)
    (continuous_const.intervalIntegrable (μ := volume) a b)
    ((hfc.add continuous_const).intervalIntegrable a b)
    fun t ht => le_add_integral_abs_deriv hf hf' hxa hxb ht.1 ht.2
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hfc.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const] at this
  simpa [smul_eq_mul] using this

/-- Integrals over `δ`-separated arcs of points of `[0, 1]` sum to at most the integral over
`[-1, 2]`. -/
lemma sum_arc_integral_le {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (pts : Finset ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hpts : ∀ x ∈ pts, 0 ≤ x ∧ x ≤ 1)
    (hsep : ∀ x ∈ pts, ∀ y ∈ pts, x ≠ y → δ ≤ |x - y|) :
    ∑ x ∈ pts, ∫ u in (x - δ / 2)..(x + δ / 2), g u ≤ ∫ u in (-1:ℝ)..2, g u := by
  have hle : ∀ x : ℝ, x - δ / 2 ≤ x + δ / 2 := fun x => by linarith
  simp_rw [intervalIntegral.integral_of_le (hle _), intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 2)]
  rw [← integral_biUnion_finset pts (fun _ _ => measurableSet_Ioc)]
  · apply setIntegral_mono_set
    · exact hg.integrableOn_Ioc
    · exact Filter.Eventually.of_forall fun u => hg0 u
    · refine (Set.iUnion₂_subset fun x hx => ?_).eventuallyLE
      have := hpts x hx
      exact Set.Ioc_subset_Ioc (by linarith) (by linarith)
  · intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro u hu hv
    have := hsep x hx y hy hxy
    simp only [Set.mem_Ioc] at hu hv
    rcases le_total x y with h | h
    · rw [abs_of_nonpos (by linarith)] at this; linarith
    · rw [abs_of_nonneg (by linarith)] at this; linarith
  · intro x _; exact hg.integrableOn_Ioc

lemma hasDerivAt_expSum (S : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) :
    HasDerivAt (expSum S b) (expSum S (fun n => b n * (2 * Real.pi * I * n)) x) x := by
  unfold expSum
  have := HasDerivAt.fun_sum (fun n (_ : n ∈ S) => (hasDerivAt_ee_mul n x).const_mul (b n))
  refine this.congr_deriv ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast; ring

lemma two_mul_le_add (a b l : ℝ) (hl : 0 < l) : 2 * a * b ≤ l * a ^ 2 + l⁻¹ * b ^ 2 := by
  have h : 0 ≤ (l * a - b) ^ 2 / l := by positivity
  have e : (l * a - b) ^ 2 / l = l * a ^ 2 + l⁻¹ * b ^ 2 - 2 * a * b := by
    field_simp; ring
  linarith

/-- **The analytic large sieve** (Gallagher's form, constant `3/δ + 12π(N+1)`). -/
theorem analytic_large_sieve (N : ℕ) (c : ℕ → ℂ) (pts : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hpts : ∀ x ∈ pts, 0 ≤ x ∧ x ≤ 1)
    (hsep : ∀ x ∈ pts, ∀ y ∈ pts, x ≠ y → δ ≤ |x - y|) :
    ∑ x ∈ pts, ‖expSum (range (N + 1)) c x‖ ^ 2
      ≤ (3 / δ + 12 * Real.pi * (N + 1)) * ∑ k ∈ range (N + 1), ‖c k‖ ^ 2 := by
  set S := range (N + 1)
  set T := expSum S c
  set c' : ℕ → ℂ := fun n => c n * (2 * Real.pi * I * n)
  set T' := expSum S c'
  set f : ℝ → ℝ := fun t => ‖T t‖ ^ 2
  set f' : ℝ → ℝ := fun t => 2 * inner ℝ (T t) (T' t)
  have hf : ∀ t, HasDerivAt f (f' t) t := fun t => (hasDerivAt_expSum S c t).norm_sq
  have hTc : Continuous T := continuous_expSum S c
  have hT'c : Continuous T' := continuous_expSum S c'
  have hf'c : Continuous f' := continuous_const.mul (hTc.inner hT'c)
  have hfc : Continuous f := hTc.norm.pow 2
  set A := ∑ k ∈ S, ‖c k‖ ^ 2
  set l : ℝ := 2 * Real.pi * (N + 1)
  have hl : 0 < l := by positivity
  -- pointwise Gallagher
  have hpt : ∀ x ∈ pts, f x ≤ δ⁻¹ * (∫ u in (x - δ / 2)..(x + δ / 2), f u)
      + ∫ u in (x - δ / 2)..(x + δ / 2), |f' u| := by
    intro x _
    have := gallagher hf hf'c (a := x - δ / 2) (b := x + δ / 2) (x := x) (by linarith) (by linarith)
    rw [show x + δ / 2 - (x - δ / 2) = δ by ring] at this
    rw [← mul_le_mul_iff_of_pos_left hδ, mul_add, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
    exact this
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have h1 := sum_arc_integral_le hfc (fun t => by positivity) pts hδ hδ1 hpts hsep
  have h2 := sum_arc_integral_le hf'c.abs (fun t => abs_nonneg _) pts hδ hδ1 hpts hsep
  have hP : ∫ u in (-1:ℝ)..2, f u = 3 * A := integral_norm_expSum_sq S c
  have hP' : ∫ u in (-1:ℝ)..2, ‖T' u‖ ^ 2 ≤ 3 * (l ^ 2 * A) := by
    rw [integral_norm_expSum_sq S c']
    gcongr 3 * ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : (k:ℝ) ≤ N + 1 := by
      have := Finset.mem_range.1 hk; exact_mod_cast this.le
    have hn : ‖c' k‖ = ‖c k‖ * (2 * Real.pi * k) := by
      simp [c', abs_of_pos Real.pi_pos]
    have hkl : 2 * Real.pi * k ≤ l := by simp only [l]; gcongr
    rw [hn, mul_pow, mul_comm]
    gcongr
  have hD : ∫ u in (-1:ℝ)..2, |f' u| ≤ ∫ u in (-1:ℝ)..2, (l * f u + l⁻¹ * ‖T' u‖ ^ 2) := by
    have hgc : Continuous (fun u => l * f u + l⁻¹ * ‖T' u‖ ^ 2) :=
      (continuous_const.mul hfc).add (continuous_const.mul (hT'c.norm.pow 2))
    apply intervalIntegral.integral_mono_on (by norm_num) (hf'c.abs.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)
    intro u _
    calc |f' u| ≤ 2 * ‖T u‖ * ‖T' u‖ := by
          simp only [f', abs_mul, abs_two, mul_assoc]
          gcongr; exact abs_real_inner_le_norm _ _
      _ ≤ _ := two_mul_le_add _ _ l hl
  rw [intervalIntegral.integral_add (f := fun u => l * f u) (g := fun u => l⁻¹ * ‖T' u‖ ^ 2) ((continuous_const.mul hfc).intervalIntegrable _ _)
    ((continuous_const.mul (hT'c.norm.pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hP] at hD
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
  have hA : 0 ≤ A := by positivity
  have hli : l⁻¹ * (3 * (l ^ 2 * A)) = 3 * l * A := by field_simp
  have := mul_le_mul_of_nonneg_left hP' (inv_nonneg.2 hl.le)
  calc ∑ x ∈ pts, ‖T x‖ ^ 2 = ∑ x ∈ pts, f x := rfl
    _ ≤ δ⁻¹ * (3 * A) + (l * (3 * A) + 3 * l * A) := by
        refine hsum.trans ?_
        gcongr
        · exact h1.trans hP.le
        · linarith
    _ = (3 / δ + 12 * Real.pi * (N + 1)) * A := by simp only [l]; ring

end LeanFormalizations.Erdos385.LargeSieve

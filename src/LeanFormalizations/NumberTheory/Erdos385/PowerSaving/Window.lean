/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll

/-!
# Erdős #385 power saving: the per-window count against an arbitrary majorant (phase E9b)

`card_badWindow_le_of_split` generalises `card_badWindow_le` (W2): on a bad window the difference
`D(x) = S(x, h₁)/h₁ − S(x, H)/H` satisfies `|D(x)| ≥ μ` (because `S(x, h₁) = 0` there and the long
average is `≥ μ`), so *any* nonnegative `G` with `|D| ≥ μ ⇒ G ≥ ν` controls the count:
`#badWindow · ν ≤ ∫_X^{2X} G`.  For the near/far split take `G = |D_far|²`, `ν = μ²/4`, once
`|D_near| ≤ μ/2` pointwise.  `H` (the long length) is free, so `T₀ = Z^{c₀}` is allowed.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory

theorem card_badWindow_le_of_split {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∀ᶠ Z : ℝ in atTop, ∀ (H μ ν : ℝ) (G : ℝ → ℝ), 0 < μ → (∀ x, 0 ≤ G x) →
      IntegrableOn G (Set.Ioc (paramX δ Z) (2 * paramX δ Z)) →
      (∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z → μ ≤ shortSum (coeffA δ g Z) x H / H) →
      (∀ x, paramX δ Z < x → x ≤ 2 * paramX δ Z →
        μ ≤ |shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
          shortSum (coeffA δ g Z) x H / H| → ν ≤ G x) →
      ((badWindow δ Z).ncard : ℝ) * ν ≤ ∫ x in (paramX δ Z)..(2 * paramX δ Z), G x := by
  have hsq : Tendsto (fun Z : ℝ => δ / 4 * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
  filter_upwards [eventually_gt_atTop 1, hsq.eventually_ge_atTop 2] with Z hZ hh H μ ν G hμ hG0
    hint hlong hGD
  set h := paramH δ Z with hhdef
  have hh' : 2 ≤ h := hh
  set X := paramX δ Z with hX
  have hX0 : 0 < X := by rw [hX, paramX]; nlinarith
  have hH1 : paramH1 δ Z ≤ h / 2 - 1 := by
    unfold paramH1; have := Nat.floor_le (show 0 ≤ paramH δ Z / 2 by linarith); linarith
  have hH1' : 0 ≤ paramH1 δ Z := by
    unfold paramH1
    have : (1 : ℝ) ≤ ⌊paramH δ Z / 2⌋₊ := by
      have : 1 ≤ ⌊paramH δ Z / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    linarith
  classical
  set N := ⌊(1 + δ / 2) * Z⌋₊ + 1
  set T := (Finset.range N).filter (· ∈ badWindow δ Z)
  have hBT : badWindow δ Z = ↑T := by
    ext n; simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · intro hn; refine ⟨?_, hn⟩
      have := Nat.le_floor hn.2.1; omega
    · exact fun h => h.2
  rw [hBT, Set.ncard_coe_finset]
  set J : ℕ → Set ℝ := fun n => Set.Ico ((n : ℝ) - h) ((n : ℝ) - h + 1)
  have hJ : ∀ n ∈ T, ∀ x ∈ J n, ν ≤ G x ∧ X < x ∧ x ≤ 2 * X := by
    intro n hn x hx
    obtain ⟨hn1, hn2, hn3⟩ := (Finset.mem_filter.1 hn).2
    obtain ⟨hx1, hx2⟩ := hx
    have hxZ : Z ≤ x := by linarith
    have hxZ' : x ≤ (1 + δ / 2) * Z := by linarith
    have hXx : X < x := by
      have : X < Z := by rw [hX, paramX]; nlinarith
      linarith
    have hx2X : x ≤ 2 * X := by
      have : (1 + δ / 2) * Z ≤ 2 * X := by rw [hX, paramX]; nlinarith
      linarith
    refine ⟨?_, hXx, hx2X⟩
    have hS1 : shortSum (coeffA δ g Z) x (paramH1 δ Z) = 0 := by
      unfold shortSum
      refine Finset.sum_eq_zero fun m hm => ?_
      by_contra ha
      rw [Finset.mem_Icc] at hm
      have hm1 : x ≤ m := (Nat.ceil_le).1 hm.1
      have hm2 : (m : ℝ) ≤ x + paramH1 δ Z :=
        (Nat.le_floor_iff (by linarith)).1 hm.2
      have hmn : m < n := by
        have : (m : ℝ) < n := by linarith
        exact_mod_cast this
      have := witness_margin hδ hδ' hZ hg hn1 hn2 (by linarith) hmn ha
      linarith
    apply hGD x hXx hx2X
    rw [hS1, zero_div, zero_sub, abs_neg]
    exact (hlong x hxZ hxZ').trans (le_abs_self _)
  have hdisj : Set.Pairwise (↑T) (Function.onFun Disjoint J) := by
    intro n _ m _ hnm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hnm with h | h
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith
    · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith
  have hsub : (⋃ n ∈ T, J n) ⊆ Set.Ioc X (2 * X) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨(hJ n hn x hx).2.1, (hJ n hn x hx).2.2⟩
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc (T.card : ℝ) * ν = ∑ n ∈ T, ν * volume.real (J n) := by
        rw [Finset.sum_congr rfl fun n _ => by
          rw [show volume.real (J n) = 1 by
            simp only [J, Real.volume_real_Ico]; rw [max_eq_left (by linarith)]; ring, mul_one]]
        simp [mul_comm]
    _ ≤ ∑ n ∈ T, ∫ x in J n, G x := Finset.sum_le_sum fun n hn =>
        setIntegral_ge_of_const_le_real measurableSet_Ico measure_Ico_lt_top.ne
          (fun x hx => (hJ n hn x hx).1) (hint.mono_set fun x hx => hsub (by
            simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩))
    _ = ∫ x in ⋃ n ∈ T, J n, G x := (integral_biUnion_finset T (fun _ _ => measurableSet_Ico)
        hdisj fun n hn => hint.mono_set fun x hx => hsub (by
          simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩)).symm
    _ ≤ ∫ x in Set.Ioc X (2 * X), G x :=
        setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => hG0 x)
          (Filter.Eventually.of_forall hsub)

end LeanFormalizations.Erdos385

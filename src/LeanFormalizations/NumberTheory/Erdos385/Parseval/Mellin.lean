/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The L² carrier `Φ(u) = e^{-u} H(e^u)` and its Fourier transform

For `a` supported on `1 ≤ m ≤ N`: `Φ = Σ a_m e^{-u} 1_{u ≥ log m}`, with (mathlib normalization)
`𝓕 Φ ξ = A(s)/s`, `s = 1 + 2πiξ`, `A = LSeries a`.  Also `v Φ(log v) = Σ_{m ≤ v} a_m`.
-/

open MeasureTheory Filter Complex Set
open scoped Topology FourierTransform

noncomputable section

namespace Erdos385.Parseval

/-- `e^{-u} 1_{u ≥ log m}`. -/
def phiTerm (m : ℕ) (u : ℝ) : ℂ :=
  (Ici (Real.log m)).indicator (fun u ↦ ((Real.exp (-u) : ℝ) : ℂ)) u

/-- `Φ(u) = Σ_{m ≤ N} a_m e^{-u} 1_{u ≥ log m}`. -/
def Phi (a : ℕ → ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), a m * phiTerm m u

/-- `s(ξ) = 1 + 2πiξ`. -/
def sArg (ξ : ℝ) : ℂ := 1 + 2 * Real.pi * ξ * I

lemma sArg_re (ξ : ℝ) : (sArg ξ).re = 1 := by simp [sArg]

lemma sArg_ne_zero (ξ : ℝ) : sArg ξ ≠ 0 := fun h ↦ by
  have := sArg_re ξ; rw [h] at this; simp at this

lemma LSeries_eq_sum {a : ℕ → ℂ} {N : ℕ} (ha : ∀ m, (m = 0 ∨ N < m) → a m = 0) (s : ℂ) :
    LSeries a s = ∑ m ∈ Finset.range (N + 1), a m * (m : ℂ) ^ (-s) := by
  have h0 : a 0 = 0 := ha 0 (Or.inl rfl)
  rw [LSeries, tsum_eq_sum (s := Finset.range (N + 1))]
  · exact Finset.sum_congr rfl fun m _ ↦ LSeries.term_def₀ h0 s m
  · intro m hm
    rw [LSeries.term_def₀ h0, ha m (Or.inr (by simpa using hm)), zero_mul]

lemma integrable_phiTerm (m : ℕ) : Integrable (phiTerm m) := by
  unfold phiTerm
  rw [integrable_indicator_iff measurableSet_Ici]
  have := (integrableOn_exp_mul_complex_Ioi (a := -1) (by simp) (Real.log m))
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine this.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  simp [Complex.ofReal_exp]

lemma fourier_phiTerm {m : ℕ} (hm : 1 ≤ m) (ξ : ℝ) :
    𝓕 (phiTerm m) ξ = (m : ℂ) ^ (-sArg ξ) / sArg ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpt : ∀ u, cexp (↑(-2 * Real.pi * u * ξ) * I) • phiTerm m u =
      (Ici (Real.log m)).indicator (fun u : ℝ ↦ cexp (-sArg ξ * u)) u := by
    intro u
    unfold phiTerm
    by_cases hu : u ∈ Ici (Real.log m)
    · rw [indicator_of_mem hu, indicator_of_mem hu, smul_eq_mul, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 1; simp only [sArg]; push_cast; ring
    · rw [indicator_of_notMem hu, indicator_of_notMem hu, smul_zero]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi (by simp [sArg_re])]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm0.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hm0.le]
  rw [neg_div, ← div_neg]
  congr 2
  · ring
  · ring

lemma integrable_Phi (a : ℕ → ℂ) (N : ℕ) : Integrable (Phi a N) :=
  integrable_finsetSum _ fun m _ ↦ (integrable_phiTerm m).const_mul (a m)

lemma fourier_Phi {a : ℕ → ℂ} {N : ℕ} (ha : ∀ m, (m = 0 ∨ N < m) → a m = 0) (ξ : ℝ) :
    𝓕 (Phi a N) ξ = LSeries a (sArg ξ) / sArg ξ := by
  rw [LSeries_eq_sum ha, Finset.sum_div]
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold Phi
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ ↦ ?_
    by_cases hm : m = 0
    · simp [hm, ha 0 (Or.inl rfl)]
    have := fourier_phiTerm (Nat.one_le_iff_ne_zero.mpr hm) ξ
    rw [Real.fourier_real_eq_integral_exp_smul] at this
    simp_rw [smul_eq_mul] at this ⊢
    simp_rw [mul_left_comm _ (a m)]
    rw [integral_const_mul, this, mul_div_assoc]
  · intro m _
    have := ((integrable_phiTerm m).const_mul (a m)).bdd_mul (c := 1)
      (f := fun u : ℝ ↦ cexp (↑(-2 * Real.pi * u * ξ) * I)) (by fun_prop)
      (Eventually.of_forall fun u ↦ by
        rw [Complex.norm_exp_ofReal_mul_I])
    simpa [smul_eq_mul] using this

lemma norm_phiTerm_le (m : ℕ) (u : ℝ) : ‖phiTerm m u‖ ≤ 1 := by
  unfold phiTerm
  by_cases hu : u ∈ Ici (Real.log m)
  · rw [indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact (Real.log_natCast_nonneg m).trans hu
  · rw [indicator_of_notMem hu, norm_zero]; exact zero_le_one

lemma norm_Phi_le (a : ℕ → ℂ) (N : ℕ) (u : ℝ) :
    ‖Phi a N u‖ ≤ ∑ m ∈ Finset.range (N + 1), ‖a m‖ := by
  unfold Phi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_phiTerm_le m u)

lemma continuousAt_phiTerm {m : ℕ} {u : ℝ} (hu : u ≠ Real.log m) :
    ContinuousAt (phiTerm m) u := by
  unfold phiTerm
  rcases lt_or_gt_of_ne hu with h | h
  · apply continuousAt_const.congr
    filter_upwards [Iio_mem_nhds h] with w hw
    rw [indicator_of_notMem (by simpa using hw)]
  · apply (show Continuous (fun u : ℝ ↦ ((Real.exp (-u) : ℝ) : ℂ)) by fun_prop).continuousAt.congr
    filter_upwards [Ioi_mem_nhds h] with w hw
    rw [indicator_of_mem (show w ∈ Ici _ from mem_Ici.mpr hw.le)]

lemma ae_continuousAt_Phi (a : ℕ → ℂ) (N : ℕ) : ∀ᵐ u ∂volume, ContinuousAt (Phi a N) u := by
  have hfin : ((Finset.range (N + 1)).image (fun m : ℕ ↦ Real.log m) : Set ℝ).Countable :=
    (Finset.finite_toSet _).countable
  filter_upwards [hfin.ae_notMem volume] with u hu
  unfold Phi
  have : ∀ m ∈ Finset.range (N + 1), ContinuousAt (fun w ↦ a m * phiTerm m w) u := by
    intro m hm
    refine continuousAt_const.mul (continuousAt_phiTerm fun h ↦ hu ?_)
    simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
    exact ⟨m, Finset.mem_range.mp hm, h.symm⟩
  exact tendsto_finsetSum _ this

/-- `v Φ(log v) = Σ_{m ≤ v} a_m`. -/
lemma mul_Phi_log {a : ℕ → ℂ} {N : ℕ} (h0 : a 0 = 0) {v : ℝ} (hv : 0 < v) :
    (v : ℂ) * Phi a N (Real.log v) =
      ∑ m ∈ Finset.range (N + 1), a m * if (m : ℝ) ≤ v then 1 else 0 := by
  unfold Phi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  by_cases hm : m = 0
  · simp [hm, h0]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  unfold phiTerm
  by_cases hmv : (m : ℝ) ≤ v
  · rw [if_pos hmv, indicator_of_mem (show Real.log v ∈ Ici _ from
      Real.log_le_log hm0 hmv), Real.exp_neg, Real.exp_log hv]
    have : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    push_cast
    field_simp
  · rw [if_neg hmv, indicator_of_notMem (show Real.log v ∉ Ici (Real.log m) from fun h ↦
      hmv ((Real.log_le_log_iff hm0 hv).mp h))]
    simp

/-- The short sum as a difference of `vΦ(log v)` (for non-integer `x`). -/
lemma sum_Icc_eq_Phi {a : ℕ → ℂ} {N : ℕ} (ha : ∀ m, (m = 0 ∨ N < m) → a m = 0) {x h : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hh : 0 ≤ h) :
    ∑ m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, a m =
      ((x + h : ℝ) : ℂ) * Phi a N (Real.log (x + h)) - (x : ℂ) * Phi a N (Real.log x) := by
  have h0 : a 0 = 0 := ha 0 (Or.inl rfl)
  rw [mul_Phi_log h0 (by linarith), mul_Phi_log h0 hx, ← Finset.sum_sub_distrib]
  have hmem : ∀ m : ℕ, m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊ ↔ x < m ∧ (m : ℝ) ≤ x + h := by
    intro m
    rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by linarith)]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (fun e ↦ hxn m e.symm), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
  calc ∑ m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, a m
      = ∑ m ∈ Finset.range (N + 1), if m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊ then a m else 0 := by
        rw [← Finset.sum_filter]
        symm
        apply Finset.sum_subset (fun m hm ↦ (Finset.mem_filter.mp hm).2)
        · intro m hm hnot
          apply ha m (Or.inr ?_)
          by_contra hle
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm⟩)
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        simp only [hmem]
        by_cases h1 : x < m <;> by_cases h2 : (m : ℝ) ≤ x + h
        · simp [h1, h2, not_le.mpr h1]
        · simp [h1, h2, not_le.mpr h1]
        · simp [h1, h2, not_lt.mp h1]
        · exfalso; exact h2 (by linarith [not_lt.mp h1])

end Erdos385.Parseval

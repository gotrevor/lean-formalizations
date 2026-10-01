/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Masked
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Near

/-!
# Erdős #385 power saving: the near/far split for real coefficients (phase E9b)

`far_split`: for real coefficients `a` (with `mr16_masked`'s hypotheses on `a_ℂ`) the difference
`D(x) = S(x,h₁)/h₁ − S(x,h₂)/h₂` splits as `D_far + D_near` with
* `|D_near(x)| ≤ ∫_{Eₜ} |A(1+it)| dt` for every `x > 0` (`norm_winDif_fourierInv_le`);
* `∫_X^{2X} D_far² ≤ 500 X (1/T₀ + ∫_{mid∖Eₜ} |A|² + B)` (`mr16_masked`).
`D_far := D − Re D[𝓕⁻(1_E Â/s)]`; a.e. (off `ℕ`) it is `Re D[Φ − 𝓕⁻(1_E Â/s)]`.
-/

open MeasureTheory Complex Set Filter
open scoped FourierTransform

noncomputable section

namespace Erdos385.Parseval

open LeanFormalizations.Erdos385

lemma winDif_sub (f g : ℝ → ℂ) (h₁ h₂ x : ℝ) :
    winDif (fun u ↦ f u - g u) h₁ h₂ x = winDif f h₁ h₂ x - winDif g h₁ h₂ x := by
  simp only [winDif, winDelta]; ring

theorem far_split {a : ℕ → ℝ} {X T₀ h₁ h₂ : ℝ} (hX : 2 ≤ X) (hT₀ : 1 ≤ T₀) (hh₁ : 2 ≤ h₁)
    (h12 : h₁ ≤ h₂) (h2X : h₂ ≤ X / T₀ ^ 3) (ha1 : ∀ m, ‖(a m : ℂ)‖ ≤ 1)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → (a m : ℂ) = 0)
    (S : Finset ℝ) (r : ℝ) (hr : 0 ≤ r) (hS : ∀ s ∈ S, T₀ + r ≤ |s|) {B : ℝ}
    (hB : ∀ T : ℝ, X / (2 * h₁) ≤ T →
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ nearSet S r,
          ‖LSeries (fun m ↦ (a m : ℂ)) (1 + t * I)‖ ^ 2 ≤ B) :
    ∃ Dfar : ℝ → ℝ, IntegrableOn (fun x ↦ Dfar x ^ 2) (Ioc X (2 * X)) ∧
      (∀ x, 0 < x → |(shortSum a x h₁ / h₁ - shortSum a x h₂ / h₂) - Dfar x| ≤
        ∫ t in nearSet S r, ‖LSeries (fun m ↦ (a m : ℂ)) (1 + t * I)‖) ∧
      ∫ x in X..(2 * X), Dfar x ^ 2 ≤
        X * (500 * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁} \ nearSet S r,
          ‖LSeries (fun m ↦ (a m : ℂ)) (1 + t * I)‖ ^ 2) + B)) := by
  set aC : ℕ → ℂ := fun m ↦ (a m : ℂ) with haC
  have hX0 : 0 < X := by linarith
  have hh₁0 : 0 < h₁ := by linarith
  have hh₂0 : 0 < h₂ := by linarith
  set N := ⌊4 * X⌋₊
  have hsN := supp_floor hX0 hsupp
  set Et := nearSet S r
  have hEt : MeasurableSet Et := measurableSet_nearSet S r
  set E := tSet Et with hEdef
  have hE : MeasurableSet E := hEt.preimage (by fun_prop)
  set Ahat : ℝ → ℂ := fun ξ ↦ LSeries aC (sArg ξ) with hAhat
  set F : ℝ → ℂ := fun ξ ↦ Ahat ξ / sArg ξ with hFdef
  have hAc : Continuous Ahat := continuous_LSeries_sArg hX0 hsupp
  have hFc : Continuous F := continuous_LSeries_div_sArg hX0 hsupp
  set R := ∑ s ∈ S, |s| + |r|
  have hESub : E ⊆ Icc (-(R / (2 * Real.pi))) (R / (2 * Real.pi)) := fun ξ hξ ↦
    abs_le_sub_Icc (nearSet_subset S r hξ)
  have iE : Integrable (E.indicator F) :=
    (integrable_indicator_iff hE).2 (hFc.integrableOn_Icc.mono_set hESub)
  have iEA : Integrable (E.indicator Ahat) :=
    (integrable_indicator_iff hE).2 (hAc.integrableOn_Icc.mono_set hESub)
  have hEs : (fun ξ ↦ E.indicator F ξ * sArg ξ) = E.indicator Ahat := by
    funext ξ; by_cases h : ξ ∈ E
    · rw [indicator_of_mem h, indicator_of_mem h]; simp only [F]
      rw [div_mul_cancel₀ _ (sArg_ne_zero ξ)]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  set PE := 𝓕⁻ (E.indicator F) with hPE
  have hPEc : Continuous PE := continuous_fourierInv_of_integrable iE
  set D : ℝ → ℝ := fun x ↦ shortSum a x h₁ / h₁ - shortSum a x h₂ / h₂ with hD
  have hDfarI : IntegrableOn (fun x ↦ (D x - (winDif PE h₁ h₂ x).re) ^ 2) (Ioc X (2 * X)) := by
    have hDi := integrableOn_sq_shortSum a (L := X) (U := 2 * X) hh₁0.le hh₂0.le
    have hc : ContinuousOn (fun x ↦ (winDif PE h₁ h₂ x).re) (Icc X (2 * X)) :=
      Complex.continuous_re.comp_continuousOn (continuousOn_winDif hPEc hX0 hh₁0.le hh₂0.le)
    have hci : IntegrableOn (fun x ↦ (winDif PE h₁ h₂ x).re ^ 2) (Ioc X (2 * X)) :=
      ((hc.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hm : AEStronglyMeasurable (fun x ↦ (D x - (winDif PE h₁ h₂ x).re) ^ 2)
        (volume.restrict (Ioc X (2 * X))) := by
      have h1 : Measurable D := ((measurable_shortSum a h₁).div_const _).sub
        ((measurable_shortSum a h₂).div_const _)
      have h2 : Measurable fun x ↦ (winDif PE h₁ h₂ x).re :=
        Complex.measurable_re.comp (measurable_winDif hPEc.measurable h₁ h₂)
      exact ((h1.sub h2).pow_const 2).aestronglyMeasurable
    refine Integrable.mono' ((hDi.const_mul 2).add (hci.const_mul 2)) hm
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (D x + (winDif PE h₁ h₂ x).re)]
  refine ⟨fun x ↦ D x - (winDif PE h₁ h₂ x).re, hDfarI, ?_, ?_⟩
  · intro x hx
    rw [show shortSum a x h₁ / h₁ - shortSum a x h₂ / h₂ - (D x - (winDif PE h₁ h₂ x).re) =
      (winDif PE h₁ h₂ x).re by simp only [D]; ring]
    have h := norm_winDif_fourierInv_le iE (by rw [hEs]; exact iEA) hx hh₁0 hh₂0
    simp_rw [show ∀ ξ, E.indicator F ξ * sArg ξ = E.indicator Ahat ξ from
      fun ξ ↦ congrFun hEs ξ] at h
    have hre : |(winDif PE h₁ h₂ x).re| ≤ ‖winDif PE h₁ h₂ x‖ := Complex.abs_re_le_norm _
    have hint : ∫ ξ, ‖E.indicator Ahat ξ‖ =
        (2 * Real.pi)⁻¹ * ∫ t in Et, ‖LSeries aC (1 + t * I)‖ := by
      have hpt : (fun ξ ↦ ‖E.indicator Ahat ξ‖) =
          fun ξ ↦ Et.indicator (fun t ↦ ‖LSeries aC (1 + t * I)‖) (2 * Real.pi * ξ) := by
        funext ξ
        by_cases hξ : ξ ∈ E
        · have hξ' : 2 * Real.pi * ξ ∈ Et := hξ
          rw [indicator_of_mem hξ, indicator_of_mem hξ']; simp only [Ahat]; rw [sArg_eq]
        · have hξ' : 2 * Real.pi * ξ ∉ Et := hξ
          rw [indicator_of_notMem hξ, indicator_of_notMem hξ']; simp
      have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [hpt, Measure.integral_comp_mul_left (fun t ↦ Et.indicator _ t), integral_indicator hEt,
        abs_of_pos (inv_pos.2 hπ), smul_eq_mul]
    rw [hint] at h
    have hI0 : 0 ≤ ∫ t in Et, ‖LSeries aC (1 + t * I)‖ := integral_nonneg fun _ ↦ norm_nonneg _
    have hπ : 2 * (2 * Real.pi)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    calc _ ≤ ‖winDif PE h₁ h₂ x‖ := hre
      _ ≤ 2 * ((2 * Real.pi)⁻¹ * ∫ t in Et, ‖LSeries aC (1 + t * I)‖) := h
      _ ≤ ∫ t in Et, ‖LSeries aC (1 + t * I)‖ := by nlinarith
  · have hmain := mr16_masked hX hT₀ hh₁ h12 h2X ha1 hsupp S r hr hS hB
    set Q : ℝ → ℂ := fun u ↦ Phi aC N u - PE u with hQ
    -- a.e. on `Ioc X (2X)`, `D_far = Re D[Q]`
    have hnat : ∀ᵐ x : ℝ, x ∉ range (Nat.cast : ℕ → ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp ((countable_range _).measure_zero _)
    have hae : ∀ᵐ x ∂(volume.restrict (Ioc X (2 * X))),
        (D x - (winDif PE h₁ h₂ x).re) ^ 2 ≤ ‖winDif Q h₁ h₂ x‖ ^ 2 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hnat] with x hxn hxI
      have hx0 : 0 < x := hX0.trans hxI.1
      have hxn' : ∀ n : ℕ, (n : ℝ) ≠ x := fun n h ↦ hxn ⟨n, h⟩
      have hDx : (D x : ℂ) = winDif (Phi aC N) h₁ h₂ x := by
        simp only [winDif, winDelta, D]
        rw [← sum_Icc_eq_Phi hsN hx0 hxn' hh₁0.le, ← sum_Icc_eq_Phi hsN hx0 hxn' hh₂0.le]
        simp only [shortSum]; push_cast; ring
      have hQx : winDif Q h₁ h₂ x = (D x : ℂ) - winDif PE h₁ h₂ x := by
        rw [winDif_sub, hDx]
      have : D x - (winDif PE h₁ h₂ x).re = (winDif Q h₁ h₂ x).re := by
        rw [hQx]; simp
      rw [this]
      have := Complex.abs_re_le_norm (winDif Q h₁ h₂ x)
      nlinarith [abs_nonneg (winDif Q h₁ h₂ x).re, sq_abs (winDif Q h₁ h₂ x).re]
    -- integrability of `‖D[Q]‖²`
    have hQi : IntegrableOn (fun x ↦ ‖winDif Q h₁ h₂ x‖ ^ 2) (Ioc X (2 * X)) := by
      have hDi := integrableOn_sq_shortSum a (L := X) (U := 2 * X) hh₁0.le hh₂0.le
      have hc : ContinuousOn (fun x ↦ ‖winDif PE h₁ h₂ x‖) (Icc X (2 * X)) :=
        (continuousOn_winDif hPEc hX0 hh₁0.le hh₂0.le).norm
      have hci : IntegrableOn (fun x ↦ ‖winDif PE h₁ h₂ x‖ ^ 2) (Ioc X (2 * X)) :=
        ((hc.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
      have hQm : Measurable Q := (measurable_Phi aC N).sub hPEc.measurable
      refine Integrable.mono' ((hDi.const_mul 2).add (hci.const_mul 2))
        ((measurable_winDif hQm h₁ h₂).norm.pow_const 2).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hnat] with x hxn hxI
      have hx0 : 0 < x := hX0.trans hxI.1
      have hxn' : ∀ n : ℕ, (n : ℝ) ≠ x := fun n h ↦ hxn ⟨n, h⟩
      have hDx : (D x : ℂ) = winDif (Phi aC N) h₁ h₂ x := by
        simp only [winDif, winDelta, D]
        rw [← sum_Icc_eq_Phi hsN hx0 hxn' hh₁0.le, ← sum_Icc_eq_Phi hsN hx0 hxn' hh₂0.le]
        simp only [shortSum]; push_cast; ring
      have hQx : winDif Q h₁ h₂ x = (D x : ℂ) - winDif PE h₁ h₂ x := by
        rw [winDif_sub, hDx]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hQx]
      have := norm_sub_le (D x : ℂ) (winDif PE h₁ h₂ x)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      have h0 : 0 ≤ ‖(D x : ℂ) - winDif PE h₁ h₂ x‖ := norm_nonneg _
      have : ‖(D x : ℂ) - winDif PE h₁ h₂ x‖ ^ 2 ≤ (|D x| + ‖winDif PE h₁ h₂ x‖) ^ 2 :=
        pow_le_pow_left₀ h0 this 2
      simp only [Pi.add_apply]
      nlinarith [sq_abs (D x), sq_nonneg (|D x| - ‖winDif PE h₁ h₂ x‖)]
    rw [intervalIntegral.integral_of_le (by linarith)]
    have hle := setIntegral_mono_ae_restrict
      (f := fun x ↦ (D x - (winDif PE h₁ h₂ x).re) ^ 2) ?_ hQi hae
    · have : (1 / X) * ∫ x in Ioc X (2 * X), ‖winDif Q h₁ h₂ x‖ ^ 2 ≤ _ := hmain
      rw [one_div, inv_mul_le_iff₀ hX0] at this
      exact hle.trans this
    · exact hDfarI
end Erdos385.Parseval

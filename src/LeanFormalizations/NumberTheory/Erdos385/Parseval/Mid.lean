/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Low
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Bands
import LeanFormalizations.NumberTheory.Erdos385.Parseval.LogChange

/-!
# The middle band

`Δ(𝓕⁻(G/s))(x,h) = ∫_x^{x+h} (𝓕⁻ G)(log v) dv` (Fubini), then Cauchy–Schwarz on the window,
averaging over `x`, `v = e^u`, and Plancherel: `∫_X^{2X} |D|² ≤ 12 X ∫ |G|²`.
-/

open MeasureTheory Complex Set
open scoped FourierTransform

noncomputable section

namespace Erdos385.Parseval

lemma fourierInv_log_eq (G : ℝ → ℂ) {v : ℝ} (hv : 0 < v) :
    𝓕⁻ G (Real.log v) = ∫ ξ, G ξ * (v : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  rw [Real.fourierInv_eq']
  congr 1 with ξ
  rw [smul_eq_mul, mul_comm, cpow_def_of_ne_zero (by exact_mod_cast hv.ne'), ← ofReal_log hv.le]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast; ring

/-- Fubini: the window sum of a band-limited piece is the integral of `𝓕⁻ G ∘ log`. -/
lemma winDelta_eq_integral {G : ℝ → ℂ} (hG : Integrable G) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    winDelta (𝓕⁻ (fun ξ ↦ G ξ / sArg ξ)) x h = ∫ v in x..x + h, 𝓕⁻ G (Real.log v) := by
  have hF : Integrable (fun ξ ↦ G ξ / sArg ξ) := by
    refine (hG.mul_bdd (g := fun ξ ↦ (sArg ξ)⁻¹) (c := 1) ?_ (Filter.Eventually.of_forall fun ξ ↦ ?_)).congr
      (Filter.Eventually.of_forall fun ξ ↦ by simp [div_eq_mul_inv])
    · exact ((by unfold sArg; fun_prop : Continuous sArg).inv₀ sArg_ne_zero).aestronglyMeasurable
    · rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have := Complex.abs_re_le_norm (sArg ξ)
      rw [sArg_re, abs_one] at this; exact this
  rw [winDelta_fourierInv hF hx hh.le]
  have hpos : ∀ v ∈ uIoc x (x + h), 0 < v := fun v hv ↦ by
    rw [uIoc_of_le (by linarith)] at hv; linarith [hv.1]
  rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun v hv ↦
    fourierInv_log_eq G (hpos v hv))]
  rw [intervalIntegral_integral_swap]
  · congr 1 with ξ
    rw [intervalIntegral.integral_const_mul, integral_cpow (Or.inl (by simp)), sArg_eq]
    rw [add_comm (((2 * Real.pi * ξ : ℝ) : ℂ) * I) 1]
    field_simp
  · have hm : AEStronglyMeasurable (Function.uncurry fun v ξ ↦
        G ξ * ((v : ℝ) : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * I))
        ((volume.restrict (uIoc x (x + h))).prod volume) := by
      refine (hG.1.comp_snd).mul ?_
      exact (Measurable.aestronglyMeasurable (by fun_prop))
    haveI : IsFiniteMeasure (volume.restrict (uIoc x (x + h))) :=
      isFiniteMeasure_restrict.mpr (by rw [uIoc_of_le (by linarith)]; simp)
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hG.norm) hm ?_
    have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (uIoc x (x + h))).prod volume),
        p.1 ∈ uIoc x (x + h) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_uIoc)
    filter_upwards [hmem] with p hp
    simp only [Function.uncurry, norm_mul, one_mul]
    rw [norm_cpow_eq_rpow_re_of_pos (hpos _ hp)]
    simp

/-- Cauchy–Schwarz on an interval. -/
lemma norm_intervalIntegral_sq_le {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ v in a..b, f v‖ ^ 2 ≤ (b - a) * ∫ v in a..b, ‖f v‖ ^ 2 := by
  set I1 := ∫ v in a..b, ‖f v‖
  set I2 := ∫ v in a..b, ‖f v‖ ^ 2
  have h1 : ‖∫ v in a..b, f v‖ ≤ I1 := intervalIntegral.norm_integral_le_integral_norm hab
  have hI1 : 0 ≤ ‖∫ v in a..b, f v‖ := norm_nonneg _
  have hg : Continuous fun v ↦ ‖f v‖ := hf.norm
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  have hba : 0 < b - a := by linarith
  set c := I1 / (b - a)
  have h0 : 0 ≤ ∫ v in a..b, (‖f v‖ - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _
  have hexp : ∫ v in a..b, (‖f v‖ - c) ^ 2 = I2 - 2 * c * I1 + c ^ 2 * (b - a) := by
    have : ∀ v, (‖f v‖ - c) ^ 2 = ‖f v‖ ^ 2 - 2 * c * ‖f v‖ + c ^ 2 := fun v ↦ by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp [smul_eq_mul]; ring
    all_goals first
      | exact ((hg.pow 2).sub (continuous_const.mul hg)).intervalIntegrable _ _
      | exact (hg.pow 2).intervalIntegrable _ _
      | exact (continuous_const.mul hg).intervalIntegrable _ _
      | exact continuous_const.intervalIntegrable _ _
  rw [hexp] at h0
  have key : I1 ^ 2 ≤ (b - a) * I2 := by
    have : c * (b - a) = I1 := div_mul_cancel₀ _ hba.ne'
    nlinarith
  calc ‖∫ v in a..b, f v‖ ^ 2 ≤ I1 ^ 2 := pow_le_pow_left₀ hI1 h1 2
    _ ≤ _ := key

/-- Averaging windows over `x ∈ [X, 2X]`. -/
lemma integral_window_le {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hnn : ∀ v, 0 ≤ ψ v) {X h : ℝ}
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h ≤ X) :
    ∫ x in X..2 * X, ∫ v in x..x + h, ψ v ≤ h * ∫ v in X..3 * X, ψ v := by
  have hii : ∀ a b, IntervalIntegrable ψ volume a b := fun a b ↦ hψ.intervalIntegrable a b
  set Ψ : ℝ → ℝ := fun t ↦ ∫ v in X..t, ψ v
  have hΨc : Continuous Ψ := intervalIntegral.continuous_primitive hii X
  have hΨii : ∀ a b, IntervalIntegrable Ψ volume a b := fun a b ↦ hΨc.intervalIntegrable a b
  have hwin : ∀ x, ∫ v in x..x + h, ψ v = Ψ (x + h) - Ψ x := fun x ↦
    (intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)).symm
  have hmono : ∀ s t, s ≤ t → Ψ s ≤ Ψ t := fun s t hst ↦ by
    have : Ψ t - Ψ s = ∫ v in s..t, ψ v :=
      intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)
    have := intervalIntegral.integral_nonneg (μ := volume) hst (fun v _ ↦ hnn v)
    linarith
  simp_rw [hwin]
  have hc2 : Continuous fun x ↦ Ψ (x + h) := hΨc.comp (continuous_add_const h)
  rw [intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) (hΨii _ _),
    intervalIntegral.integral_comp_add_right (fun x ↦ Ψ x)]
  have e1 : ∫ x in X + h..2 * X + h, Ψ x = (∫ x in X..2 * X + h, Ψ x) - ∫ x in X..X + h, Ψ x :=
    (intervalIntegral.integral_interval_sub_left (hΨii _ _) (hΨii _ _)).symm
  have e2 : ∫ x in X..2 * X, Ψ x = (∫ x in X..2 * X + h, Ψ x) - ∫ x in 2 * X..2 * X + h, Ψ x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hΨii X (2 * X)) (hΨii _ (2 * X + h))]
    ring
  rw [e1, e2]
  have b1 : ∫ x in 2 * X..2 * X + h, Ψ x ≤ h * Ψ (3 * X) := by
    have := intervalIntegral.integral_mono_on (f := Ψ) (g := fun _ ↦ Ψ (3 * X)) (a := 2 * X)
      (b := 2 * X + h) (by linarith) (hΨii _ _) intervalIntegrable_const
      (fun v hv ↦ hmono v (3 * X) (by linarith [hv.2]))
    simpa using this
  have b2 : 0 ≤ ∫ x in X..X + h, Ψ x := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro v hv
    have : Ψ X = 0 := by simp [Ψ]
    linarith [hmono X v hv.1]
  have : Ψ (3 * X) = ∫ v in X..3 * X, ψ v := rfl
  linarith

lemma continuous_fourierInv_of_integrable {G : ℝ → ℂ} (hG : Integrable G) : Continuous (𝓕⁻ G) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg hG

/-- `∫_X^{3X} ‖𝓕⁻G(log v)‖² ≤ 3X ∫‖G‖²`. -/
lemma integral_log_band_le {G : ℝ → ℂ} (hG : Integrable G) {K : ℝ} (hK : ∀ ξ, ‖G ξ‖ ≤ K)
    (hc : ∀ᵐ ξ, ContinuousAt G ξ) {X : ℝ} (hX : 0 < X) :
    ∫ v in X..3 * X, ‖𝓕⁻ G (Real.log (max v X))‖ ^ 2 ≤ 3 * X * ∫ ξ, ‖G ξ‖ ^ 2 := by
  obtain ⟨hγ2, hγeq⟩ := plancherel_fourierInv hG hK hc
  have hγc := continuous_fourierInv_of_integrable hG
  set ψ : ℝ → ℝ := fun v ↦ ‖𝓕⁻ G (Real.log (max v X))‖ ^ 2
  have hψc : Continuous ψ := by
    have : Continuous fun v : ℝ ↦ Real.log (max v X) :=
      Real.continuousOn_log.comp_continuous (continuous_id.max continuous_const)
        (fun v ↦ by simp only [mem_compl_iff, mem_singleton_iff]; positivity)
    exact ((hγc.comp this).norm).pow 2
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun v ↦ by positivity)
      hψc.aestronglyMeasurable.restrict]
  have hl : ∫⁻ v in Icc X (3 * X), ENNReal.ofReal (ψ v) =
      ∫⁻ v in Icc X (3 * X), ‖𝓕⁻ G (Real.log v)‖ₑ ^ 2 * ENNReal.ofReal (v ^ 0) := by
    refine setLIntegral_congr_fun measurableSet_Icc fun v hv ↦ ?_
    simp only [ψ, max_eq_left hv.1, pow_zero, ENNReal.ofReal_one, mul_one]
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hl]
  have hb := lintegral_log_le (G := 𝓕⁻ G) 0 hX (by linarith : X ≤ 3 * X)
  have hfin : ∫⁻ u, ‖𝓕⁻ G u‖ₑ ^ 2 = ENNReal.ofReal (∫ ξ, ‖G ξ‖ ^ 2) := by
    rw [← hγeq, ofReal_integral_eq_lintegral_ofReal hγ2
      (Filter.Eventually.of_forall fun _ ↦ by positivity)]
    congr 1 with u
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hfin, zero_add, pow_one, ← ENNReal.ofReal_mul (by linarith)] at hb
  have h0 : 0 ≤ 3 * X * ∫ ξ, ‖G ξ‖ ^ 2 :=
    mul_nonneg (by linarith) (integral_nonneg fun _ ↦ by positivity)
  exact ENNReal.toReal_le_of_le_ofReal h0 hb

/-- **Middle band.** `∫_X^{2X} |D|² ≤ 12 X ∫ |G|²`. -/
theorem integral_winDif_mid_le {G : ℝ → ℂ} (hG : Integrable G) {K : ℝ} (hK : ∀ ξ, ‖G ξ‖ ≤ K)
    (hc : ∀ᵐ ξ, ContinuousAt G ξ) {X h₁ h₂ : ℝ} (hX : 0 < X) (hh₁ : 0 < h₁) (h12 : h₁ ≤ h₂)
    (h2X : h₂ ≤ X) :
    ∫ x in X..2 * X, ‖winDif (𝓕⁻ (fun ξ ↦ G ξ / sArg ξ)) h₁ h₂ x‖ ^ 2 ≤
      12 * X * ∫ ξ, ‖G ξ‖ ^ 2 := by
  have hh₂ : 0 < h₂ := hh₁.trans_le h12
  set γ := 𝓕⁻ G
  have hγc : Continuous γ := continuous_fourierInv_of_integrable hG
  set f : ℝ → ℂ := fun v ↦ γ (Real.log (max v X))
  have hlogc : Continuous fun v : ℝ ↦ Real.log (max v X) :=
    Real.continuousOn_log.comp_continuous (continuous_id.max continuous_const)
      (fun v ↦ by simp only [mem_compl_iff, mem_singleton_iff]; positivity)
  have hfc : Continuous f := hγc.comp hlogc
  set ψ : ℝ → ℝ := fun v ↦ ‖f v‖ ^ 2
  have hψc : Continuous ψ := hfc.norm.pow 2
  have hii : ∀ a b, IntervalIntegrable ψ volume a b := fun a b ↦ hψc.intervalIntegrable a b
  set W : ℝ → ℝ → ℝ := fun h x ↦ ∫ v in x..x + h, ψ v
  have hWc : ∀ h, Continuous (W h) := by
    intro h
    have hp := intervalIntegral.continuous_primitive hii X
    have : W h = fun x ↦ (∫ v in X..x + h, ψ v) - ∫ v in X..x, ψ v := by
      funext x
      exact (intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)).symm
    rw [this]
    exact (hp.comp (continuous_add_const h)).sub hp
  -- the window piece
  have hwin : ∀ x, X ≤ x → ∀ h, 0 < h →
      ‖winDelta (𝓕⁻ (fun ξ ↦ G ξ / sArg ξ)) x h / h‖ ^ 2 ≤ W h x / h := by
    intro x hx h hh
    rw [winDelta_eq_integral hG (by linarith) hh]
    have : ∫ v in x..x + h, γ (Real.log v) = ∫ v in x..x + h, f v := by
      refine intervalIntegral.integral_congr fun v hv ↦ ?_
      rw [uIcc_of_le (by linarith)] at hv
      simp only [f, max_eq_left (hx.trans hv.1)]
    rw [this, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_pow]
    have hcs := norm_intervalIntegral_sq_le hfc (by linarith : x ≤ x + h)
    rw [show x + h - x = h by ring] at hcs
    rw [div_le_div_iff₀ (by positivity) hh]
    calc ‖∫ v in x..x + h, f v‖ ^ 2 * h ≤ h * W h x * h := by gcongr
      _ = W h x * h ^ 2 := by ring
  have hpt : ∀ x ∈ Icc X (2 * X),
      ‖winDif (𝓕⁻ (fun ξ ↦ G ξ / sArg ξ)) h₁ h₂ x‖ ^ 2 ≤
        2 * (W h₁ x / h₁) + 2 * (W h₂ x / h₂) := by
    intro x hx
    have e1 := hwin x hx.1 h₁ hh₁
    have e2 := hwin x hx.1 h₂ hh₂
    unfold winDif
    set a := winDelta (𝓕⁻ (fun ξ ↦ G ξ / sArg ξ)) x h₁ / h₁
    set b := winDelta (𝓕⁻ (fun ξ ↦ G ξ / sArg ξ)) x h₂ / h₂
    have := norm_sub_le a b
    have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
    have h3 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ h0 this 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  -- integrability of the left side
  set g := 𝓕⁻ (fun ξ ↦ G ξ / sArg ξ)
  have hF : Integrable (fun ξ ↦ G ξ / sArg ξ) := by
    refine (hG.mul_bdd (g := fun ξ ↦ (sArg ξ)⁻¹) (c := 1) ?_
      (Filter.Eventually.of_forall fun ξ ↦ ?_)).congr
      (Filter.Eventually.of_forall fun ξ ↦ by simp [div_eq_mul_inv])
    · exact ((by unfold sArg; fun_prop : Continuous sArg).inv₀ sArg_ne_zero).aestronglyMeasurable
    · rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have := Complex.abs_re_le_norm (sArg ξ)
      rw [sArg_re, abs_one] at this; exact this
  have hgc : Continuous g := continuous_fourierInv_of_integrable hF
  have hlc : ∀ h : ℝ, Continuous fun x : ℝ ↦ Real.log (max (x + h) X) := fun h ↦
    Real.continuousOn_log.comp_continuous ((continuous_add_const h).max continuous_const)
      (fun v ↦ by simp only [mem_compl_iff, mem_singleton_iff]; positivity)
  have hLi : IntervalIntegrable (fun x ↦ ‖winDif g h₁ h₂ x‖ ^ 2) volume X (2 * X) := by
    let D : ℝ → ℂ := fun x ↦
      ((((x + h₁ : ℝ) : ℂ) * g (Real.log (max (x + h₁) X)) -
        (x : ℂ) * g (Real.log (max (x + 0) X))) / h₁ -
      (((x + h₂ : ℝ) : ℂ) * g (Real.log (max (x + h₂) X)) -
        (x : ℂ) * g (Real.log (max (x + 0) X))) / h₂)
    have hDc : Continuous D := by
      have := hgc.comp (hlc h₁); have := hgc.comp (hlc h₂); have := hgc.comp (hlc 0)
      fun_prop
    refine ContinuousOn.intervalIntegrable ((hDc.norm.pow 2).continuousOn.congr ?_)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    simp only [D, winDif, winDelta, add_zero, max_eq_left hx.1,
      max_eq_left (by linarith [hx.1] : X ≤ x + h₁), max_eq_left (by linarith [hx.1] : X ≤ x + h₂)]
  have hRi : ∀ h, IntervalIntegrable (fun x ↦ 2 * (W h x / h)) volume X (2 * X) := fun h ↦
    ((continuous_const.mul ((hWc h).div_const h))).intervalIntegrable _ _
  calc ∫ x in X..2 * X, ‖winDif g h₁ h₂ x‖ ^ 2
      ≤ ∫ x in X..2 * X, (2 * (W h₁ x / h₁) + 2 * (W h₂ x / h₂)) :=
        intervalIntegral.integral_mono_on (by linarith) hLi ((hRi h₁).add (hRi h₂)) hpt
    _ = 2 / h₁ * (∫ x in X..2 * X, W h₁ x) + 2 / h₂ * ∫ x in X..2 * X, W h₂ x := by
        rw [intervalIntegral.integral_add (hRi h₁) (hRi h₂)]
        simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
        ring
    _ ≤ 2 / h₁ * (h₁ * ∫ v in X..3 * X, ψ v) + 2 / h₂ * (h₂ * ∫ v in X..3 * X, ψ v) := by
        gcongr
        · exact integral_window_le hψc (fun _ ↦ by positivity) hX hh₁.le (h12.trans h2X)
        · exact integral_window_le hψc (fun _ ↦ by positivity) hX hh₂.le h2X
    _ = 4 * ∫ v in X..3 * X, ψ v := by field_simp; ring
    _ ≤ 4 * (3 * X * ∫ ξ, ‖G ξ‖ ^ 2) := by
        gcongr; exact integral_log_band_le hG hK hc hX
    _ = 12 * X * ∫ ξ, ‖G ξ‖ ^ 2 := by ring

end Erdos385.Parseval

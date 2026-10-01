/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Pointwise Plancherel for bounded, integrable, a.e.-continuous functions

Mathlib has Plancherel only for the abstract `L²` Fourier transform (`Lp.norm_fourier_eq`), with no
bridge to the pointwise integral `𝓕 f` of an `L¹ ∩ L²` function.  Here:

`plancherel_lintegral : ∫⁻ ‖𝓕 f‖ₑ² = ∫⁻ ‖f‖ₑ²` for `f` integrable, bounded and a.e. continuous.

Proof (Gaussian regularization, the mechanism of mathlib's Fourier inversion):
`∫ e^{-‖ξ‖²/c} |𝓕 f ξ|² = ∫ conj (f x) · (K_c ⋆ f)(x)` by the multiplication formula, where `K_c` is
the Gaussian approximate identity; `(K_c ⋆ f)(x) → f x` at continuity points
(`Real.tendsto_integral_gaussian_smul'`), dominated by `M ‖f x‖`; and monotone convergence in `c`
on the left.
-/

open MeasureTheory Filter Complex Module
open scoped Topology FourierTransform RealInnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace Erdos385.Parseval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The Gaussian approximate identity applied to `f`. -/
def gaussSmooth (f : V → ℂ) (c : ℝ) (v : V) : ℂ :=
  ∫ w : V, ((Real.pi * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) * cexp (-Real.pi ^ 2 * c * ‖v - w‖ ^ 2)) • f w

/-- The regularized inverse transform of `𝓕 f` is the Gaussian smoothing of `f`. -/
lemma fourierInv_gauss_mul_fourier {f : V → ℂ} (hf : Integrable f) {c : ℝ} (hc : 0 < c) (v : V) :
    𝓕⁻ (fun w ↦ cexp (-c⁻¹ * ‖w‖ ^ 2) • 𝓕 f w) v = gaussSmooth f c v := by
  have J : Integrable (fun w ↦ cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫)) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
  have h1 : 𝓕⁻ (fun w ↦ cexp (-c⁻¹ * ‖w‖ ^ 2) • 𝓕 f w) v =
      ∫ w : V, cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫) • (𝓕 f) w := by
    rw [Real.fourierInv_eq]
    congr 1 with w
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add, real_inner_comm]
    congr 2
    push_cast
    ring
  have h2 : (∫ w : V, cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫) • (𝓕 f) w) =
      ∫ w : V, 𝓕 (fun w ↦ cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫)) w • f w := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner J hf).symm
  rw [h1, h2, gaussSmooth]
  congr with w
  rw [fourier_gaussian_innerProductSpace' (by simpa)]
  congr
  · simp
  · simp; ring


lemma continuous_fourier_of_integrable {f : V → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

lemma norm_fourier_le {f : V → ℂ} (ξ : V) : ‖𝓕 f ξ‖ ≤ ∫ v, ‖f v‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

lemma integrable_gauss_mul_fourier {f : V → ℂ} (hf : Integrable f) {c : ℝ} (hc : 0 < c) :
    Integrable (fun w ↦ cexp (-c⁻¹ * ‖w‖ ^ 2) • 𝓕 f w) := by
  have hg : Integrable (fun w : V ↦ cexp (-(c⁻¹ : ℂ) * ‖w‖ ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V)
      (b := (c⁻¹ : ℂ)) (by simpa using hc) 0 0
  simp only [smul_eq_mul]
  convert hg.mul_bdd (continuous_fourier_of_integrable hf).aestronglyMeasurable
    (Eventually.of_forall fun ξ ↦ norm_fourier_le ξ) using 3
  push_cast; ring

lemma gaussSmooth_norm_le {f : V → ℂ} {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) {c : ℝ} (hc : 0 < c)
    (v : V) : ‖gaussSmooth f c v‖ ≤ M := by
  set d : ℝ := (finrank ℝ V : ℝ)
  have hb : 0 < Real.pi ^ 2 * c := by positivity
  let kr : V → ℝ := fun w ↦ (Real.pi * c) ^ (d / 2) * Real.exp (-(Real.pi ^ 2 * c) * ‖v - w‖ ^ 2)
  have hG : ∫ w : V, Real.exp (-(Real.pi ^ 2 * c) * ‖v - w‖ ^ 2) =
      (Real.pi / (Real.pi ^ 2 * c)) ^ (d / 2) := by
    rw [integral_sub_left_eq_self (fun w ↦ Real.exp (-(Real.pi ^ 2 * c) * ‖w‖ ^ 2)),
      GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  have hk1 : ∫ w, kr w = 1 := by
    simp only [kr]
    rw [integral_const_mul, hG, ← Real.mul_rpow (by positivity) (by positivity)]
    have : Real.pi * c * (Real.pi / (Real.pi ^ 2 * c)) = 1 := by
      field_simp
    rw [this, Real.one_rpow]
  have hkint : Integrable kr := Integrable.of_integral_ne_zero (by rw [hk1]; norm_num)
  have hnorm : ∀ w, ‖((Real.pi * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) *
      cexp (-Real.pi ^ 2 * c * ‖v - w‖ ^ 2))‖ = kr w := by
    intro w
    rw [norm_mul, Complex.norm_exp]
    have h1 : ((Real.pi : ℂ) * c) = ((Real.pi * c : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [kr, d]
    congr 1
    · congr 1
      simp
    · congr 1
      simp [← Complex.ofReal_pow]
  calc ‖gaussSmooth f c v‖ ≤ ∫ w, ‖((Real.pi * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) *
        cexp (-Real.pi ^ 2 * c * ‖v - w‖ ^ 2)) • f w‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w, kr w * M := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w ↦ norm_nonneg _)
          (hkint.mul_const M) (Eventually.of_forall fun w ↦ ?_)
        simp only; rw [norm_smul, hnorm]
        exact mul_le_mul_of_nonneg_left (hM w) (by positivity)
    _ = M := by rw [integral_mul_const, hk1, one_mul]

theorem plancherel_lintegral {f : V → ℂ} (hf : Integrable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (hcont : ∀ᵐ x, ContinuousAt f x) :
    ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  -- (i) the multiplication formula
  have hi : ∀ c : ℝ, 0 < c → ∫ ξ, conj (𝓕 f ξ) * (cexp (-c⁻¹ * ‖ξ‖ ^ 2) • 𝓕 f ξ) =
      ∫ x, conj (f x) * gaussSmooth f c x := by
    intro c hc
    have := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ) (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner hf (integrable_gauss_mul_fourier hf hc)
    simp_rw [← fourierInv_gauss_mul_fourier hf hc]
    calc _ = ∫ ξ, cexp (-((c : ℂ)⁻¹ * ‖ξ‖ ^ 2)) * 𝓕 f ξ * conj (𝓕 f ξ) := by
            congr 1 with ξ; simp only [smul_eq_mul, neg_mul]; push_cast; ring
      _ = ∫ x, 𝓕⁻ (fun w ↦ cexp (-((c : ℂ)⁻¹ * ‖w‖ ^ 2)) * 𝓕 f w) x * conj (f x) := by
            simp at this; exact this
      _ = _ := by congr 1 with x; simp only [smul_eq_mul, neg_mul]; push_cast; ring
  have hgs_cont : ∀ c : ℝ, 0 < c → Continuous (gaussSmooth f c) := by
    intro c hc
    have : gaussSmooth f c = 𝓕⁻ (fun w ↦ cexp (-c⁻¹ * ‖w‖ ^ 2) • 𝓕 f w) :=
      funext fun v ↦ (fourierInv_gauss_mul_fourier hf hc v).symm
    rw [this]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner.neg (integrable_gauss_mul_fourier hf hc)
  -- (ii) the approximate identity
  have hii : Tendsto (fun c : ℝ ↦ ∫ x, conj (f x) * gaussSmooth f c x) atTop
      (𝓝 (∫ x, conj (f x) * f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖ * M)
    · filter_upwards [Ioi_mem_atTop 0] with c hc
      exact (Complex.continuous_conj.comp_aestronglyMeasurable hf.1).mul
        (hgs_cont c hc).aestronglyMeasurable
    · filter_upwards [Ioi_mem_atTop 0] with c hc
      filter_upwards with x
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (gaussSmooth_norm_le hM hc x) (norm_nonneg _)
    · exact hf.norm.mul_const M
    · filter_upwards [hcont] with x hx
      exact (Real.tendsto_integral_gaussian_smul' hf hx).const_mul _
  -- (iii) monotone convergence on the Fourier side
  have hF := continuous_fourier_of_integrable hf
  let a : ℕ → V → ℝ≥0∞ := fun n ξ ↦
    ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * ‖ξ‖ ^ 2) * ‖𝓕 f ξ‖ ^ 2)
  have hlim : Tendsto (fun n ↦ ∫⁻ ξ, a n ξ) atTop (𝓝 (∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ 2)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (Continuous.measurable (by fun_prop)).ennreal_ofReal.aemeasurable
    · filter_upwards with ξ
      intro n m hnm
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (n : ℝ) + 1 ≤ m + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
      have := inv_anti₀ (by positivity) this
      linarith
    · filter_upwards with ξ
      have h0 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ by simp
      have : Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) + 1)⁻¹ * ‖ξ‖ ^ 2) * ‖𝓕 f ξ‖ ^ 2) atTop
          (𝓝 (Real.exp (-0 * ‖ξ‖ ^ 2) * ‖𝓕 f ξ‖ ^ 2)) := by
        apply Tendsto.mul_const
        exact (Real.continuous_exp.tendsto _).comp ((h0.neg).mul_const _)
      simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at this
      have := (ENNReal.continuous_ofReal.tendsto _).comp this
      rw [show ‖𝓕 f ξ‖ₑ ^ 2 = ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]]
      exact this
  have hval : ∀ n : ℕ, ∫⁻ ξ, a n ξ =
      ENNReal.ofReal (∫ x, conj (f x) * gaussSmooth f ((n : ℝ) + 1) x).re := by
    intro n
    have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [← hi _ hc]
    have hpt : ∀ ξ, conj (𝓕 f ξ) * cexp (-↑((n : ℝ) + 1)⁻¹ * ↑‖ξ‖ ^ 2) • 𝓕 f ξ =
        ((Real.exp (-((n : ℝ) + 1)⁻¹ * ‖ξ‖ ^ 2) * ‖𝓕 f ξ‖ ^ 2 : ℝ) : ℂ) := by
      intro ξ
      rw [smul_eq_mul, mul_left_comm, Complex.conj_mul']
      push_cast
      ring
    have hcint : Integrable (fun ξ ↦ conj (𝓕 f ξ) * cexp (-↑((n : ℝ) + 1)⁻¹ * ↑‖ξ‖ ^ 2) • 𝓕 f ξ) :=
      (integrable_gauss_mul_fourier hf hc).bdd_mul
        (Complex.continuous_conj.comp hF).aestronglyMeasurable
        (Eventually.of_forall fun ξ ↦ (Complex.norm_conj _).le.trans (norm_fourier_le ξ))
    have hint : Integrable (fun ξ ↦ Real.exp (-((n : ℝ) + 1)⁻¹ * ‖ξ‖ ^ 2) * ‖𝓕 f ξ‖ ^ 2) := by
      have h2 := (integrable_congr (Eventually.of_forall hpt)).mp hcint
      exact h2.re.congr (Eventually.of_forall fun ξ ↦ by simp only [RCLike.re_to_complex, Complex.ofReal_re])
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_complex_ofReal, Complex.ofReal_re,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ξ ↦ by positivity)]
  have hlim2 : Tendsto (fun n : ℕ ↦ ∫⁻ ξ, a n ξ) atTop
      (𝓝 (ENNReal.ofReal (∫ x, conj (f x) * f x).re)) := by
    simp_rw [hval]
    refine (ENNReal.continuous_ofReal.tendsto _).comp
      ((Complex.continuous_re.tendsto _).comp (hii.comp ?_))
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  rw [tendsto_nhds_unique hlim hlim2]
  have hpt : ∀ x, conj (f x) * f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [Complex.conj_mul']; push_cast; ring
  have hint : Integrable (fun x ↦ ‖f x‖ ^ 2) := by
    refine (hf.norm.mul_const M).mono' (hf.1.norm.pow 2) (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_complex_ofReal, Complex.ofReal_re,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ξ ↦ by positivity)]
  congr 1 with x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end Erdos385.Parseval

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.ContourTools
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.LocalLog
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Deviation

/-!
# Erdős #385 power saving: the contour for local zero detection (phase E9b, crux step (c))

`vkDev_lt_of_zeroFree`: if no zero with `Re ρ ≥ 1 − 2η − 8 log log P/log P` lies within
`4 P^{η/3} log P` of `t`, then `‖vkDev f P t‖ < P^{1−η}` (for `8 P^{η/3} log P ≤ |t| ≤ P⁴`,
`η ≤ 1/16`, `P ≥ P₀`).  Notation `ℓ = log P`, `λ = log ℓ`, `η₂ = η + 3λ/ℓ`, `L = 2P^{η/3}ℓ`,
`c = 1 + 1/ℓ`, `σ₁ = 1 − η₂`, `G(s) = F(s) P^s H(s + it)`.
V4 at `Re s = 2`; tails `|y| > P`; shift `[c, 2] × [−P, P]`; split `Re s = c` at `±L`; shift
`[σ₁, c] × [−L, L]`, where `local_logDeriv_bound` gives `|H| ≤ 12K₁ℓ² + 1`; `P^{σ₁} = P^{1−η}/ℓ³`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex LeanFormalizations.Literature

/-- The size conditions on `P`, all eventually true. -/
lemma zc_eventually {a y₁ Q c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 ≤ c₁) : ∀ᶠ P : ℝ in atTop,
    1 ≤ a * P ∧ 16 ≤ P ∧ 1 ≤ Real.log (Real.log P) ∧
    48 * Real.log (Real.log P) ≤ Real.log P ∧ 2 * P ^ ((1 : ℝ) / 48) * Real.log P ≤ P ∧
    y₁ ≤ 6 * Real.log P ∧ Q ≤ Real.log P ∧ c₁ * Real.log P ≤ √P := by
  have hll : Tendsto (fun P : ℝ => Real.log (Real.log P)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_log_atTop
  have h4 := (isLittleO_log_id_atTop.comp_tendsto tendsto_log_atTop).bound
    (show (0 : ℝ) < 1 / 48 by norm_num)
  have h5 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 47 / 48 by norm_num)).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have h7 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show (0 : ℝ) < 1 / (c₁ + 1) by positivity)
  filter_upwards [eventually_ge_atTop (1 / a), eventually_ge_atTop (16 : ℝ),
    hll.eventually_ge_atTop 1, h4, h5, h7,
    tendsto_log_atTop.eventually_ge_atTop (max (y₁ / 6) Q),
    eventually_gt_atTop (1 : ℝ)] with P hPa hP16 hl1 h4 h5 h7 hlq hP1
  have hP0 : 0 < P := by linarith
  have hl0 : 0 ≤ Real.log P := Real.log_nonneg hP1.le
  have hll0 : 0 ≤ Real.log (Real.log P) := by linarith
  simp only [Function.comp_apply, id, Real.norm_eq_abs, abs_of_nonneg hl0,
    abs_of_nonneg hll0] at h4
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ P ^ ((47 : ℝ) / 48))] at h5
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ P ^ ((1 : ℝ) / 2))] at h7
  refine ⟨?_, hP16, hl1, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ ha] at hPa; linarith
  · have e : P ^ ((1 : ℝ) / 48) * P ^ ((47 : ℝ) / 48) = P := by
      rw [← Real.rpow_add hP0]; norm_num
    have hp : 0 ≤ P ^ ((1 : ℝ) / 48) := by positivity
    calc 2 * P ^ ((1 : ℝ) / 48) * Real.log P = 2 * (P ^ ((1 : ℝ) / 48) * Real.log P) := by ring
      _ ≤ 2 * (P ^ ((1 : ℝ) / 48) * (1 / 2 * P ^ ((47 : ℝ) / 48))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hp) (by norm_num)
      _ = P ^ ((1 : ℝ) / 48) * P ^ ((47 : ℝ) / 48) := by ring
      _ = P := e
  · have := le_max_left (y₁ / 6) Q; linarith
  · exact (le_max_right _ _).trans hlq
  · rw [Real.sqrt_eq_rpow]
    have hp : 0 ≤ P ^ ((1 : ℝ) / 2) := by positivity
    calc c₁ * Real.log P ≤ c₁ * (1 / (c₁ + 1) * P ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left h7 hc₁
      _ = c₁ / (c₁ + 1) * P ^ ((1 : ℝ) / 2) := by ring
      _ ≤ 1 * P ^ ((1 : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_right _ hp
          rw [div_le_one (by positivity)]; linarith
      _ = P ^ ((1 : ℝ) / 2) := one_mul _

/-- The local Landau property delivered by `local_logDeriv_bound`. -/
def LocalLogProp (K₁ y₁ : ℝ) : Prop :=
  ∀ η₂ y₀ : ℝ, 0 < η₂ → η₂ ≤ 1 / 8 → y₁ ≤ |y₀| →
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 5 / 2 * η₂ < ‖ρ - (1 + η₂ + y₀ * I)‖) →
    ∀ σ : ℝ, 1 - η₂ ≤ σ → σ ≤ 1 + 3 * η₂ →
      ‖zLD (σ + y₀ * I)‖ ≤ K₁ * (Real.log |y₀| +
        (Real.log (Real.log |y₀|) + Real.log (1 / η₂) + 1) / η₂)

set_option maxHeartbeats 1000000 in
/-- **`H` on the zero-free box**: `ζ(w) ≠ 0`, `w ≠ 1`, `‖H(w)‖ ≤ 12 K₁ ℓ² + 1` for
`1 − η₂ ≤ Re w ≤ 1 + 3η₂`, `|Im w − t| ≤ 2P^{η/3}ℓ`. -/
lemma box_H_bound {K₁ y₁ : ℝ} (hK₁ : 0 ≤ K₁) (hloc : LocalLogProp K₁ y₁) {P η t : ℝ}
    (hP : 16 ≤ P) (hlam1 : 1 ≤ Real.log (Real.log P))
    (h48 : 48 * Real.log (Real.log P) ≤ Real.log P) (hη : 0 < η) (hη16 : η ≤ 1 / 16)
    (ht4 : |t| ≤ P ^ 4) (hLP : 2 * P ^ (η / 3) * Real.log P ≤ P)
    (hty : 8 * P ^ (η / 3) * Real.log P ≤ |t|) (hy₁ : y₁ ≤ 6 * Real.log P)
    (hfree : ∀ ρ : ℂ, riemannZeta ρ = 0 →
      1 - 2 * η - 8 * Real.log (Real.log P) / Real.log P ≤ ρ.re →
        4 * P ^ (η / 3) * Real.log P < |ρ.im - t|)
    (w : ℂ) (hw1 : 1 - (η + 3 * Real.log (Real.log P) / Real.log P) ≤ w.re)
    (hw2 : w.re ≤ 1 + 3 * (η + 3 * Real.log (Real.log P) / Real.log P))
    (hw3 : |w.im - t| ≤ 2 * P ^ (η / 3) * Real.log P) :
    riemannZeta w ≠ 0 ∧ w ≠ 1 ∧ ‖zetaH w‖ ≤ 12 * K₁ * Real.log P ^ 2 + 1 := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log P := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = Real.log ℓ := ⟨_, rfl⟩
  rw [← hℓ, ← hlam] at h48 hlam1 hfree hw1 hw2
  rw [← hℓ] at hLP hty hy₁ hw3 ⊢
  have hP0 : 0 < P := by linarith
  have hℓ2 : 2 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le hP0]
    have := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by
          have h0 := Real.exp_pos 1
          nlinarith
      _ ≤ P := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨η₂, hη₂⟩ : ∃ η₂, η₂ = η + 3 * lam / ℓ := ⟨_, rfl⟩
  rw [← hη₂] at hw1 hw2
  have hlamℓ : 3 * lam / ℓ ≤ 1 / 16 := by
    rw [div_le_iff₀ hℓ0]; linarith
  have h3l : 3 / ℓ ≤ 3 * lam / ℓ := div_le_div_of_nonneg_right (by linarith) hℓ0.le
  have hη₂0 : 0 < η₂ := by rw [hη₂]; have : 0 < 3 * lam / ℓ := by positivity
                           linarith
  have hη₂8 : η₂ ≤ 1 / 8 := by rw [hη₂]; linarith
  have hinvη : 1 / η₂ ≤ ℓ := by
    rw [div_le_iff₀ hη₂0]
    have : 3 / ℓ ≤ η₂ := by rw [hη₂]; linarith
    have := (div_le_iff₀ hℓ0).1 (le_trans (by
      apply div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 3) hℓ0.le) this)
    linarith
  obtain ⟨Lw, hLw⟩ : ∃ Lw, Lw = 2 * P ^ (η / 3) * ℓ := ⟨_, rfl⟩
  have hPη : 1 ≤ P ^ (η / 3) := Real.one_le_rpow (by linarith) (by positivity)
  have hLw4 : 2 * ℓ ≤ Lw := by rw [hLw]; nlinarith
  rw [← hLw] at hLP hw3
  have hfour : 4 * P ^ (η / 3) * ℓ = 2 * Lw := by rw [hLw]; ring
  have height : 8 * P ^ (η / 3) * ℓ = 4 * Lw := by rw [hLw]; ring
  rw [hfour] at hfree
  rw [height] at hty
  set y₀ := w.im with hy₀
  set σ := w.re with hσ
  have hy₀lo : 3 * Lw ≤ |y₀| := by
    have := abs_sub_abs_le_abs_sub t y₀
    rw [abs_sub_comm] at hw3; linarith
  have hy₀1 : y₁ ≤ |y₀| := by linarith
  -- the Landau hypothesis at height `y₀`
  have hfree' : ∀ ρ : ℂ, riemannZeta ρ = 0 → 5 / 2 * η₂ < ‖ρ - (1 + η₂ + y₀ * I)‖ := by
    intro ρ hρ
    by_contra hcon
    push Not at hcon
    have hre := Complex.abs_re_le_norm (ρ - (1 + η₂ + y₀ * I))
    have him := Complex.abs_im_le_norm (ρ - (1 + η₂ + y₀ * I))
    have e1 : (ρ - (1 + η₂ + y₀ * I)).re = ρ.re - 1 - η₂ := by simp; ring
    have e2 : (ρ - (1 + η₂ + y₀ * I)).im = ρ.im - y₀ := by simp
    rw [e1] at hre; rw [e2] at him
    have hρre : 1 - 2 * η - 8 * lam / ℓ ≤ ρ.re := by
      have : 8 * lam / ℓ ≥ 9 / 2 * (lam / ℓ) := by
        rw [ge_iff_le, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by nlinarith) hℓ0.le
      have h1 := (abs_le.1 hre).1
      have e3 : η₂ = η + 3 * (lam / ℓ) := by rw [hη₂]; ring
      rw [e3] at h1 hcon
      have : 0 ≤ lam / ℓ := div_nonneg (by linarith) hℓ0.le
      have e4 : 8 * lam / ℓ = 8 * (lam / ℓ) := by ring
      rw [e4]
      nlinarith
    have h1 := hfree ρ hρ hρre
    have h2 : |ρ.im - t| ≤ |ρ.im - y₀| + |y₀ - t| := by
      have := abs_sub_le ρ.im y₀ t; linarith
    have h3 : |ρ.im - y₀| ≤ 1 := by linarith
    linarith
  have hw : w = (σ : ℂ) + y₀ * I := (Complex.re_add_im w).symm
  have hz : riemannZeta w ≠ 0 := by
    intro h0
    have h1 := hfree' w h0
    have e : w - (1 + η₂ + y₀ * I) = ((σ - 1 - η₂ : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at h1
    have : |σ - 1 - η₂| ≤ 2 * η₂ := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hy0 : 0 < |y₀| := by linarith
  have hw1' : w ≠ 1 := by
    intro h1
    have : y₀ = 0 := by rw [hy₀, h1]; simp
    rw [this, abs_zero] at hy0; exact lt_irrefl _ hy0
  refine ⟨hz, hw1', ?_⟩
  have hb := hloc η₂ y₀ hη₂0 hη₂8 hy₀1 hfree' σ hw1 hw2
  rw [← hw] at hb
  -- sizes
  have hy₀hi : |y₀| ≤ P ^ 5 := by
    have : |y₀| ≤ |t| + Lw := by
      have := abs_sub_abs_le_abs_sub y₀ t; linarith
    have hP4 : P ^ 4 + P ≤ P ^ 5 := by
      have : P ≤ P ^ 4 := by
        calc P = P ^ 1 := (pow_one P).symm
          _ ≤ P ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have : 2 * P ^ 4 ≤ P ^ 5 := by
        calc 2 * P ^ 4 ≤ P * P ^ 4 := by
              apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = P ^ 5 := by ring
      linarith
    linarith
  have hly : Real.log |y₀| ≤ 5 * ℓ := by
    calc Real.log |y₀| ≤ Real.log (P ^ 5) := Real.log_le_log hy0 hy₀hi
      _ = 5 * ℓ := by rw [Real.log_pow, hℓ]; push_cast; ring
  have hly1 : 1 ≤ Real.log |y₀| := by
    rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9; linarith
  have hlly : Real.log (Real.log |y₀|) ≤ 5 * ℓ := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log |y₀| by linarith)
    linarith
  have hlly0 : 0 ≤ Real.log (Real.log |y₀|) := Real.log_nonneg hly1
  have hlη : Real.log (1 / η₂) ≤ ℓ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / η₂ by positivity)
    linarith
  have hlη0 : 0 ≤ Real.log (1 / η₂) := Real.log_nonneg (by rw [le_div_iff₀ hη₂0]; linarith)
  set X := Real.log (Real.log |y₀|) + Real.log (1 / η₂) + 1 with hX
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hXη : X / η₂ ≤ X * ℓ := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinvη hX0
  have hXℓ : X ≤ 7 * ℓ := by rw [hX]; linarith
  have hzLD : ‖zLD w‖ ≤ 12 * K₁ * ℓ ^ 2 := by
    calc ‖zLD w‖ ≤ K₁ * (Real.log |y₀| + X / η₂) := hb
      _ ≤ K₁ * (5 * ℓ + X * ℓ) := by gcongr
      _ ≤ K₁ * (5 * ℓ * ℓ + 7 * ℓ * ℓ) := by
          apply mul_le_mul_of_nonneg_left _ hK₁
          have : X * ℓ ≤ 7 * ℓ * ℓ := mul_le_mul_of_nonneg_right hXℓ hℓ0.le
          nlinarith
      _ = 12 * K₁ * ℓ ^ 2 := by ring
  have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
    have him1 : |y₀| ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      have e : (w - 1).im = y₀ := by simp [hy₀]
      rwa [e] at this
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  have e : zetaH w = zLD w + 1 / (w - 1) := rfl
  rw [e]
  calc ‖zLD w + 1 / (w - 1)‖ ≤ ‖zLD w‖ + ‖1 / (w - 1)‖ := norm_add_le _ _
    _ ≤ 12 * K₁ * ℓ ^ 2 + 1 := add_le_add hzLD hinv

/-- The contour integrand `G(s) = F(s) P^s H(s + it)`. -/
noncomputable def zcG (f : ℝ → ℂ) (P t : ℝ) (s : ℂ) : ℂ :=
  mellin f s * (P : ℂ) ^ s * zetaH (s + t * I)

lemma zcG_differentiableAt {f : ℝ → ℂ} (hFd : Differentiable ℂ (mellin f)) {P t : ℝ}
    (hP : 0 < P) {s : ℂ} (h1 : s + t * I ≠ 1) (hz : riemannZeta (s + t * I) ≠ 0) :
    DifferentiableAt ℂ (zcG f P t) s :=
  ((hFd s).mul ((differentiableAt_id).const_cpow (Or.inl (by exact_mod_cast hP.ne')))).mul
    ((zetaH_differentiableAt h1 hz).comp s (differentiableAt_id.add_const _))

lemma zcG_right {f : ℝ → ℂ} (hFd : Differentiable ℂ (mellin f)) {P t : ℝ} (hP : 0 < P)
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (zcG f P t) s := by
  have hre : (s + t * I).re = s.re := by simp
  refine zcG_differentiableAt hFd hP (fun h => ?_) (riemannZeta_ne_zero_of_one_lt_re (by linarith))
  have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith

lemma zcG_norm {f : ℝ → ℂ} {P t : ℝ} (hP : 0 < P) (s : ℂ) :
    ‖zcG f P t s‖ = ‖mellin f s‖ * P ^ s.re * ‖zetaH (s + t * I)‖ := by
  simp only [zcG, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hP]

lemma continuous_zcG_line {f : ℝ → ℂ} (hFd : Differentiable ℂ (mellin f)) {P t σ : ℝ}
    (hP : 0 < P) (hσ : 1 < σ) : Continuous fun y : ℝ => zcG f P t (σ + y * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  exact (zcG_right hFd hP (by simpa using hσ)).continuousAt.comp
    (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)

/-- `‖F(s)‖ (1 + y²) M ≤ K₃` whenever `M ≤ (1 + y²)²`. -/
lemma mellin_cube_le {f : ℝ → ℂ} {K₃ : ℝ}
    (hK₃ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖mellin f s‖ * (1 + s.im ^ 2) ^ 3 ≤ K₃)
    {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 2) {M : ℝ} (hM : M ≤ (1 + s.im ^ 2) ^ 2) :
    ‖mellin f s‖ * ((1 + s.im ^ 2) * M) ≤ K₃ := by
  have hF := norm_nonneg (mellin f s)
  have hy : 0 ≤ 1 + s.im ^ 2 := by positivity
  calc ‖mellin f s‖ * ((1 + s.im ^ 2) * M) ≤ ‖mellin f s‖ * ((1 + s.im ^ 2) * (1 + s.im ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM hy) hF
    _ = ‖mellin f s‖ * (1 + s.im ^ 2) ^ 3 := by ring
    _ ≤ K₃ := hK₃ s h1 h2

/-- **Piece 1: tails on `Re s = 2`** beyond `|y| = P`. -/
lemma zc_tail {f : ℝ → ℂ} (hFd : Differentiable ℂ (mellin f)) {K₃ H₂ : ℝ} (hK₃0 : 0 ≤ K₃)
    (hK₃ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖mellin f s‖ * (1 + s.im ^ 2) ^ 3 ≤ K₃)
    (hH₂ : ∀ w : ℂ, w.re = 2 → ‖zetaH w‖ ≤ H₂) {P t : ℝ} (hP : 1 ≤ P) :
    Integrable (fun y : ℝ => zcG f P t (2 + y * I)) ∧
      ‖∫ y in (Set.Ioc (-P) P)ᶜ, zcG f P t (2 + y * I)‖ ≤ K₃ * |H₂| * π := by
  have hP0 : 0 < P := by linarith
  have hc : Continuous fun y : ℝ => zcG f P t (2 + y * I) := by
    have := continuous_zcG_line hFd hP0 (t := t) (σ := 2) (by norm_num)
    simpa using this
  have hpt : ∀ y : ℝ, ‖zcG f P t (2 + y * I)‖ ≤ K₃ * P ^ 2 * |H₂| * (1 + y ^ 2)⁻¹ := by
    intro y
    rw [zcG_norm hP0]
    have hre : (2 + (y : ℂ) * I).re = 2 := by simp
    have him : (2 + (y : ℂ) * I).im = y := by simp
    rw [hre, show P ^ (2 : ℝ) = P ^ 2 by norm_cast]
    have hF := mellin_cube_le hK₃ (s := 2 + y * I) (by rw [hre]; norm_num) (by rw [hre])
      (M := 1) (by rw [him]; nlinarith [sq_nonneg y])
    rw [him, mul_one] at hF
    have hH := (hH₂ (2 + y * I + t * I) (by simp)).trans (le_abs_self H₂)
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ‖mellin f (2 + y * I)‖ * P ^ 2 * ‖zetaH (2 + y * I + t * I)‖ * (1 + y ^ 2)
        = (‖mellin f (2 + y * I)‖ * (1 + y ^ 2)) * P ^ 2 * ‖zetaH (2 + y * I + t * I)‖ := by ring
      _ ≤ K₃ * P ^ 2 * |H₂| := by gcongr
  refine ⟨(integrable_inv_one_add_sq.const_mul _).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [mul_comm] using hpt y), ?_⟩
  have htail : ∀ y ∈ (Set.Ioc (-P) P)ᶜ, ‖zcG f P t (2 + y * I)‖ ≤ K₃ * |H₂| * (1 + y ^ 2)⁻¹ := by
    intro y hy
    have hyP : P ≤ |y| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [zcG_norm hP0]
    have hre : (2 + (y : ℂ) * I).re = 2 := by simp
    have him : (2 + (y : ℂ) * I).im = y := by simp
    rw [hre, show P ^ (2 : ℝ) = P ^ 2 by norm_cast]
    have hP2 : P ^ 2 ≤ (1 + y ^ 2) ^ 2 := by
      have : P ≤ 1 + y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
      exact pow_le_pow_left₀ hP0.le this 2
    have hF := mellin_cube_le hK₃ (s := 2 + y * I) (by rw [hre]; norm_num) (by rw [hre])
      (M := P ^ 2) (by rw [him]; exact hP2)
    rw [him] at hF
    have hH := (hH₂ (2 + y * I + t * I) (by simp)).trans (le_abs_self H₂)
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ‖mellin f (2 + y * I)‖ * P ^ 2 * ‖zetaH (2 + y * I + t * I)‖ * (1 + y ^ 2)
        = (‖mellin f (2 + y * I)‖ * ((1 + y ^ 2) * P ^ 2)) * ‖zetaH (2 + y * I + t * I)‖ := by
          ring
      _ ≤ K₃ * |H₂| := by gcongr
  calc ‖∫ y in (Set.Ioc (-P) P)ᶜ, zcG f P t (2 + y * I)‖
      ≤ ∫ y in (Set.Ioc (-P) P)ᶜ, K₃ * |H₂| * (1 + y ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _).integrableOn
          ((ae_restrict_iff' measurableSet_Ioc.compl).2 (Eventually.of_forall htail))
    _ ≤ ∫ y, K₃ * |H₂| * (1 + y ^ 2)⁻¹ :=
        setIntegral_le_integral (integrable_inv_one_add_sq.const_mul _)
          (Eventually.of_forall fun y => by positivity)
    _ = K₃ * |H₂| * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

end LeanFormalizations.Erdos385

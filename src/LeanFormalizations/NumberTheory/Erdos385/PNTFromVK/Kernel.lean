/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.PNTFromVK.Line

/-!
# Phase E3e helper: the log-scaled plateau weight

`wt A B η x = step((log x − log A)/η) − step((log x − log B)/η)` for `x > 0`, where `step` is a
smooth step from `0` (at `−1`) to `1` (at `1`).  It is `1` on `[A e^η, B e^{−η}]`, vanishes off
`[A e^{−η}, B e^η]`, and takes values in `[0, 1]`.

Its Mellin transform is exact: `x · wt'(x) = (ρ(·/A) − ρ(·/B))/η` with `ρ = step'`, and
`x ↦ ρ(log(x/A)/η)/η` has Mellin transform `A^s · mellin φ (η s)` for the FIXED function
`φ(y) = ρ(log y)` (`mellin_comp_rpow`, `mellin_comp_mul_left`).  So
`mellin wt s = (B^s − A^s) · mellin φ (η s) / s`, and the decay of `mellin φ` on a fixed strip
(`mellin_strip_decay`) is uniform in `η`: the uniformity a smooth-sandwich PNT needs.
-/

open Real Filter MeasureTheory Complex
open scoped ContDiff

namespace LeanFormalizations.Erdos385.PNTVK

open LeanFormalizations.Erdos385

/-- Smooth step: `0` for `v ≤ −1`, `1` for `v ≥ 1`, monotone. -/
noncomputable def step (v : ℝ) : ℝ := Real.smoothTransition ((v + 1) / 2)

/-- Its derivative, supported in `[−1, 1]`. -/
noncomputable def rho : ℝ → ℝ := deriv step

/-- The fixed profile `φ(y) = ρ(log y)` (`y > 0`). -/
noncomputable def phi (y : ℝ) : ℂ := if 0 < y then (rho (Real.log y) : ℂ) else 0

/-- The plateau weight, real form. -/
noncomputable def wr (A B η : ℝ) (x : ℝ) : ℝ :=
  if 0 < x then step ((Real.log x - Real.log A) / η) - step ((Real.log x - Real.log B) / η) else 0

/-- The plateau weight. -/
noncomputable def wt (A B η : ℝ) (x : ℝ) : ℂ := (wr A B η x : ℂ)

theorem step_contDiff : ContDiff ℝ ∞ step :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem step_zero {v : ℝ} (hv : v ≤ -1) : step v = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem step_one {v : ℝ} (hv : 1 ≤ v) : step v = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem step_mono : Monotone step := fun u v h =>
  Real.smoothTransition.monotone (by linarith)

theorem step_nonneg (v : ℝ) : 0 ≤ step v := Real.smoothTransition.nonneg _

theorem step_le_one (v : ℝ) : step v ≤ 1 := Real.smoothTransition.le_one _

theorem rho_contDiff : ContDiff ℝ ∞ rho := by
  unfold rho
  exact (contDiff_infty_iff_deriv.1 step_contDiff).2

theorem hasDerivAt_step (v : ℝ) : HasDerivAt step (rho v) v :=
  ((step_contDiff.differentiable (by simp)) v).hasDerivAt

theorem rho_zero {v : ℝ} (hv : 1 < |v|) : rho v = 0 := by
  unfold rho
  rcases lt_abs.1 hv with h | h
  · have : step =ᶠ[nhds v] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h] with u hu using step_one (le_of_lt hu)
    rw [this.deriv_eq]; simp
  · have : step =ᶠ[nhds v] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show v < -1 by linarith)] with u hu using step_zero (le_of_lt hu)
    rw [this.deriv_eq]; simp

/-- Gluing: smooth on `(0, ∞)` and zero on `(−∞, δ)` gives smooth on `ℝ`. -/
theorem contDiff_glue {F g : ℝ → ℂ} {δ : ℝ} {k : ℕ} (hδ : 0 < δ)
    (hg : ∀ y, 0 < y → ContDiffAt ℝ k g y) (hFg : ∀ y, 0 < y → F y = g y)
    (hF0 : ∀ y, y < δ → F y = 0) : ContDiff ℝ k F := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  rcases lt_or_ge y δ with h | h
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with u hu using hF0 u hu
  · refine (hg y (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show 0 < y by linarith)] with u hu using hFg u hu

theorem phi_contDiff (k : ℕ) : ContDiff ℝ k phi := by
  refine contDiff_glue (g := fun y => (rho (Real.log y) : ℂ)) (δ := Real.exp (-1)) (Real.exp_pos _)
    (fun y hy => ?_) (fun y hy => by simp [phi, hy]) (fun y hy => ?_)
  · exact ofRealCLM.contDiff.contDiffAt.comp y
      ((rho_contDiff.of_le (by exact_mod_cast le_top)).contDiffAt.comp y (Real.contDiffAt_log.2 hy.ne'))
  · unfold phi
    split_ifs with h0
    · have : Real.log y < -1 := by
        rw [Real.log_lt_iff_lt_exp h0]; exact hy
      rw [rho_zero (by rw [abs_of_neg (by linarith)]; linarith)]; simp
    · rfl

theorem phi_support {y : ℝ} (h : phi y ≠ 0) : Real.exp (-1) ≤ y ∧ y ≤ Real.exp 1 := by
  unfold phi at h
  split_ifs at h with h0
  · by_contra hc
    apply h
    rw [rho_zero]; · simp
    rcases not_and_or.1 hc with h1 | h1
    · have : Real.log y < -1 := by rw [Real.log_lt_iff_lt_exp h0]; linarith
      rw [abs_of_neg (by linarith)]; linarith
    · have : 1 < Real.log y := by rw [Real.lt_log_iff_exp_lt h0]; linarith
      rw [abs_of_pos (by linarith)]; exact this
  · exact absurd rfl h

theorem wr_zero_left {A B η x : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hη : 0 < η)
    (hx : x < A * Real.exp (-η)) : wr A B η x = 0 := by
  unfold wr
  split_ifs with h0
  · have h1 : Real.log x < Real.log A - η := by
      rw [Real.log_lt_iff_lt_exp h0, Real.exp_sub, Real.exp_log hA, div_eq_mul_inv, ← Real.exp_neg]
      exact hx
    have h2 : Real.log A ≤ Real.log B := Real.log_le_log hA hAB
    rw [step_zero, step_zero]; · simp
    · rw [div_le_iff₀ hη]; linarith
    · rw [div_le_iff₀ hη]; linarith
  · rfl

theorem wr_zero_right {A B η x : ℝ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) (hη : 0 < η)
    (hx : B * Real.exp η < x) : wr A B η x = 0 := by
  have h0 : 0 < x := lt_trans (by positivity) hx
  unfold wr
  rw [if_pos h0]
  have h1 : Real.log B + η < Real.log x := by
    rw [Real.lt_log_iff_exp_lt h0, Real.exp_add, Real.exp_log hB]; exact hx
  have h2 : Real.log A ≤ Real.log B := Real.log_le_log hA hAB
  rw [step_one, step_one]; · simp
  · rw [le_div_iff₀ hη]; linarith
  · rw [le_div_iff₀ hη]; linarith

theorem wt_contDiff {A B η : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hη : 0 < η) (k : ℕ) :
    ContDiff ℝ k (wt A B η) := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  refine contDiff_glue (g := fun x => ((step ((Real.log x - Real.log A) / η) -
      step ((Real.log x - Real.log B) / η) : ℝ) : ℂ)) (δ := A * Real.exp (-η)) (by positivity)
    (fun y hy => ?_) (fun y hy => by simp [wt, wr, hy])
    (fun y hy => by simp [wt, wr_zero_left hA hAB hη hy])
  have hl : ContDiffAt ℝ k Real.log y := Real.contDiffAt_log.2 hy.ne'
  have hs : ContDiff ℝ k step := step_contDiff.of_le (by exact_mod_cast le_top)
  refine ofRealCLM.contDiff.contDiffAt.comp y (ContDiffAt.sub ?_ ?_)
  · exact hs.contDiffAt.comp y ((hl.sub contDiffAt_const).div_const _)
  · exact hs.contDiffAt.comp y ((hl.sub contDiffAt_const).div_const _)

theorem wt_support {A B η : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hη : 0 < η) {x : ℝ}
    (h : wt A B η x ≠ 0) : A * Real.exp (-η) ≤ x ∧ x ≤ B * Real.exp η := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  by_contra hc
  apply h
  rcases not_and_or.1 hc with h1 | h1
  · simp [wt, wr_zero_left hA hAB hη (not_le.1 h1)]
  · simp [wt, wr_zero_right hA hB hAB hη (not_le.1 h1)]

/-- `wr` is in `[0, 1]` and `1` on the plateau. -/
theorem wr_bounds {A B η : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hη : 0 < η) (x : ℝ) :
    0 ≤ wr A B η x ∧ wr A B η x ≤ 1 ∧
      (A * Real.exp η ≤ x → x ≤ B * Real.exp (-η) → wr A B η x = 1) := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have h2 : Real.log A ≤ Real.log B := Real.log_le_log hA hAB
  unfold wr
  split_ifs with h0
  · refine ⟨sub_nonneg.2 (step_mono (div_le_div_of_nonneg_right (by linarith) hη.le)),
      by linarith [step_le_one ((Real.log x - Real.log A) / η),
        step_nonneg ((Real.log x - Real.log B) / η)], fun h1 h3 => ?_⟩
    have e1 : Real.log A + η ≤ Real.log x := by
      rw [← Real.log_exp η, ← Real.log_mul hA.ne' (Real.exp_pos _).ne']
      exact Real.log_le_log (by positivity) h1
    have e2 : Real.log x ≤ Real.log B - η := by
      rw [← Real.log_exp η, ← Real.log_div hB.ne' (Real.exp_pos _).ne', div_eq_mul_inv, ← Real.exp_neg]
      exact Real.log_le_log h0 h3
    rw [step_one, step_zero]; · ring
    · rw [div_le_iff₀ hη]; linarith
    · rw [le_div_iff₀ hη]; linarith
  · refine ⟨le_rfl, zero_le_one, fun h1 _ => absurd (lt_of_lt_of_le (by positivity) h1) h0⟩

/-- Mellin convergence for a function continuous on `[a, b] ⊂ (0, ∞)` and zero elsewhere on `(0, ∞)`. -/
theorem mellinConvergent_of_Icc {f : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (hf : ContinuousOn f (Set.Icc a b))
    (hs : ∀ x, 0 < x → f x ≠ 0 → a ≤ x ∧ x ≤ b) (s : ℂ) : MellinConvergent f s := by
  unfold MellinConvergent
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Set.Icc a b) := by
    intro u hu
    exact ((continuousAt_ofReal_cpow_const u _ (Or.inr (by linarith [hu.1]))).continuousWithinAt).smul
      (hf u hu)
  refine (hcont.integrableOn_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi fun u hu => ?_
  have : f u = 0 := by by_contra h; exact hu.2 (hs u hu.1 h)
  simp [this]

/-- The scaled profile `q(y) = φ(y^{1/η})/η`; for `x > 0`, `q(x/A) = ρ((log x − log A)/η)/η`. -/
noncomputable def qfun (η : ℝ) (y : ℝ) : ℂ := phi (y ^ (1 / η)) / η

theorem qfun_eq {A η x : ℝ} (hA : 0 < A) (hη : 0 < η) (hx : 0 < x) :
    qfun η (A⁻¹ * x) = ((rho ((Real.log x - Real.log A) / η) / η : ℝ) : ℂ) := by
  have h1 : 0 < A⁻¹ * x := by positivity
  have h2 : 0 < (A⁻¹ * x) ^ (1 / η) := Real.rpow_pos_of_pos h1 _
  unfold qfun phi
  rw [if_pos h2, Real.log_rpow h1, Real.log_mul (inv_pos.2 hA).ne' hx.ne', Real.log_inv]
  push_cast
  congr 2
  ring

theorem mellin_qfun {A η : ℝ} (hA : 0 < A) (hη : 0 < η) (s : ℂ) :
    mellin (fun t => qfun η (A⁻¹ * t)) s = (A : ℂ) ^ s * mellin phi (η * s) := by
  rw [mellin_comp_mul_left (qfun η) s (inv_pos.2 hA)]
  have hq : mellin (qfun η) s = mellin phi (η * s) := by
    unfold qfun
    rw [mellin_div_const, mellin_comp_rpow, abs_of_pos (by positivity), inv_div, div_one]
    rw [Complex.real_smul]
    have : s / ((1 / η : ℝ) : ℂ) = (η : ℂ) * s := by
      push_cast; field_simp
    rw [this]
    have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    field_simp
  rw [hq, smul_eq_mul, Complex.ofReal_inv,
    inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hA.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg, inv_inv]

theorem qfun_support {A η x : ℝ} (hA : 0 < A) (hη : 0 < η) (hx : 0 < x)
    (h : qfun η (A⁻¹ * x) ≠ 0) : A * Real.exp (-η) ≤ x ∧ x ≤ A * Real.exp η := by
  rw [qfun_eq hA hη hx] at h
  have hr : rho ((Real.log x - Real.log A) / η) ≠ 0 := by
    intro h0; apply h; simp [h0]
  have hle : |(Real.log x - Real.log A) / η| ≤ 1 := by
    by_contra hc; exact hr (rho_zero (not_le.1 hc))
  rw [abs_le, le_div_iff₀ hη, div_le_iff₀ hη] at hle
  constructor
  · rw [← Real.exp_log hA, ← Real.exp_add, ← Real.exp_log hx]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [← Real.exp_log hA, ← Real.exp_add, ← Real.exp_log hx]
    exact Real.exp_le_exp.2 (by linarith)

theorem qfun_continuousOn {A η : ℝ} (hA : 0 < A) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => qfun η (A⁻¹ * t)) (Set.Icc a b) := by
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  apply ContinuousAt.continuousWithinAt
  unfold qfun
  refine ContinuousAt.div_const ?_ _
  refine (phi_contDiff 0).continuous.continuousAt.comp ?_
  exact (continuousAt_const.mul continuousAt_id).rpow_const (Or.inl (mul_pos (inv_pos.2 hA) hu0).ne')

theorem mellinConvergent_qfun {A η : ℝ} (hA : 0 < A) (hη : 0 < η) (s : ℂ) :
    MellinConvergent (fun t => qfun η (A⁻¹ * t)) s :=
  mellinConvergent_of_Icc (by positivity) (qfun_continuousOn hA (by positivity))
    (fun x hx h => qfun_support hA hη hx h) s

theorem xDeriv_wt {A B η x : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hη : 0 < η) (hx : 0 < x) :
    xDeriv (wt A B η) x = qfun η (A⁻¹ * x) - qfun η (B⁻¹ * x) := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  rw [qfun_eq hA hη hx, qfun_eq hB hη hx]
  set g : ℝ → ℝ := fun x => step ((Real.log x - Real.log A) / η) - step ((Real.log x - Real.log B) / η)
  have hg : HasDerivAt g (rho ((Real.log x - Real.log A) / η) * (x⁻¹ / η) -
      rho ((Real.log x - Real.log B) / η) * (x⁻¹ / η)) x := by
    have hl := Real.hasDerivAt_log hx.ne'
    exact ((hasDerivAt_step _).comp x ((hl.sub_const _).div_const η)).sub
      ((hasDerivAt_step _).comp x ((hl.sub_const _).div_const η))
  have heq : wt A B η =ᶠ[nhds x] fun x => ((g x : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    simp [wt, wr, g, show (0:ℝ) < u from hu]
  unfold xDeriv
  rw [heq.deriv_eq, hg.ofReal_comp.deriv]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

/-- **Exact Mellin transform.** -/
theorem mellin_wt {A B η : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hη : 0 < η) {s : ℂ} (hs : s ≠ 0) :
    mellin (wt A B η) s = ((B : ℂ) ^ s - (A : ℂ) ^ s) * mellin phi (η * s) / s := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hsupp : ∀ x, wt A B η x ≠ 0 → A * Real.exp (-η) ≤ x ∧ x ≤ B * Real.exp η :=
    fun x h => wt_support hA hAB hη h
  have hab : A * Real.exp (-η) ≤ B * Real.exp η :=
    mul_le_mul hAB (Real.exp_le_exp.2 (by linarith)) (by positivity) hB.le
  have hX := mellin_xDeriv (by exact_mod_cast wt_contDiff hA hAB hη 1) (by positivity) hab hsupp hs
  have hD : mellin (xDeriv (wt A B η)) s =
      mellin (fun t => qfun η (A⁻¹ * t)) s - mellin (fun t => qfun η (B⁻¹ * t)) s := by
    unfold mellin
    rw [← integral_sub (mellinConvergent_qfun hA hη s) (mellinConvergent_qfun hB hη s)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [smul_eq_mul]
    rw [xDeriv_wt hA hAB hη hx, mul_sub]
  rw [hD, mellin_qfun hA hη, mellin_qfun hB hη] at hX
  field_simp
  linear_combination hX

/-- **Main term**: `∫ wt` is squeezed between the plateau and the support lengths. -/
theorem mellin_wt_one {A B η : ℝ} (hA : 0 < A) (hAB : A * Real.exp η ≤ B * Real.exp (-η))
    (hη : 0 < η) :
    (mellin (wt A B η) 1).im = 0 ∧
      B * Real.exp (-η) - A * Real.exp η ≤ (mellin (wt A B η) 1).re ∧
      (mellin (wt A B η) 1).re ≤ B * Real.exp η - A * Real.exp (-η) := by
  have hB : 0 < B := by
    have : 0 < A * Real.exp η := by positivity
    have := lt_of_lt_of_le this hAB
    exact pos_of_mul_pos_left this (Real.exp_pos _).le
  have hAB' : A ≤ B := by
    have h1 : Real.exp (-η) ≤ Real.exp η := Real.exp_le_exp.2 (by linarith)
    by_contra hc
    have : B * Real.exp (-η) < A * Real.exp η :=
      mul_lt_mul (not_le.1 hc) h1 (Real.exp_pos _) hA.le
    linarith
  set a := A * Real.exp (-η)
  set b := B * Real.exp η
  set p := A * Real.exp η
  set q := B * Real.exp (-η)
  have ha : 0 < a := by positivity
  have hp : 0 < p := by positivity
  have hab : a ≤ b := mul_le_mul hAB' (Real.exp_le_exp.2 (by linarith)) (by positivity) hB.le
  have hwc : Continuous (wr A B η) := by
    have := Complex.continuous_re.comp (wt_contDiff hA hAB' hη 0).continuous
    simpa [Function.comp_def, wt] using this
  have hzero : ∀ x ∈ Set.Ioi (0 : ℝ) \ Set.Icc a b, wr A B η x = 0 := by
    intro x hx
    rcases not_and_or.1 hx.2 with h | h
    · exact wr_zero_left hA hAB' hη (not_le.1 h)
    · exact wr_zero_right hA hB hAB' hη (not_le.1 h)
  have hint : IntegrableOn (wr A B η) (Set.Ioi 0) :=
    (hwc.continuousOn.integrableOn_Icc (a := a) (b := b)).of_forall_diff_eq_zero measurableSet_Ioi hzero
  have hm : mellin (wt A B η) 1 = ((∫ x in Set.Ioi (0:ℝ), wr A B η x : ℝ) : ℂ) := by
    rw [mellin, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp [wt]
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  have hI : ∫ x in Set.Ioi (0:ℝ), wr A B η x = ∫ x in Set.Icc a b, wr A B η x :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hzero)
  rw [hm, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨rfl, ?_, ?_⟩
  · have hsub' : Set.Icc p q ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hp hx.1
    have h1 : ∫ x in Set.Icc p q, wr A B η x = ∫ x in Set.Icc p q, (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc fun x hx => (wr_bounds hA hAB' hη x).2.2 hx.1 hx.2
    have h2 : ∫ x in Set.Icc p q, wr A B η x ≤ ∫ x in Set.Ioi (0:ℝ), wr A B η x :=
      setIntegral_mono_set hint
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x _ =>
          (wr_bounds hA hAB' hη x).1)) hsub'.eventuallyLE
    rw [h1, setIntegral_const, Real.volume_real_Icc_of_le hAB, smul_eq_mul, mul_one] at h2
    exact h2
  · rw [hI]
    have h2 : ∫ x in Set.Icc a b, wr A B η x ≤ ∫ x in Set.Icc a b, (1 : ℝ) :=
      setIntegral_mono_on (hwc.continuousOn.integrableOn_Icc) (by simp) measurableSet_Icc
        fun x _ => (wr_bounds hA hAB' hη x).2.1
    rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul, mul_one] at h2
    exact h2

end LeanFormalizations.Erdos385.PNTVK

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll

/-!
# Phase E3e helper: the Perron identity on a vertical line `Re s = c`, `1 < c ≤ 2`

`AlmostAll.lean` proves `smoothTwist_sub_main_eq_line` on `Re s = 2`; the tail of that integral costs
`P²`, which is too much for the PNT.  These are the same proofs with `2` replaced by `c`.
-/

open Real Filter MeasureTheory Complex

namespace LeanFormalizations.Erdos385.PNTVK

open LeanFormalizations.Erdos385

/-- `H` is bounded on the line `Re w = 2`. -/
theorem zetaH_bound_line {c : ℝ} (hc : 1 < c) : ∃ B : ℝ, ∀ w : ℂ, w.re = c → ‖zetaH w‖ ≤ B := by
  have hs2 : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) c :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  set B0 := ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) c n‖
  refine ⟨B0 + 1 / (c - 1), fun w hw => ?_⟩
  have hw1 : 1 < w.re := by rw [hw]; exact hc
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw1
  have hterm : ∀ n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w n‖ =
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) c n‖ := by
    intro n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hw]; simp
  have hsum : Summable fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) c n‖ :=
    summable_norm_iff.mpr hs2
  have hLb : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w‖ ≤ B0 := by
    rw [LSeries]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hterm))
    exact hsum.congr fun n => (hterm n).symm
  have hinv : ‖1 / (w - 1)‖ ≤ 1 / (c - 1) := by
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le (by linarith)
    have := Complex.abs_re_le_norm (w - 1)
    simp only [sub_re, one_re, hw] at this
    rw [abs_of_pos (by linarith)] at this; exact this
  unfold zetaH
  have : deriv riemannZeta w / riemannZeta w =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w := by
    rw [hL]; ring
  rw [this]
  calc ‖-LSeries _ w + 1 / (w - 1)‖ ≤ ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w‖ +
        ‖1 / (w - 1)‖ := by rw [← norm_neg (LSeries _ w)]; exact norm_add_le _ _
    _ ≤ B0 + 1 / (c - 1) := add_le_add hLb hinv

/-- `y ↦ mellin f (2 + iy)` is continuous, integrable, and `≤ K/(1+y²)`. -/
theorem mellin_vertical_facts_line {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ y : ℝ, ‖mellin f (c + y * I)‖ ≤ K * (1 + y ^ 2)⁻¹) ∧
      Continuous (fun y : ℝ => mellin f (c + y * I)) ∧
      Integrable (fun y : ℝ => mellin f (c + y * I)) := by
  obtain ⟨K, hK0, hK⟩ := mellin_pointwise hf ha hab hs
  have hb : ∀ y : ℝ, ‖mellin f (c + y * I)‖ ≤ K * (1 + y ^ 2)⁻¹ := by
    intro y
    have := (hK (c + y * I) (by simp; linarith) (by simpa using hc2)).1
    simpa using this
  have hcont : Continuous (fun y : ℝ => mellin f (c + y * I)) :=
    (mellin_differentiable (hf 0).continuous ha hs).continuous.comp (by fun_prop)
  exact ⟨K, hK0, hb, hcont, (integrable_inv_one_add_sq.const_mul K).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall hb)⟩

/-- **Mellin inversion on `Re s = 2`.** -/
theorem mellin_inversion_line {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) {x : ℝ} (hx : 0 < x) :
    f x = ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, (x : ℂ) ^ (-(c + y * I)) * mellin f (c + y * I) := by
  obtain ⟨K, -, -, -, hint⟩ := mellin_vertical_facts_line hc hc2 hf ha hab hs
  have hconv : MellinConvergent f (c : ℝ) := by
    unfold MellinConvergent
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (((c : ℝ) : ℂ) - 1) • f t) (Set.Icc a b) := by
      intro u hu
      apply ContinuousAt.continuousWithinAt
      exact (continuousAt_ofReal_cpow_const u _ (Or.inr (by linarith [hu.1]))).smul
        (hf 0).continuous.continuousAt
    refine (hcont.integrableOn_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi fun u hu => ?_
    have : f u = 0 := by by_contra h; exact hu.2 (hs u h)
    simp [this]
  have hvert : VerticalIntegrable (mellin f) (c : ℝ) := by
    unfold VerticalIntegrable; push_cast; exact hint
  have := mellinInv_mellin_eq (c : ℝ) f hx hconv hvert (hf 0).continuous.continuousAt
  rw [← this, mellinInv]
  push_cast
  simp only [smul_eq_mul]
  rw [Complex.real_smul]; push_cast; ring

/-- **V4, main-term half.**  If `f(x/P) = 0` for `x < 1`, then
`F(1 − it) P^{1−it} = (1/2π) ∫ F(2+iy) P^{2+iy} / (2+iy+it−1) dy`. -/
theorem mainTerm_eq_vertical_line {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) {P : ℝ} (hP : 1 ≤ a * P) (t : ℝ) :
    mellin f (1 - t * I) * (P : ℂ) ^ (1 - t * I) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) /
        (c + y * I + t * I - 1) := by
  obtain ⟨K, hK0, hKb, hKc, hKi⟩ := mellin_vertical_facts_line hc hc2 hf ha hab hs
  have hP0 : 0 < P := by
    by_contra h; push Not at h; nlinarith
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
  set κ : ℂ := ((1 / (2 * π) : ℝ) : ℂ)
  set s : ℝ → ℂ := fun y => c + y * I with hs_def
  set Φ : ℝ → ℝ → ℂ := fun x y => (x : ℂ) ^ (-(s y + t * I)) * (mellin f (s y) * (P : ℂ) ^ (s y))
    with hΦ
  -- Claim 1: inversion inside the `x`-integral
  have hc1 : ∀ x : ℝ, 0 < x → (x : ℂ) ^ (-(t * I)) * f (x / P) = κ * ∫ y, Φ x y := by
    intro x hx
    rw [mellin_inversion_line hc hc2 hf ha hab hs (div_pos hx hP0), ← mul_assoc, mul_comm _ κ, mul_assoc,
      ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    simp only [hΦ, hs_def]
    rw [show ((x / P : ℝ) : ℂ) = (x : ℂ) * ((P⁻¹ : ℝ) : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg hx.le (inv_nonneg.2 hP0.le), Complex.ofReal_inv,
      inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hP0.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg (P : ℂ), inv_inv,
      show -((c : ℂ) + y * I + t * I) = -(c + y * I) + -(t * I) by ring,
      Complex.cpow_add _ _ hx0]
    ring
  -- Claim 2: the inner `x`-integral
  have hc2 : ∀ y : ℝ, ∫ x in Set.Ioi (1 : ℝ), Φ x y =
      mellin f (s y) * (P : ℂ) ^ (s y) / (s y + t * I - 1) := by
    intro y
    simp only [hΦ]
    rw [integral_mul_const, integral_Ioi_cpow_of_lt (by simp [hs_def]; exact hc) one_pos]
    have hne : -(s y + t * I) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hne' : s y + t * I - 1 ≠ 0 := by
      intro h; apply hne; linear_combination -h
    rw [Complex.ofReal_one, Complex.one_cpow]
    field_simp
    ring
  -- Claim 3: Fubini
  have hint : Integrable (Function.uncurry Φ) ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume) := by
    have hbound : Integrable (fun z : ℝ × ℝ => z.1 ^ (-c) * (K * P ^ c * (1 + z.2 ^ 2)⁻¹))
        ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume) :=
      Integrable.mul_prod (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
        (integrable_inv_one_add_sq.const_mul _)
    have hm : Measurable fun y : ℝ => mellin f (c + y * I) := hKc.measurable
    have hmeas : Measurable (Function.uncurry Φ) := by
      show Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (-((c : ℂ) + (z.2 : ℂ) * I + t * I)) *
        (mellin f (c + z.2 * I) * (P : ℂ) ^ ((c : ℂ) + (z.2 : ℂ) * I))
      refine Measurable.mul (Measurable.pow (measurable_ofReal.comp measurable_fst) ?_)
        ((hm.comp measurable_snd).mul (Measurable.pow measurable_const ?_)) <;> fun_prop
    refine hbound.mono' hmeas.aestronglyMeasurable ?_
    · rw [Measure.ae_prod_iff_ae_ae]
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
        refine Eventually.of_forall fun y => ?_
        have hx0 : 0 < x := by linarith [show (1:ℝ) < x from hx]
        simp only [Function.uncurry, hΦ, hs_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
          Complex.norm_cpow_eq_rpow_re_of_pos hP0]
        have hre1 : (-((c:ℂ) + y * I + t * I)).re = -c := by simp
        have hre2 : ((c:ℂ) + y * I).re = c := by simp
        rw [hre1, hre2]
        have := hKb y
        have h0 : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx0.le _
        have h1 : 0 ≤ P ^ c := Real.rpow_nonneg hP0.le _
        calc x ^ (-c) * (‖mellin f (c + y * I)‖ * P ^ c)
            ≤ x ^ (-c) * (K * (1 + y ^ 2)⁻¹ * P ^ c) := by gcongr
          _ = _ := by ring
      · exact measurableSet_le hmeas.norm (by fun_prop)
  -- Claim 4: the left side as an `x`-integral over `(1, ∞)`
  have hPinv : ((P⁻¹ : ℝ) : ℂ) ^ (-(1 - t * I)) = (P : ℂ) ^ (1 - t * I) := by
    rw [Complex.ofReal_inv, inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hP0.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg, inv_inv]
  have hL : mellin f (1 - t * I) * (P : ℂ) ^ (1 - t * I) =
      ∫ x in Set.Ioi (1 : ℝ), (x : ℂ) ^ (-(t * I)) * f (x / P) := by
    have h1 := mellin_comp_mul_left f (1 - t * I) (inv_pos.2 hP0)
    rw [hPinv, smul_eq_mul] at h1
    rw [mul_comm, ← h1, mellin]
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      (fun x (hx : (1:ℝ) < x) => show (0:ℝ) < x by linarith)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [smul_eq_mul]
      rw [show 1 - (t : ℂ) * I - 1 = -(t * I) by ring, div_eq_inv_mul]
    · have : ∀ᵐ x : ℝ, x ≠ 1 := by rw [ae_iff]; simp
      filter_upwards [this] with x hx1 hx
      have hx' : x < 1 := lt_of_le_of_ne (not_lt.1 hx.2) hx1
      have : f (P⁻¹ * x) = 0 := by
        by_contra h
        have := (hs _ h).1
        have : a * P ≤ x := by
          calc a * P ≤ P⁻¹ * x * P := mul_le_mul_of_nonneg_right this hP0.le
            _ = x := by field_simp
        linarith
      simp [this]
  rw [hL, setIntegral_congr_fun measurableSet_Ioi (fun x hx => hc1 x (by
      linarith [show (1:ℝ) < x from hx])), integral_const_mul, integral_integral_swap hint]
  congr 1
  exact integral_congr_ae (Eventually.of_forall hc2)

/-- Mellin inversion at `x/P`, twisted by `x^{−it}`. -/
theorem twist_inversion_line {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) {P : ℝ} (hP0 : 0 < P) (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    (x : ℂ) ^ (-(t * I)) * f (x / P) = ((1 / (2 * π) : ℝ) : ℂ) *
      ∫ y : ℝ, (x : ℂ) ^ (-(c + y * I + t * I)) * (mellin f (c + y * I) * (P : ℂ) ^ (c + y * I)) := by
  rw [mellin_inversion_line hc hc2 hf ha hab hs (div_pos hx hP0), ← mul_assoc,
    mul_comm _ ((1 / (2 * π) : ℝ) : ℂ), mul_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  beta_reduce
  rw [show ((x / P : ℝ) : ℂ) = (x : ℂ) * ((P⁻¹ : ℝ) : ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg hx.le (inv_nonneg.2 hP0.le), Complex.ofReal_inv,
    inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hP0.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg (P : ℂ), inv_inv,
    show -((c : ℂ) + y * I + t * I) = -(c + y * I) + -(t * I) by ring,
    Complex.cpow_add _ _ hx0]
  ring

/-- **V4, prime-sum half.** `S = (1/2π) ∫ F(2+iy) P^{2+iy} L(Λ, 2+iy+it) dy`. -/
theorem smoothTwist_eq_vertical_line {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) {P : ℝ} (hP0 : 0 < P) (t : ℝ) :
    smoothTwist f P t = ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, mellin f (c + y * I) *
      (P : ℂ) ^ (c + y * I) * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (c + y * I + t * I) := by
  obtain ⟨K, hK0, hKb, hKc, hKi⟩ := mellin_vertical_facts_line hc hc2 hf ha hab hs
  set κ : ℂ := ((1 / (2 * π) : ℝ) : ℂ)
  set Λc : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) with hΛc
  set h : ℝ → ℂ := fun y => mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) with hh
  set G : ℕ → ℝ → ℂ := fun n y => LSeries.term Λc (c + y * I + t * I) n * h y with hG
  set an : ℕ → ℝ := fun n => ‖LSeries.term Λc c n‖ with han
  have hsum : Summable an :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
  have hterm : ∀ (n : ℕ) (y : ℝ), ‖LSeries.term Λc (c + y * I + t * I) n‖ = an n := by
    intro n y; simp only [han]; rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp
  have hhn : ∀ y, ‖h y‖ = ‖mellin f (c + y * I)‖ * P ^ c := by
    intro y
    simp only [hh, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hP0]
    simp
  have hhc : Continuous h := by
    refine hKc.mul (continuous_iff_continuousAt.2 fun y => ?_)
    exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousAt.const_cpow
      (Or.inl (by exact_mod_cast hP0.ne'))
  have hhi : Integrable h := by
    refine (hKi.norm.mul_const (P ^ c)).mono' hhc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [hhn]
  have hGm : ∀ n, Continuous (fun y : ℝ => LSeries.term Λc (c + y * I + t * I) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]; exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ fun y => ?_
      · exact continuous_iff_continuousAt.2 fun y =>
          (by fun_prop : Continuous fun y : ℝ => c + (y : ℂ) * I + t * I).continuousAt.const_cpow
            (Or.inl (by exact_mod_cast hn))
      · exact Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
          intro h0; have := congrArg Complex.re h0; simp at this; linarith) |>.2 (by exact_mod_cast hn)
  have hGi : ∀ n, Integrable (G n) := by
    intro n
    refine (hhi.norm.const_mul (an n)).mono' ((hGm n).mul hhc).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [hG, norm_mul, hterm]; rfl
  have hGn : ∀ n, ∫ y, ‖G n y‖ = an n * ∫ y, ‖h y‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1; ext y; simp only [hG, norm_mul, hterm]
  have hGs : Summable fun n => ∫ y, ‖G n y‖ := by
    simp only [hGn]; exact hsum.mul_right _
  -- per-`n` inversion
  have hper : ∀ n : ℕ, Λc n * (n : ℂ) ^ (-((t : ℂ) * I)) * f (n / P) = κ * ∫ y, G n y := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hΛc, hG]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have := twist_inversion_line hc hc2 hf ha hab hs hP0 t hn0
    rw [Complex.ofReal_natCast] at this
    rw [mul_assoc, this, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hG, LSeries.term_of_ne_zero hn, hh]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    ring
  have hL : ∀ y : ℝ, ∑' n, G n y = h y * LSeries Λc (c + y * I + t * I) := by
    intro y
    simp only [hG, LSeries]
    rw [tsum_mul_right, mul_comm]
  unfold smoothTwist
  rw [tsum_congr hper, tsum_mul_left, integral_tsum_of_summable_integral_norm hGi hGs]
  congr 1
  exact integral_congr_ae (Eventually.of_forall hL)

/-- **Crux leaf V4 (Perron at `Re s = 2`, main term subtracted).**  Once `f(x/P)` vanishes for
`x ≤ 1` (`a P ≥ 1`): `S − F(1 − it) P^{1−it} = −(1/2π) ∫ F(2+iy) P^{2+iy} H(2+iy+it) dy`.
English proof: Mellin inversion `mellinInv_mellin_eq` at `x = n/P`, Fubini against
`∑ Λ(n) n^{-2}` (absolutely convergent, `mellin_strip_decay` k = 2 for integrability),
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`; the main term is `∫_1^∞ x^{−it} f(x/P) dx`
(`mellin_comp_mul_left`) whose Mellin–Perron form is `∫ F(s) P^s/(s + it − 1)` since
`∫_1^∞ x^{−s−it} dx = 1/(s+it−1)`.  Confidence 95%. -/
theorem smoothTwist_sub_main_eq_line {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) {P : ℝ} (hP : 1 ≤ a * P) (t : ℝ) :
    smoothTwist f P t - mellin f (1 - t * I) * (P : ℂ) ^ (1 - t * I) =
      -((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) *
        zetaH (c + y * I + t * I) := by
  have hP0 : 0 < P := by
    by_contra h; push Not at h; nlinarith
  obtain ⟨K, hK0, hKb, hKc, hKi⟩ := mellin_vertical_facts_line hc hc2 hf ha hab hs
  obtain ⟨B, hB⟩ := zetaH_bound_line hc
  have hhn : ∀ y : ℝ, ‖mellin f (c + y * I) * (P : ℂ) ^ (c + y * I)‖ =
      ‖mellin f (c + y * I)‖ * P ^ c := by
    intro y
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hP0]
    simp
  have hhc : Continuous fun y : ℝ => mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) := by
    refine hKc.mul (continuous_iff_continuousAt.2 fun y => ?_)
    exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousAt.const_cpow
      (Or.inl (by exact_mod_cast hP0.ne'))
  have hhi : Integrable fun y : ℝ => mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) := by
    refine (hKi.norm.mul_const (P ^ c)).mono' hhc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [hhn]
  have hw1 : ∀ y : ℝ, 1 < (c + (y : ℂ) * I + t * I).re := fun y => by simpa using hc
  have hwne : ∀ y : ℝ, (c + (y : ℂ) * I + t * I) - 1 ≠ 0 := fun y h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hzc : Continuous fun y : ℝ => zetaH (c + y * I + t * I) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hw : (c + (y : ℂ) * I + t * I) ≠ 1 := fun h0 => hwne y (by rw [h0]; ring)
    have hz : riemannZeta (c + (y : ℂ) * I + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (hw1 y)
    exact (zetaH_differentiableAt hw hz).continuousAt.comp
      (f := fun y : ℝ => c + (y : ℂ) * I + t * I) (by fun_prop)
  have hzi : Integrable fun y : ℝ => mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) *
      zetaH (c + y * I + t * I) := by
    refine (hhi.norm.mul_const |B|).mono' (hhc.mul hzc).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hB _ (by simp)).trans (le_abs_self B)) (norm_nonneg _)
  have hdi : Integrable fun y : ℝ => mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) /
      (c + y * I + t * I - 1) := by
    refine (hhi.norm.const_mul (1 / (c - 1))).mono' (hhc.div (by fun_prop) hwne).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    · rw [norm_div, div_eq_mul_inv, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := Complex.abs_re_le_norm (c + (y : ℂ) * I + t * I - 1)
      have hre : (c + (y : ℂ) * I + t * I - 1).re = c - 1 := by simp
      rw [hre, abs_of_pos (by linarith)] at this
      rw [one_div]; exact inv_anti₀ (by linarith) this
  have hpt : ∀ y : ℝ, mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c + y * I + t * I) =
      mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) / (c + y * I + t * I - 1) -
        mellin f (c + y * I) * (P : ℂ) ^ (c + y * I) * zetaH (c + y * I + t * I) := by
    intro y
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hw1 y), zetaH]
    field_simp [hwne y]
    ring
  rw [smoothTwist_eq_vertical_line hc hc2 hf ha hab hs hP0 t, mainTerm_eq_vertical_line hc hc2 hf ha hab hs hP t,
    integral_congr_ae (Eventually.of_forall hpt), integral_sub hdi hzi]
  ring

end LeanFormalizations.Erdos385.PNTVK

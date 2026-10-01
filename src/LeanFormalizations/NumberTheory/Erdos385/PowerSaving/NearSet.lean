/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.NearFar
import LeanFormalizations.NumberTheory.Erdos385.MeanValue

/-!
# Erdős #385 power saving: `NearFarInput` from a pointwise near-set leaf (phase E9b)

`nearFarInput_of_nearSetLeaf`: `NearFarInput δ` follows from `NearSetLeaf δ`, which asks only for
a finite set `S` of heights whose unit neighbourhoods carry little `L¹` mass of `A(1+it)`, and off
which the short prime sum is pointwise small: `|P(1+it)| ≤ Z^{−η}` for `Z^{c₀} ≤ |t| ≤ 16X`.

Off the near set `|A|² = |P|²|Q|²/log² Z ≤ Z^{−2η}|Q|²`, and the MVT for `Q` (`primeQ_meanSquare`)
gives the mid band and every tail band with `T ≤ 8X`; for `T > 8X` the MVT for `A` itself
(`coeffC_meanSquare`) gives `X/(h₁T)·3T/Z ≪ 1/h₁ ≪ Z^{−1/2}`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex LeanFormalizations.Literature Erdos385.Parseval

/-- **The near-set leaf.**  Believed (65%), see `NearFarInput`'s docstring: `S` = a maximal
`1`-separated set of large values of `P` on `Z^{c₀}+1 ≤ |t| ≤ 16X`; the `L¹` bound from
`NearOneLargeValues` levels (applied to the per-interval sup points) + VK; the pointwise bound off
the unit neighbourhoods is immediate from maximality (every `t` with `|P| > Z^{−η}` is within `1`
of `S`), no derivative bound needed. -/
def NearSetLeaf (δ : ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ cmax : ℝ, 0 < cmax ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cmax → ∀ g : ℝ → ℝ,
    Admissible δ g → ∀ᶠ Z : ℝ in atTop, ∃ T₀ : ℝ, Z ^ c₀ / 2 ≤ T₀ ∧ T₀ ≤ Z ^ c₀ ∧
      ∃ S : Finset ℝ, (∀ s ∈ S, T₀ + 1 ≤ |s|) ∧
      (∫ t in nearSet S 1, ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖) ≤
        1 / Real.log Z ^ 3 ∧
      ∀ t : ℝ, T₀ ≤ |t| → |t| ≤ 16 * paramX δ Z → t ∉ nearSet S 1 →
        ‖primeP g Z (1 + t * I)‖ ≤ Z ^ (-η)

section
variable {δ Z : ℝ} {g : ℝ → ℝ}

lemma normA_sq_eq (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 1 < Z) (hg : Admissible δ g) (t : ℝ) :
    ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2 =
      ‖primeP g Z (1 + t * I)‖ ^ 2 * ‖primeQ δ Z (1 + t * I)‖ ^ 2 / Real.log Z ^ 2 := by
  rw [show (fun m ↦ (coeffA δ g Z m : ℂ)) = coeffC δ g Z from rfl,
    LSeries_coeffC_eq hδ hδ' hZ hg, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_pos hZ).le]
  ring

lemma continuous_normA_sq (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 1 < Z) (hg : Admissible δ g) :
    Continuous fun t : ℝ => ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2 := by
  simp_rw [normA_sq_eq hδ hδ' hZ hg]
  have := continuous_primeP g Z
  have := continuous_primeQ δ Z
  fun_prop

/-- Bound a set integral of a continuous nonnegative function by the interval integral. -/
lemma setIntegral_le_interval {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {M : Set ℝ} (hM : MeasurableSet M) {U : ℝ} (hU : 0 ≤ U) (hMU : M ⊆ Set.Icc (-U) U) :
    ∫ t in M, f t ≤ ∫ t in (-U)..U, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_mono_set (hf.continuousOn.integrableOn_compact isCompact_Icc)
    (Eventually.of_forall fun t => hf0 t) hMU.eventuallyLE

/-- Masked bound: on `M ⊆ [−U, U]` where `|P| ≤ ε`, `∫_M |A|² ≤ ε² ∫_{−U}^{U} |Q|²`. -/
lemma masked_le (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 1 < Z) (hg : Admissible δ g)
    (hlog : 1 ≤ Real.log Z) {M : Set ℝ} (hM : MeasurableSet M) {U : ℝ} (hU : 0 ≤ U)
    (hMU : M ⊆ Set.Icc (-U) U) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : ∀ t ∈ M, ‖primeP g Z (1 + t * I)‖ ≤ ε) :
    ∫ t in M, ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2 ≤
      ε ^ 2 * ∫ t in (-U)..U, ‖primeQ δ Z (1 + t * I)‖ ^ 2 := by
  have hQc : Continuous fun t : ℝ => ε ^ 2 * ‖primeQ δ Z (1 + t * I)‖ ^ 2 := by
    have := continuous_primeQ δ Z; fun_prop
  have hint : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f M := fun hf =>
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set hMU
  calc ∫ t in M, ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2
      ≤ ∫ t in M, ε ^ 2 * ‖primeQ δ Z (1 + t * I)‖ ^ 2 := by
        refine setIntegral_mono_on (hint (continuous_normA_sq hδ hδ' hZ hg)) (hint hQc) hM
          fun t ht => ?_
        rw [normA_sq_eq hδ hδ' hZ hg]
        have hl : 1 ≤ Real.log Z ^ 2 := one_le_pow₀ hlog
        have hp : ‖primeP g Z (1 + t * I)‖ ^ 2 ≤ ε ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hP t ht) 2
        calc _ ≤ ‖primeP g Z (1 + t * I)‖ ^ 2 * ‖primeQ δ Z (1 + t * I)‖ ^ 2 :=
              div_le_self (by positivity) hl
          _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ ∫ t in (-U)..U, ε ^ 2 * ‖primeQ δ Z (1 + t * I)‖ ^ 2 :=
        setIntegral_le_interval hQc (fun t => by positivity) hM hU hMU
    _ = _ := by rw [intervalIntegral.integral_const_mul]

end

lemma measurableSet_band (a b : ℝ) (S : Finset ℝ) :
    MeasurableSet ({t : ℝ | a ≤ |t| ∧ |t| ≤ b} \ nearSet S 1) :=
  ((measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)).diff (measurableSet_nearSet S 1)

lemma band_subset (a b : ℝ) (S : Finset ℝ) :
    {t : ℝ | a ≤ |t| ∧ |t| ≤ b} \ nearSet S 1 ⊆ Set.Icc (-b) b :=
  fun t ht => abs_le.1 ht.1.2

lemma tail_alg1 (X h T z K w : ℝ) (hh : h ≠ 0) (hT : T ≠ 0) (hw : w ≠ 0) :
    X / (h * T) * (z * (K * (3 * T) / w)) = 3 * K * z * (X / (h * w)) := by
  field_simp

lemma tail_alg2 (X h T K w : ℝ) (hh : h ≠ 0) (hT : T ≠ 0) (hw : w ≠ 0) :
    X / (h * T) * (K * (3 * T) / (w * w)) = 3 * K * (X / (h * w)) * (1 / w) := by
  field_simp

set_option maxHeartbeats 1600000 in
/-- **`NearFarInput` from the near-set leaf** (MVT for `Q` off the near set, MVT for `A` far out). -/
theorem nearFarInput_of_nearSetLeaf {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hL : NearSetLeaf δ) : NearFarInput δ := by
  obtain ⟨η, hη, m, hm, hL⟩ := hL
  have hMVT : MontgomeryVaughanMVT := ⟨32, Erdos385.MVT.mvt⟩
  obtain ⟨KQ, hKQ⟩ := primeQ_meanSquare hMVT hδ hδ'
  refine ⟨min m (1 / 12), lt_min hm (by norm_num), fun c₀ hc₀ hc₀m g hg => ?_⟩
  obtain ⟨KA, hKA⟩ := coeffC_meanSquare hMVT hδ hδ' hg
  obtain ⟨K, hK⟩ : ∃ K, K = |KQ| + |KA| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨min (2 * η) (1 / 2), 100 * K * (1 + 1 / δ), lt_min (by positivity) (by norm_num), ?_⟩
  filter_upwards [hL c₀ hc₀ (hc₀m.trans (min_le_left _ _)) g hg, hKQ, hKA,
    variance_params (κ := 1) hδ hδ' one_pos] with Z hS hQ hA hv
  obtain ⟨T₀, hT₀lo, hT₀hi, S, hSs, hnear, hP⟩ := hS
  clear hL hKQ hKA
  obtain ⟨hZ16, hlog, hX2, hH2, hH1lo, hH1hi, -⟩ := hv
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hZ16
  have hXlo : 7 / 8 * Z ≤ paramX δ Z := by rw [paramX]; nlinarith
  have hXhi : paramX δ Z ≤ Z := by rw [paramX]; nlinarith
  generalize paramX δ Z = X at *
  generalize paramH1 δ Z = h₁ at *
  have hh₁0 : 0 < h₁ := by linarith
  have hh₁s : h₁ ≤ √Z := by nlinarith
  have hε0 : 0 ≤ Z ^ (-η) := by positivity
  have hε2 : (Z ^ (-η)) ^ 2 = Z ^ (-(2 * η)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]; ring_nf
  generalize Z ^ (-η) = ε at *
  obtain ⟨c, hcdef⟩ : ∃ c, c = min (2 * η) (1 / 2) := ⟨_, rfl⟩
  rw [← hcdef]
  have hεc : ε ^ 2 ≤ Z ^ (-c) := by
    rw [hε2]; exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by simp [hcdef])
  have hsc : 1 / √Z ≤ Z ^ (-c) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by simp [hcdef])
  have hZc0 : 0 ≤ Z ^ (-c) := by positivity
  have hc₀s : T₀ ≤ √Z := by
    refine hT₀hi.trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le
      (by linarith [hc₀m.trans (min_le_right _ _)])
  -- `X/(h₁√Z) ≤ 16/δ`
  have hXh : X / (h₁ * √Z) ≤ 16 / δ := by
    rw [div_le_div_iff₀ (by positivity) hδ]
    have : δ * Z / 16 ≤ h₁ * √Z := by
      have := mul_le_mul_of_nonneg_right hH1lo hsZ.le
      calc δ * Z / 16 = δ * √Z / 16 * √Z := by linear_combination (-δ / 16) * hZsq
        _ ≤ _ := this
    nlinarith
  have h16 : (1 + 1 / δ) * 16 ≤ 16 + 16 / δ := by
    rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul]
  have hδinv : 0 ≤ 1 / δ := by positivity
  refine ⟨T₀, hT₀lo, hT₀hi, S, hSs, hnear, ?_, fun T hT => ?_⟩
  · -- mid band
    obtain ⟨U, hUdef⟩ : ∃ U, U = X / h₁ := ⟨_, rfl⟩
    rw [← hUdef]
    have hU1 : 1 ≤ U := by rw [hUdef, le_div_iff₀ hh₁0]; nlinarith
    have hU : U ≤ 16 * √Z / δ := by
      have : U = X / (h₁ * √Z) * √Z := by rw [hUdef]; field_simp
      rw [this]
      calc X / (h₁ * √Z) * √Z ≤ 16 / δ * √Z := mul_le_mul_of_nonneg_right hXh hsZ.le
        _ = _ := by ring
    have hmid := masked_le hδ hδ' hZ1 hg hlog (measurableSet_band T₀ U S) (by linarith)
      (band_subset T₀ U S) hε0 (fun t ht => by
        refine hP t ht.1.1 (ht.1.2.trans ?_) ht.2
        have : U ≤ X := by rw [hUdef]; exact div_le_self (by linarith) (by linarith)
        linarith)
    have hq := hQ U hU1
    have hq' : KQ * (U + √Z) / √Z ≤ K * (16 / δ + 1) := by
      rw [div_le_iff₀ hsZ]
      have h1 : KQ * (U + √Z) ≤ |KQ| * (U + √Z) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      have h2 : |KQ| * (U + √Z) ≤ K * (U + √Z) :=
        mul_le_mul_of_nonneg_right (by rw [hK]; linarith only [abs_nonneg KA]) (by linarith)
      have h3 : U + √Z ≤ (16 / δ + 1) * √Z := by
        have : 16 * √Z / δ = 16 / δ * √Z := by ring
        have e2 : (16 / δ + 1) * √Z = 16 / δ * √Z + √Z := by ring
        linarith
      nlinarith
    calc _ ≤ ε ^ 2 * ∫ t in (-U)..U, ‖primeQ δ Z (1 + t * I)‖ ^ 2 := hmid
      _ ≤ Z ^ (-c) * (K * (16 / δ + 1)) := mul_le_mul hεc (hq.trans hq') (by
          exact intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity) hZc0
      _ ≤ 100 * K * (1 + 1 / δ) * Z ^ (-c) := by
          have e : Z ^ (-c) * (K * (16 / δ + 1)) = (16 * (K * (1 / δ)) + K) * Z ^ (-c) := by
            ring
          have e2 : 100 * K * (1 + 1 / δ) * Z ^ (-c) =
              (100 * (K * (1 / δ)) + 100 * K) * Z ^ (-c) := by ring
          rw [e, e2]
          exact mul_le_mul_of_nonneg_right (by linarith only [mul_nonneg hK0 hδinv, hK0]) hZc0
  · -- tail bands
    have hX2h : √Z ≤ X / (2 * h₁) := by
      rw [le_div_iff₀ (by linarith)]
      have hδs : δ * √Z ≤ √Z := mul_le_of_le_one_left hsZ.le (by linarith only [hδ'])
      have h2 : 2 * h₁ ≤ √Z / 2 := by linarith only [hδs, hH1hi, hsZ]
      have := mul_le_mul_of_nonneg_left h2 hsZ.le
      have e : √Z * (√Z / 2) = Z / 2 := by linear_combination hZsq / 2
      linarith only [this, e, hXlo, hZ0]
    have hTlo : √Z ≤ T := hX2h.trans hT
    have hT0 : 0 < T := by linarith only [hTlo, hsZ]
    have hw0 : 0 ≤ X / (h₁ * T) := by positivity
    have hI0 : 0 ≤ ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ nearSet S 1,
        ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2 :=
      setIntegral_nonneg (measurableSet_band _ _ S) fun t _ => by positivity
    rcases le_or_gt T (8 * X) with hT8 | hT8
    · have hmid := masked_le hδ hδ' hZ1 hg hlog (measurableSet_band T (2 * T) S)
        (by linarith only [hT0]) (band_subset T (2 * T) S) hε0
        (fun t ht => hP t (hc₀s.trans (hTlo.trans ht.1.1))
          (by linarith only [ht.1.2, hT8]) ht.2)
      have hq := hQ (2 * T) (by linarith only [hTlo, hs4])
      have hq' : KQ * (2 * T + √Z) / √Z ≤ K * (3 * T) / √Z := by
        apply div_le_div_of_nonneg_right _ hsZ.le
        have h1 : KQ * (2 * T + √Z) ≤ |KQ| * (2 * T + √Z) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hT0, hsZ])
        have h2 : |KQ| ≤ K := by rw [hK]; linarith only [abs_nonneg KA]
        exact h1.trans (mul_le_mul h2 (by linarith only [hTlo]) (by linarith only [hT0, hsZ])
          hK0)
      have hint0 : 0 ≤ ∫ t in (-(2 * T))..(2 * T), ‖primeQ δ Z (1 + t * I)‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith only [hT0]) fun t _ => by positivity
      have hI : (∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ nearSet S 1,
          ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2) ≤
          Z ^ (-c) * (K * (3 * T) / √Z) :=
        hmid.trans (mul_le_mul hεc (hq.trans hq') hint0 hZc0)
      have e : X / (h₁ * T) * (Z ^ (-c) * (K * (3 * T) / √Z)) =
          3 * K * Z ^ (-c) * (X / (h₁ * √Z)) :=
        tail_alg1 _ _ _ _ _ _ hh₁0.ne' hT0.ne' hsZ.ne'
      calc _ ≤ X / (h₁ * T) * (Z ^ (-c) * (K * (3 * T) / √Z)) :=
            mul_le_mul_of_nonneg_left hI hw0
        _ = _ := e
        _ ≤ 3 * K * Z ^ (-c) * (16 / δ) :=
            mul_le_mul_of_nonneg_left hXh (by positivity)
        _ ≤ 100 * K * (1 + 1 / δ) * Z ^ (-c) := by
            have : 3 * K * Z ^ (-c) * (16 / δ) = 48 * (K * (1 / δ)) * Z ^ (-c) := by ring
            have e2 : 100 * K * (1 + 1 / δ) * Z ^ (-c) =
                (100 * (K * (1 / δ)) + 100 * K) * Z ^ (-c) := by ring
            rw [this, e2]
            exact mul_le_mul_of_nonneg_right (by linarith only [mul_nonneg hK0 hδinv, hK0]) hZc0
    · have hTZ : Z ≤ T := by linarith only [hT8, hXlo, hZ0]
      have hint := setIntegral_le_interval (continuous_normA_sq hδ hδ' hZ1 hg)
        (fun t => by positivity) (measurableSet_band T (2 * T) S) (by linarith only [hT0])
        (band_subset T (2 * T) S)
      have ha := hA (2 * T) (by linarith only [hTZ, hZ1])
      have ha' : KA * (2 * T + Z) / Z ≤ K * (3 * T) / Z := by
        apply div_le_div_of_nonneg_right _ hZ0.le
        have h1 : KA * (2 * T + Z) ≤ |KA| * (2 * T + Z) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hT0, hZ0])
        have h2 : |KA| ≤ K := by rw [hK]; linarith only [abs_nonneg KQ]
        exact h1.trans (mul_le_mul h2 (by linarith only [hTZ]) (by linarith only [hT0, hZ0])
          hK0)
      have hI : (∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ nearSet S 1,
          ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2) ≤ K * (3 * T) / Z :=
        hint.trans (ha.trans ha')
      have e : X / (h₁ * T) * (K * (3 * T) / Z) = 3 * K * (X / (h₁ * √Z)) * (1 / √Z) := by
        have := tail_alg2 X h₁ T K (√Z) hh₁0.ne' hT0.ne' hsZ.ne'
        rwa [hZsq] at this
      calc _ ≤ X / (h₁ * T) * (K * (3 * T) / Z) := mul_le_mul_of_nonneg_left hI hw0
        _ = _ := e
        _ ≤ 3 * K * (16 / δ) * Z ^ (-c) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hXh (by positivity)) hsc
              (by positivity) (by positivity)
        _ ≤ 100 * K * (1 + 1 / δ) * Z ^ (-c) := by
            have : 3 * K * (16 / δ) * Z ^ (-c) = 48 * (K * (1 / δ)) * Z ^ (-c) := by ring
            have e2 : 100 * K * (1 + 1 / δ) * Z ^ (-c) =
                (100 * (K * (1 / δ)) + 100 * K) * Z ^ (-c) := by ring
            rw [this, e2]
            exact mul_le_mul_of_nonneg_right (by linarith only [mul_nonneg hK0 hδinv, hK0]) hZc0

end LeanFormalizations.Erdos385

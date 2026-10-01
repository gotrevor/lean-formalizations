/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Mid
import LeanFormalizations.NumberTheory.Erdos385.Parseval.High
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Freq
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Dyadic
import LeanFormalizations.Literature.Erdos385AlmostAll

/-!
# Assembly helpers for MR16 Lemma 14

Frequency bands in `ξ` (with `t = 2πξ`), almost-everywhere continuity of the band indicators,
and the linear change of variables `t = 2πξ` for (Lebesgue) integrals.
-/

open MeasureTheory Complex Set Filter
open scoped FourierTransform ENNReal Topology

noncomputable section

namespace Erdos385.Parseval

open LeanFormalizations.Literature

lemma lintegral_comp_mul_left {g : ℝ → ℝ≥0∞} (hg : Measurable g) {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ ξ, g (c * ξ) = ENNReal.ofReal |c⁻¹| * ∫⁻ t, g t := by
  rw [← lintegral_map hg (measurable_const_mul c), Real.map_volume_mul_left hc,
    lintegral_smul_measure, smul_eq_mul]

/-- Points `ξ` with `|2πξ| = c` form a null set. -/
lemma null_abs_eq (c : ℝ) : volume {ξ : ℝ | |2 * Real.pi * ξ| = c} = 0 := by
  refine measure_mono_null (t := {c / (2 * Real.pi), -c / (2 * Real.pi)}) ?_
    ((toFinite _).measure_zero _)
  intro ξ hξ
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  simp only [mem_insert_iff, mem_singleton_iff]
  rcases eq_or_eq_neg_of_abs_eq hξ with h | h
  · left; rw [eq_div_iff hπ]; linarith
  · right; rw [eq_div_iff hπ]; linarith

lemma eventually_side {r c : ℝ} (h : r ≠ c) :
    ∀ᶠ r' in 𝓝 r, (r' ≤ c ↔ r ≤ c) ∧ (r' < c ↔ r < c) := by
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [eventually_lt_nhds h] with r' hr'
    exact ⟨⟨fun _ ↦ h.le, fun _ ↦ hr'.le⟩, ⟨fun _ ↦ h, fun _ ↦ hr'⟩⟩
  · filter_upwards [eventually_gt_nhds h] with r' hr'
    exact ⟨⟨fun h' ↦ absurd h' (not_le.2 hr'), fun h' ↦ absurd h' (not_le.2 h)⟩,
      ⟨fun h' ↦ absurd h' (not_lt.2 hr'.le), fun h' ↦ absurd h' (not_lt.2 h.le)⟩⟩

/-- An indicator of a set locally constant off a null set is a.e. continuous. -/
lemma ae_continuousAt_indicator {G : ℝ → ℂ} (hG : Continuous G) {S : Set ℝ} {E : Set ℝ}
    (hE : volume E = 0) (hloc : ∀ ξ ∉ E, ∀ᶠ η in 𝓝 ξ, (η ∈ S ↔ ξ ∈ S)) :
    ∀ᵐ ξ, ContinuousAt (S.indicator G) ξ := by
  have : ∀ᵐ ξ, ξ ∉ E := measure_eq_zero_iff_ae_notMem.mp hE
  filter_upwards [this] with ξ hξ
  by_cases hS : ξ ∈ S
  · refine hG.continuousAt.congr ?_
    filter_upwards [hloc ξ hξ] with η hη
    rw [indicator_of_mem (hη.2 hS)]
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hloc ξ hξ] with η hη
    rw [indicator_of_notMem (fun h ↦ hS (hη.1 h))]

/-- The band sets, in the variable `ξ` (`t = 2πξ`). -/
def bandLo (T₀ : ℝ) : Set ℝ := {ξ | |2 * Real.pi * ξ| < T₀}
def bandAll (Y : ℝ) : Set ℝ := {ξ | |2 * Real.pi * ξ| ≤ Y}
def bandMid (T₀ Y : ℝ) : Set ℝ := {ξ | T₀ ≤ |2 * Real.pi * ξ| ∧ |2 * Real.pi * ξ| ≤ Y}

lemma ae_continuousAt_band {G : ℝ → ℂ} (hG : Continuous G) (T₀ Y : ℝ) :
    (∀ᵐ ξ, ContinuousAt ((bandLo T₀).indicator G) ξ) ∧
    (∀ᵐ ξ, ContinuousAt ((bandAll Y).indicator G) ξ) ∧
    (∀ᵐ ξ, ContinuousAt ((bandMid T₀ Y).indicator G) ξ) := by
  set E := {ξ : ℝ | |2 * Real.pi * ξ| = T₀} ∪ {ξ : ℝ | |2 * Real.pi * ξ| = Y}
  have hE : volume E = 0 := measure_union_null (null_abs_eq _) (null_abs_eq _)
  have hc : Continuous fun ξ : ℝ ↦ |2 * Real.pi * ξ| := by fun_prop
  have key : ∀ ξ ∉ E, ∀ᶠ η in 𝓝 ξ, ((|2 * Real.pi * η| ≤ T₀ ↔ |2 * Real.pi * ξ| ≤ T₀) ∧
      (|2 * Real.pi * η| < T₀ ↔ |2 * Real.pi * ξ| < T₀)) ∧
      ((|2 * Real.pi * η| ≤ Y ↔ |2 * Real.pi * ξ| ≤ Y) ∧
      (|2 * Real.pi * η| < Y ↔ |2 * Real.pi * ξ| < Y)) := by
    intro ξ hξ
    simp only [E, mem_union, mem_setOf_eq, not_or] at hξ
    exact (hc.continuousAt.eventually (eventually_side hξ.1)).and
      (hc.continuousAt.eventually (eventually_side hξ.2))
  refine ⟨ae_continuousAt_indicator hG hE fun ξ hξ ↦ ?_,
    ae_continuousAt_indicator hG hE fun ξ hξ ↦ ?_,
    ae_continuousAt_indicator hG hE fun ξ hξ ↦ ?_⟩ <;>
  filter_upwards [key ξ hξ] with η hη
  · simp only [bandLo, mem_setOf_eq, hη.1.2]
  · simp only [bandAll, mem_setOf_eq, hη.2.1]
  · simp only [bandMid, mem_setOf_eq]; simp only [← not_lt (b := T₀), hη.1.2, hη.2.1]

lemma measurableSet_bandLo (T₀ : ℝ) : MeasurableSet (bandLo T₀) :=
  measurableSet_lt (by fun_prop) measurable_const
lemma measurableSet_bandAll (Y : ℝ) : MeasurableSet (bandAll Y) :=
  measurableSet_le (by fun_prop) measurable_const
lemma measurableSet_bandMid (T₀ Y : ℝ) : MeasurableSet (bandMid T₀ Y) :=
  (measurableSet_le measurable_const (g := fun ξ : ℝ ↦ |2 * Real.pi * ξ|) (by fun_prop)).inter
    (measurableSet_le (f := fun ξ : ℝ ↦ |2 * Real.pi * ξ|) (by fun_prop) measurable_const)

lemma fourierInv_add_of_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g :=
  VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner.neg hf hg

lemma measurable_Phi (a : ℕ → ℂ) (N : ℕ) : Measurable (Phi a N) := by
  unfold Phi phiTerm
  refine Finset.measurable_sum _ fun m _ ↦ measurable_const.mul ?_
  exact (Measurable.indicator (by fun_prop) measurableSet_Ici)

lemma measurable_winDif {g : ℝ → ℂ} (hg : Measurable g) (h₁ h₂ : ℝ) :
    Measurable (winDif g h₁ h₂) := by
  unfold winDif winDelta
  have h1 : Measurable fun x : ℝ ↦ g (Real.log (x + h₁)) := hg.comp (by fun_prop)
  have h2 : Measurable fun x : ℝ ↦ g (Real.log (x + h₂)) := hg.comp (by fun_prop)
  have h0 : Measurable fun x : ℝ ↦ g (Real.log x) := hg.comp (by fun_prop)
  fun_prop

lemma winDif_add (f g : ℝ → ℂ) (h₁ h₂ x : ℝ) :
    winDif (f + g) h₁ h₂ x = winDif f h₁ h₂ x + winDif g h₁ h₂ x := by
  simp only [winDif, winDelta, Pi.add_apply]; ring

lemma norm_add3_sq_le (u v w : ℂ) : ‖u + v + w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have h := norm_add₃_le (a := u) (b := v) (c := w)
  have h0 : 0 ≤ ‖u + v + w‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖v‖ - ‖w‖), sq_nonneg (‖u‖ - ‖w‖),
    norm_nonneg u, norm_nonneg v, norm_nonneg w]

lemma bandAll_indicator (G : ℝ → ℂ) {T₀ Y : ℝ} (hTY : T₀ ≤ Y) :
    (bandAll Y).indicator G = (bandLo T₀).indicator G + (bandMid T₀ Y).indicator G := by
  funext ξ
  simp only [Pi.add_apply, indicator, bandAll, bandLo, bandMid, mem_setOf_eq]
  by_cases h1 : |2 * Real.pi * ξ| < T₀
  · rw [if_pos (h1.le.trans hTY), if_pos h1, if_neg (fun h ↦ not_le.2 h1 h.1), add_zero]
  · by_cases h2 : |2 * Real.pi * ξ| ≤ Y
    · rw [if_pos h2, if_neg h1, if_pos ⟨not_lt.1 h1, h2⟩, zero_add]
    · rw [if_neg h2, if_neg h1, if_neg (fun h ↦ h2 h.2), add_zero]

section LSeries

variable {a : ℕ → ℂ} {X : ℝ}

lemma continuous_LSeries_sArg (hX : 0 < X)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) :
    Continuous fun ξ ↦ LSeries a (sArg ξ) := by
  simp_rw [sArg_eq]
  exact (continuous_LSeries_line hX hsupp).comp (by fun_prop)

lemma continuous_sArg : Continuous sArg := by unfold sArg; fun_prop

lemma continuous_LSeries_div_sArg (hX : 0 < X)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) :
    Continuous fun ξ ↦ LSeries a (sArg ξ) / sArg ξ :=
  (continuous_LSeries_sArg hX hsupp).div continuous_sArg sArg_ne_zero

lemma sq_le_norm_sArg_sq (ξ : ℝ) : (2 * Real.pi * ξ) ^ 2 ≤ ‖sArg ξ‖ ^ 2 := by
  have h := abs_im_le_norm (sArg ξ)
  have him : (sArg ξ).im = 2 * Real.pi * ξ := by simp [sArg]
  rw [him] at h
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **High tail in frequency.**  `∫_{|2πξ| > Y} |A/s|² ≤ (2π)⁻¹ · 2B/Y²` from dyadic block
bounds `∫_{T ≤ |t| ≤ 2T} |A(1+it)|² ≤ B T / Y` (`T ≥ Y`). -/
theorem integral_tail_le (hX : 0 < X)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) {Y B : ℝ} (hY : 0 < Y)
    (hB : ∀ T : ℝ, Y ≤ T →
      ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B * T / Y) :
    ∫ ξ in (bandAll Y)ᶜ, ‖LSeries a (sArg ξ) / sArg ξ‖ ^ 2 ≤
      (2 * Real.pi)⁻¹ * (2 * B / Y ^ 2) := by
  set f : ℝ → ℝ := fun t ↦ ‖LSeries a (1 + t * I)‖ ^ 2
  have hfc : Continuous f := (continuous_LSeries_line hX hsupp).norm.pow 2
  have hB0 : 0 ≤ B := by
    have h1 := hB Y le_rfl
    have h0 : 0 ≤ ∫ t in {t : ℝ | Y ≤ |t| ∧ |t| ≤ 2 * Y}, ‖LSeries a (1 + t * I)‖ ^ 2 :=
      integral_nonneg fun _ ↦ by positivity
    rw [mul_div_assoc, div_self hY.ne', mul_one] at h1
    linarith
  set g : ℝ → ℝ≥0∞ := {t : ℝ | Y < |t|}.indicator fun t ↦ ENNReal.ofReal (f t / t ^ 2)
  have hYm : MeasurableSet {t : ℝ | Y < |t|} := measurableSet_lt measurable_const (by fun_prop)
  have hg : Measurable g := (Measurable.ennreal_ofReal (by fun_prop)).indicator hYm
  have hpt : ∀ ξ, ((bandAll Y)ᶜ).indicator
      (fun ξ ↦ ENNReal.ofReal (‖LSeries a (sArg ξ) / sArg ξ‖ ^ 2)) ξ ≤ g (2 * Real.pi * ξ) := by
    intro ξ
    by_cases hξ : ξ ∈ (bandAll Y)ᶜ
    · have hξ' : 2 * Real.pi * ξ ∈ {t : ℝ | Y < |t|} := by
        simpa [bandAll] using hξ
      simp only [g]; rw [indicator_of_mem hξ, indicator_of_mem hξ']
      refine ENNReal.ofReal_le_ofReal ?_
      have ht : 0 < (2 * Real.pi * ξ) ^ 2 := by
        have : 0 < |2 * Real.pi * ξ| := hY.trans hξ'
        rw [← sq_abs]; positivity
      have hs := sq_le_norm_sArg_sq ξ
      simp only [f, norm_div, div_pow]
      rw [← sArg_eq]
      exact div_le_div_of_nonneg_left (by positivity) ht hs
    · rw [indicator_of_notMem hξ]; exact zero_le
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hL : ∫⁻ ξ in (bandAll Y)ᶜ, ENNReal.ofReal (‖LSeries a (sArg ξ) / sArg ξ‖ ^ 2) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2)) := by
    rw [← lintegral_indicator (measurableSet_bandAll Y).compl]
    calc _ ≤ ∫⁻ ξ, g (2 * Real.pi * ξ) := lintegral_mono hpt
      _ = ENNReal.ofReal (|(2 * Real.pi)⁻¹|) * ∫⁻ t, g t := lintegral_comp_mul_left hg hπ.ne'
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          ∫⁻ t in {t : ℝ | Y < |t|}, ENNReal.ofReal (f t / t ^ 2) := by
        rw [abs_of_pos (inv_pos.2 hπ), lintegral_indicator hYm]
      _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal (2 * B / Y ^ 2) := by
        gcongr
        exact lintegral_tail_le hfc (fun _ ↦ by positivity) hY hB
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ by positivity)
    ((continuous_LSeries_div_sArg hX hsupp).norm.pow 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL

lemma integral_bandMid_eq (T₀ Y : ℝ) :
    ∫ ξ, ‖(bandMid T₀ Y).indicator (fun ξ ↦ LSeries a (sArg ξ)) ξ‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ Y}, ‖LSeries a (1 + t * I)‖ ^ 2 := by
  set S' := {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ Y}
  have hS' : MeasurableSet S' :=
    (measurableSet_le measurable_const (g := fun t : ℝ ↦ |t|) (by fun_prop)).inter
      (measurableSet_le (f := fun t : ℝ ↦ |t|) (by fun_prop) measurable_const)
  set f : ℝ → ℝ := fun t ↦ ‖LSeries a (1 + t * I)‖ ^ 2
  have hpt : (fun ξ ↦ ‖(bandMid T₀ Y).indicator (fun ξ ↦ LSeries a (sArg ξ)) ξ‖ ^ 2) =
      fun ξ ↦ S'.indicator f (2 * Real.pi * ξ) := by
    funext ξ
    by_cases hξ : ξ ∈ bandMid T₀ Y
    · have hξ' : 2 * Real.pi * ξ ∈ S' := hξ
      rw [indicator_of_mem hξ, indicator_of_mem hξ', sArg_eq]
    · have hξ' : 2 * Real.pi * ξ ∉ S' := hξ
      rw [indicator_of_notMem hξ, indicator_of_notMem hξ']; simp
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [hpt, Measure.integral_comp_mul_left (fun t ↦ S'.indicator f t), integral_indicator hS',
    abs_of_pos (inv_pos.2 hπ), smul_eq_mul]

lemma abs_le_sub_Icc {c ξ : ℝ} (h : |2 * Real.pi * ξ| ≤ c) :
    ξ ∈ Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor
  · rw [neg_le, le_div_iff₀ hπ]; linarith
  · rw [le_div_iff₀ hπ]; linarith

/-- **MR16 Lemma 14, core.**  The bound with the explicit constant `500`. -/
theorem mr16_core {T₀ h₁ h₂ : ℝ} (hX : 2 ≤ X) (hT₀ : 1 ≤ T₀) (hh₁ : 2 ≤ h₁) (h12 : h₁ ≤ h₂)
    (h2X : h₂ ≤ X / T₀ ^ 3) (ha1 : ∀ m, ‖a m‖ ≤ 1)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) {B : ℝ}
    (hB : ∀ T : ℝ, X / (2 * h₁) ≤ T →
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B) :
    (1 / X) * ∫ x in X..(2 * X), ‖shortSumC a x h₁ / h₁ - shortSumC a x h₂ / h₂‖ ^ 2 ≤
      500 * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁}, ‖LSeries a (1 + t * I)‖ ^ 2)
        + B) := by
  have hX0 : 0 < X := by linarith
  have hh₁0 : 0 < h₁ := by linarith
  have hh₂0 : 0 < h₂ := by linarith
  have hT0 : 0 < T₀ := by linarith
  have hT3 : 1 ≤ T₀ ^ 3 := one_le_pow₀ hT₀
  have hh2X' : h₂ * T₀ ^ 3 ≤ X := by rwa [le_div_iff₀ (by positivity)] at h2X
  have h2X1 : h₂ ≤ X := by nlinarith
  set Y := X / h₁ with hYdef
  have hY : 0 < Y := by positivity
  have hTY : T₀ ≤ Y := by
    rw [hYdef, le_div_iff₀ hh₁0]
    have : T₀ ≤ T₀ ^ 3 := by nlinarith [mul_nonneg hT0.le (by nlinarith : (0:ℝ) ≤ T₀ ^ 2 - 1)]
    nlinarith
  set N := ⌊4 * X⌋₊
  have hsN := supp_floor hX0 hsupp
  set Φ := Phi a N with hΦ
  set Ahat : ℝ → ℂ := fun ξ ↦ LSeries a (sArg ξ) with hAhat
  set F : ℝ → ℂ := fun ξ ↦ Ahat ξ / sArg ξ with hFdef
  have hFΦ : 𝓕 Φ = F := funext (fourier_Phi hsN)
  have hAc : Continuous Ahat := continuous_LSeries_sArg hX0 hsupp
  have hFc : Continuous F := continuous_LSeries_div_sArg hX0 hsupp
  have hAb : ∀ ξ, ‖Ahat ξ‖ ≤ 4 := fun ξ ↦ by
    simp only [Ahat]; rw [sArg_eq]; exact norm_LSeries_line_le (by linarith) ha1 hsupp _
  have hint : ∀ {S : Set ℝ} {c : ℝ}, MeasurableSet S → S ⊆ {ξ | |2 * Real.pi * ξ| ≤ c} →
      ∀ {G : ℝ → ℂ}, Continuous G → Integrable (S.indicator G) := fun hS hSc _ hG ↦
    (integrable_indicator_iff hS).2
      (hG.integrableOn_Icc.mono_set fun ξ hξ ↦ abs_le_sub_Icc (hSc hξ))
  have hLoSub : bandLo T₀ ⊆ {ξ | |2 * Real.pi * ξ| ≤ T₀} := fun ξ hξ ↦ (show |2 * Real.pi * ξ| < T₀ from hξ).le
  have hMidSub : bandMid T₀ Y ⊆ {ξ | |2 * Real.pi * ξ| ≤ Y} := fun ξ hξ ↦ hξ.2
  have hAllSub : bandAll Y ⊆ {ξ | |2 * Real.pi * ξ| ≤ Y} := fun ξ hξ ↦ hξ
  have iLo := hint (measurableSet_bandLo T₀) hLoSub hFc
  have iMid := hint (measurableSet_bandMid T₀ Y) hMidSub hFc
  have iAll := hint (measurableSet_bandAll Y) hAllSub hFc
  set Plo := 𝓕⁻ ((bandLo T₀).indicator F) with hPlo
  set Pmid := 𝓕⁻ ((bandMid T₀ Y).indicator F) with hPmid
  set Phh : ℝ → ℂ := fun u ↦ Φ u - Plo u - Pmid u with hPhh
  have hPloc : Continuous Plo := continuous_fourierInv_of_integrable iLo
  have hPmidc : Continuous Pmid := continuous_fourierInv_of_integrable iMid
  have hPhhm : Measurable Phh :=
    ((measurable_Phi a N).sub hPloc.measurable).sub hPmidc.measurable
  have hsplit : Φ = Plo + Pmid + Phh := by funext u; simp only [Pi.add_apply, Phh]; ring
  have hPall : Plo + Pmid = 𝓕⁻ ((bandAll Y).indicator F) := by
    rw [bandAll_indicator F hTY, fourierInv_add_of_integrable iLo iMid]
  -- Step 1: the short sums are window differences of `Φ` a.e.
  have hstep1 : ∫ x in X..(2 * X), ‖shortSumC a x h₁ / h₁ - shortSumC a x h₂ / h₂‖ ^ 2 =
      ∫ x in Ioc X (2 * X), ‖winDif Φ h₁ h₂ x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hnat : ∀ᵐ x : ℝ, x ∉ range (Nat.cast : ℕ → ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp ((countable_range _).measure_zero _)
    filter_upwards [hnat] with x hx hxI
    have hx0 : 0 < x := hX0.trans hxI.1
    have hxn : ∀ n : ℕ, (n : ℝ) ≠ x := fun n h ↦ hx ⟨n, h⟩
    simp only [shortSumC, winDif, winDelta]
    rw [sum_Icc_eq_Phi hsN hx0 hxn hh₁0.le, sum_Icc_eq_Phi hsN hx0 hxn hh₂0.le]
  set M := ∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁}, ‖LSeries a (1 + t * I)‖ ^ 2 with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ ↦ by positivity
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- block bounds in the form `∫ ≤ B T / Y`
  have hB' : ∀ T : ℝ, Y ≤ T →
      ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B * T / Y := by
    intro T hT
    have hT0 : 0 < T := hY.trans_le hT
    have hXT : X / (2 * h₁) ≤ T := by
      refine le_trans ?_ hT
      rw [hYdef]; exact div_le_div_of_nonneg_left hX0.le hh₁0 (by linarith)
    have h := hB T hXT
    set I0 := ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries a (1 + t * I)‖ ^ 2
    rw [le_div_iff₀ hY]
    have e : X / (h₁ * T) * I0 * T = I0 * Y := by rw [hYdef]; field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_right h hT0.le
  have hB0 : 0 ≤ B := by
    have h1 := hB' Y le_rfl
    have h0 : 0 ≤ ∫ t in {t : ℝ | Y ≤ |t| ∧ |t| ≤ 2 * Y}, ‖LSeries a (1 + t * I)‖ ^ 2 :=
      integral_nonneg fun _ ↦ by positivity
    rw [mul_div_assoc, div_self hY.ne', mul_one] at h1
    linarith
  -- the three band integrals on `Ioc X (2X)`
  set μ := volume.restrict (Ioc X (2 * X))
  have hlo : ∫⁻ x, ENNReal.ofReal (‖winDif Plo h₁ h₂ x‖ ^ 2) ∂μ ≤ ENNReal.ofReal (9 / T₀ * X) := by
    have hpt : ∀ x ∈ Ioc X (2 * X), ENNReal.ofReal (‖winDif Plo h₁ h₂ x‖ ^ 2) ≤
        ENNReal.ofReal (9 / T₀) := by
      intro x hx
      have hx0 : 0 < x := hX0.trans hx.1
      have h := norm_winDif_low (G := Ahat) (K := 4) (R := T₀ / (2 * Real.pi)) hAb
        (by positivity) (fun ξ hξ ↦ abs_le_sub_Icc (hLoSub hξ)) iLo hx0 hh₁0 h12
      have e : 2 * (T₀ / (2 * Real.pi)) * (4 * (2 * (2 * Real.pi * (T₀ / (2 * Real.pi))) * h₂ / x))
          = 8 * T₀ ^ 2 * h₂ / (Real.pi * x) := by field_simp; ring
      rw [e] at h
      have h3 : 8 * T₀ ^ 2 * h₂ / (Real.pi * x) ≤ 3 / T₀ := by
        rw [div_le_div_iff₀ (by positivity) hT0]
        have : 8 * (h₂ * T₀ ^ 3) ≤ 8 * x := by linarith [hx.1]
        nlinarith
      refine ENNReal.ofReal_le_ofReal ?_
      have hn := (h.trans h3)
      calc ‖winDif Plo h₁ h₂ x‖ ^ 2 ≤ (3 / T₀) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = 9 / T₀ / T₀ := by ring
        _ ≤ 9 / T₀ := div_le_self (by positivity) hT₀
    calc _ ≤ ∫⁻ _ in Ioc X (2 * X), ENNReal.ofReal (9 / T₀) := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal (9 / T₀ * X) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
  have hmid : ∫⁻ x, ENNReal.ofReal (‖winDif Pmid h₁ h₂ x‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (12 * X * ((2 * Real.pi)⁻¹ * M)) := by
    set G := (bandMid T₀ Y).indicator Ahat
    have hG : Integrable G := hint (measurableSet_bandMid T₀ Y) hMidSub hAc
    have hK : ∀ ξ, ‖G ξ‖ ≤ 4 := fun ξ ↦ (norm_indicator_le_norm_self (s := bandMid T₀ Y) (f := Ahat) (a := ξ)).trans (hAb ξ)
    have hc := (ae_continuousAt_band hAc T₀ Y).2.2
    have h := integral_winDif_mid_le hG hK hc hX0 hh₁0 h12 h2X1
    have hPm : 𝓕⁻ (fun ξ ↦ G ξ / sArg ξ) = Pmid := by
      rw [hPmid]; congr 1; funext ξ
      simp only [G, F, indicator]; split_ifs <;> simp
    rw [hPm, integral_bandMid_eq] at h
    have hcont := continuousOn_winDif hPmidc hX0 hh₁0.le hh₂0.le
    have hio : IntegrableOn (fun x ↦ ‖winDif Pmid h₁ h₂ x‖ ^ 2) (Ioc X (2 * X)) :=
      ((hcont.norm.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hio (ae_of_all _ fun _ ↦ by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← intervalIntegral.integral_of_le (by linarith)]
    exact h
  have hhi : ∫⁻ x, ENNReal.ofReal (‖winDif Phh h₁ h₂ x‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (432 * X ^ 3 / h₁ ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2))) := by
    have henorm : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z ↦ by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [henorm]
    have hW := lintegral_winDif_le hPhhm hX0 hh₁0 h12 h2X1
    have hcont := (ae_continuousAt_band hFc T₀ Y).2.1
    rw [← hFΦ] at iAll hcont
    obtain ⟨hi1, hi2⟩ := integral_norm_sub_proj (integrable_Phi a N) (norm_Phi_le a N)
      (ae_continuousAt_Phi a N) (measurableSet_bandAll Y) iAll hcont
    rw [hFΦ] at hi1 hi2
    have hPhh' : Phh = fun u ↦ Φ u - 𝓕⁻ ((bandAll Y).indicator F) u := by
      funext u; rw [← hPall]; simp only [Phh, Pi.add_apply]; ring
    have hL2 : ∫⁻ u, ‖Phh u‖ₑ ^ 2 ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2)) := by
      simp_rw [← henorm, hPhh']
      rw [← ofReal_integral_eq_lintegral_ofReal hi1 (ae_of_all _ fun _ ↦ by positivity), hi2]
      exact ENNReal.ofReal_le_ofReal (integral_tail_le hX0 hsupp hY hB')
    calc ∫⁻ x, ‖winDif Phh h₁ h₂ x‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ x in Icc X (2 * X), ‖winDif Phh h₁ h₂ x‖ₑ ^ 2 :=
          lintegral_mono_set Ioc_subset_Icc_self
      _ ≤ _ := hW
      _ ≤ ENNReal.ofReal (432 * X ^ 3 / h₁ ^ 2) *
          ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2)) := by gcongr
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  -- combine
  rw [hstep1]
  have hmeas : ∀ g : ℝ → ℂ, Measurable g →
      Measurable fun x ↦ ENNReal.ofReal (‖winDif g h₁ h₂ x‖ ^ 2) := fun g hg ↦
    ((measurable_winDif hg h₁ h₂).norm.pow_const 2).ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ by positivity)
    ((measurable_winDif (measurable_Phi a N) h₁ h₂).norm.pow_const 2).aestronglyMeasurable]
  set R := 3 * (9 / T₀ * X + 12 * X * ((2 * Real.pi)⁻¹ * M) +
    432 * X ^ 3 / h₁ ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2))) with hRdef
  have hL : ∫⁻ x, ENNReal.ofReal (‖winDif Φ h₁ h₂ x‖ ^ 2) ∂μ ≤ ENNReal.ofReal R := by
    have hpt : ∀ x, ENNReal.ofReal (‖winDif Φ h₁ h₂ x‖ ^ 2) ≤ ENNReal.ofReal 3 *
        (ENNReal.ofReal (‖winDif Plo h₁ h₂ x‖ ^ 2) + ENNReal.ofReal (‖winDif Pmid h₁ h₂ x‖ ^ 2) +
          ENNReal.ofReal (‖winDif Phh h₁ h₂ x‖ ^ 2)) := by
      intro x
      have e : winDif Φ h₁ h₂ x = winDif Plo h₁ h₂ x + winDif Pmid h₁ h₂ x + winDif Phh h₁ h₂ x := by
        rw [hsplit, winDif_add, winDif_add]
      rw [e, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (norm_add3_sq_le _ _ _)
    calc _ ≤ ∫⁻ x, ENNReal.ofReal 3 *
        (ENNReal.ofReal (‖winDif Plo h₁ h₂ x‖ ^ 2) + ENNReal.ofReal (‖winDif Pmid h₁ h₂ x‖ ^ 2) +
          ENNReal.ofReal (‖winDif Phh h₁ h₂ x‖ ^ 2)) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal 3 * (∫⁻ x, ENNReal.ofReal (‖winDif Plo h₁ h₂ x‖ ^ 2) ∂μ +
          ∫⁻ x, ENNReal.ofReal (‖winDif Pmid h₁ h₂ x‖ ^ 2) ∂μ +
          ∫⁻ x, ENNReal.ofReal (‖winDif Phh h₁ h₂ x‖ ^ 2) ∂μ) := by
        rw [lintegral_const_mul _ (((hmeas _ hPloc.measurable).add
          (hmeas _ hPmidc.measurable)).add (hmeas _ hPhhm)),
          lintegral_add_left ((hmeas _ hPloc.measurable).add (hmeas _ hPmidc.measurable)),
          lintegral_add_left (hmeas _ hPloc.measurable)]
      _ ≤ ENNReal.ofReal 3 * (ENNReal.ofReal (9 / T₀ * X) +
          ENNReal.ofReal (12 * X * ((2 * Real.pi)⁻¹ * M)) +
          ENNReal.ofReal (432 * X ^ 3 / h₁ ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2)))) := by
        gcongr
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num)]
  have hR0 : 0 ≤ R := by positivity
  have hRX : R = X * (27 / T₀ + 18 / Real.pi * M + 1296 / Real.pi * B) := by
    rw [hRdef, hYdef]; field_simp; ring
  have hbound := ENNReal.toReal_le_of_le_ofReal hR0 hL
  have h18 : 18 / Real.pi ≤ 500 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1296 : 1296 / Real.pi ≤ 500 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h27 : 27 / T₀ ≤ 500 * (1 / T₀) := by rw [mul_one_div]; gcongr; norm_num
  calc 1 / X * (∫⁻ x, ENNReal.ofReal (‖winDif Φ h₁ h₂ x‖ ^ 2) ∂μ).toReal ≤ 1 / X * R :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 27 / T₀ + 18 / Real.pi * M + 1296 / Real.pi * B := by
        rw [hRX]; field_simp
    _ ≤ 500 * (1 / T₀ + M + B) := by
        nlinarith [mul_le_mul_of_nonneg_right h18 hM0, mul_le_mul_of_nonneg_right h1296 hB0]

end LSeries

end Erdos385.Parseval

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Assembly

/-!
# Erdős #385 power saving: MR16 Lemma 14 with a frequency mask (phase E9b)

`mr16_masked`: `mr16_core` for `Φ − 𝓕⁻(1_E F)`, where `E = {ξ : 2πξ ∈ Eₜ}` and `Eₜ` is a finite
union of closed intervals inside `T₀ ≤ |t|` (the near-1 large-value frequencies).  The right side
loses the frequencies of `Eₜ`: the middle integral and the dyadic block integrals run over
`t ∉ Eₜ` only.

Proof: rerun `mr16_core` with `Pmid' = 𝓕⁻(1_{mid∖E} F)` and
`Phh' = Φ − 𝓕⁻(1_{all ∪ E} F)` in place of `Pmid`, `Phh`; `Plo` is unchanged because `Eₜ` avoids
`|t| < T₀`.  The inputs carry over: `integral_winDif_mid_le` needs only `‖G‖ ≤ 4` and a.e.
continuity of the masked indicator (the frontier of `mid ∖ E` is finite), and
`integral_norm_sub_proj` needs only a measurable set with integrable masked transform; the tail
bound `integral_tail_le` is applied to `|Â|² 1_{Eₜᶜ}`.
-/

open MeasureTheory Complex Set Filter
open scoped FourierTransform ENNReal Topology

noncomputable section

namespace Erdos385.Parseval

open LeanFormalizations.Literature

/-- The `ξ`-set of a `t`-set (`t = 2πξ`). -/
def tSet (Et : Set ℝ) : Set ℝ := {ξ | 2 * Real.pi * ξ ∈ Et}

/-- `lintegral_tail_le` for a locally integrable (not necessarily continuous) `f`. -/
theorem lintegral_tail_le_of_integrableOn {f : ℝ → ℝ}
    (hf : ∀ c : ℝ, IntegrableOn f (Icc (-c) c)) (hf0 : ∀ t, 0 ≤ f t) {T₁ B : ℝ}
    (hT : 0 < T₁)
    (hB : ∀ T : ℝ, T₁ ≤ T → ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, f t ≤ B * T / T₁) :
    ∫⁻ t in {t : ℝ | T₁ < |t|}, ENNReal.ofReal (f t / t ^ 2) ≤ ENNReal.ofReal (2 * B / T₁ ^ 2) := by
  set blk : ℕ → Set ℝ := fun k ↦ {t : ℝ | 2 ^ k * T₁ ≤ |t| ∧ |t| ≤ 2 * (2 ^ k * T₁)}
  have hcover : {t : ℝ | T₁ < |t|} ⊆ ⋃ k, blk k := fun t ht ↦ by
    obtain ⟨k, hk⟩ := exists_block hT ht
    exact mem_iUnion.mpr ⟨k, hk⟩
  have hblk : ∀ k : ℕ, ∫⁻ t in blk k, ENNReal.ofReal (f t / t ^ 2) ≤
      ENNReal.ofReal (B / (2 ^ k * T₁ ^ 2)) := by
    intro k
    set T := 2 ^ k * T₁
    have hTpos : 0 < T := by positivity
    have hsub : blk k ⊆ Icc (-(2 * T)) (2 * T) := fun t ht ↦ abs_le.mp ht.2
    have hmeas : MeasurableSet (blk k) :=
      (measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_le continuous_abs.measurable measurable_const)
    have hint : IntegrableOn f (blk k) := (hf (2 * T)).mono_set hsub
    calc ∫⁻ t in blk k, ENNReal.ofReal (f t / t ^ 2)
        ≤ ∫⁻ t in blk k, ENNReal.ofReal (f t / T ^ 2) := by
          refine setLIntegral_mono' hmeas fun t ht ↦ ENNReal.ofReal_le_ofReal ?_
          apply div_le_div_of_nonneg_left (hf0 t) (by positivity)
          exact (pow_le_pow_left₀ hTpos.le ht.1 2).trans (sq_abs t).le
      _ = ENNReal.ofReal (∫ t in blk k, f t / T ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
            (Filter.Eventually.of_forall fun t ↦ div_nonneg (hf0 t) (by positivity))).symm
      _ ≤ ENNReal.ofReal (B / (2 ^ k * T₁ ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_div]
          have := hB T (le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num)))
          calc (∫ t in blk k, f t) / T ^ 2 ≤ (B * T / T₁) / T ^ 2 := by gcongr
            _ = B / (2 ^ k * T₁ ^ 2) := by simp only [T]; try field_simp
  calc ∫⁻ t in {t : ℝ | T₁ < |t|}, ENNReal.ofReal (f t / t ^ 2)
      ≤ ∫⁻ t in ⋃ k, blk k, ENNReal.ofReal (f t / t ^ 2) := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ t in blk k, ENNReal.ofReal (f t / t ^ 2) := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (B / (2 ^ k * T₁ ^ 2)) := ENNReal.tsum_le_tsum hblk
    _ ≤ ENNReal.ofReal (2 * B / T₁ ^ 2) := by
        rcases le_or_gt 0 B with hB0 | hB0
        · have hs : Summable fun k : ℕ ↦ B / (2 ^ k * T₁ ^ 2) := by
            have := (summable_geometric_two).mul_left (B / T₁ ^ 2)
            refine this.congr fun k ↦ ?_
            rw [one_div, inv_pow]; field_simp
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hs]
          apply ENNReal.ofReal_le_ofReal
          have : ∑' k : ℕ, B / (2 ^ k * T₁ ^ 2) = B / T₁ ^ 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := by
            rw [← tsum_mul_left]; congr 1 with k; rw [one_div, inv_pow]; field_simp
          rw [this, tsum_geometric_two]
          ring_nf; rfl
        · have : ∀ k : ℕ, ENNReal.ofReal (B / (2 ^ k * T₁ ^ 2)) = 0 := fun k ↦
            ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hB0.le (by positivity))
          simp [this]




/-- The near set: a finite union of closed intervals. -/
def nearSet (S : Finset ℝ) (r : ℝ) : Set ℝ := ⋃ s ∈ S, Icc (s - r) (s + r)

lemma measurableSet_nearSet (S : Finset ℝ) (r : ℝ) : MeasurableSet (nearSet S r) :=
  Finset.measurableSet_biUnion S fun _ _ ↦ measurableSet_Icc

/-- The endpoints of the near set. -/
def nearEnds (S : Finset ℝ) (r : ℝ) : Finset ℝ := S.image (· - r) ∪ S.image (· + r)

lemma nearSet_loc (S : Finset ℝ) (r : ℝ) {t : ℝ} (ht : t ∉ nearEnds S r) :
    ∀ᶠ t' in 𝓝 t, (t' ∈ nearSet S r ↔ t ∈ nearSet S r) := by
  have hall : ∀ᶠ t' in 𝓝 t, ∀ s ∈ S,
      ((t' ≤ s - r ↔ t ≤ s - r) ∧ (t' < s - r ↔ t < s - r)) ∧
      ((t' ≤ s + r ↔ t ≤ s + r) ∧ (t' < s + r ↔ t < s + r)) := by
    rw [Filter.eventually_all_finset]
    intro s hs
    have h1 : t ≠ s - r := fun h ↦ ht (by
      simp only [nearEnds, Finset.mem_union, Finset.mem_image]; exact Or.inl ⟨s, hs, h.symm⟩)
    have h2 : t ≠ s + r := fun h ↦ ht (by
      simp only [nearEnds, Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨s, hs, h.symm⟩)
    exact (eventually_side h1).and (eventually_side h2)
  filter_upwards [hall] with t' ht'
  simp only [nearSet, mem_iUnion, mem_Icc, exists_prop]
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    obtain ⟨⟨_, a2⟩, ⟨b1, _⟩⟩ := ht' s hs
    refine ⟨s, hs, ?_, b1.1 h2⟩
    by_contra hc; push Not at hc
    exact absurd (a2.2 hc) (not_lt.2 h1)
  · rintro ⟨s, hs, h1, h2⟩
    obtain ⟨⟨_, a2⟩, ⟨b1, _⟩⟩ := ht' s hs
    refine ⟨s, hs, ?_, b1.2 h2⟩
    by_contra hc; push Not at hc
    exact absurd (a2.1 hc) (not_lt.2 h1)

lemma null_tSet_finset (P : Finset ℝ) : volume (tSet (P : Set ℝ)) = 0 := by
  refine measure_mono_null (t := (P.image (· / (2 * Real.pi)) : Set ℝ)) ?_
    ((Finset.finite_toSet _).measure_zero _)
  intro ξ hξ
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  simp only [Finset.coe_image, mem_image, Finset.mem_coe]
  exact ⟨_, hξ, by field_simp⟩

lemma tSet_nearSet_loc (S : Finset ℝ) (r : ℝ) {ξ : ℝ}
    (hξ : ξ ∉ tSet (nearEnds S r : Set ℝ)) :
    ∀ᶠ η in 𝓝 ξ, (η ∈ tSet (nearSet S r) ↔ ξ ∈ tSet (nearSet S r)) := by
  have hc : Continuous fun η : ℝ ↦ 2 * Real.pi * η := by fun_prop
  exact hc.continuousAt.eventually (nearSet_loc S r hξ)

lemma nearSet_subset (S : Finset ℝ) (r : ℝ) :
    nearSet S r ⊆ {t : ℝ | |t| ≤ ∑ s ∈ S, |s| + |r|} := by
  intro t ht
  simp only [nearSet, mem_iUnion, mem_Icc, exists_prop] at ht
  obtain ⟨s, hs, h1, h2⟩ := ht
  have hsS : |s| ≤ ∑ s ∈ S, |s| :=
    Finset.single_le_sum (f := fun s ↦ |s|) (fun _ _ ↦ abs_nonneg _) hs
  simp only [mem_setOf_eq, abs_le]
  constructor <;> cases abs_cases s <;> cases abs_cases r <;> linarith

section LSeries

variable {a : ℕ → ℂ} {X : ℝ}

/-- **Masked high tail.** -/
theorem integral_tail_le_masked (hX : 0 < X)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) {Et : Set ℝ} (hEt : MeasurableSet Et)
    {Y B : ℝ} (hY : 0 < Y)
    (hB : ∀ T : ℝ, Y ≤ T →
      ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ Et, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B * T / Y) :
    ∫ ξ in (bandAll Y)ᶜ ∩ (tSet Et)ᶜ, ‖LSeries a (sArg ξ) / sArg ξ‖ ^ 2 ≤
      (2 * Real.pi)⁻¹ * (2 * B / Y ^ 2) := by
  set f : ℝ → ℝ := Etᶜ.indicator fun t ↦ ‖LSeries a (1 + t * I)‖ ^ 2
  have hfc0 : Continuous fun t : ℝ ↦ ‖LSeries a (1 + t * I)‖ ^ 2 :=
    (continuous_LSeries_line hX hsupp).norm.pow 2
  have hf0 : ∀ t, 0 ≤ f t := fun t ↦ by
    simp only [f, indicator]; split_ifs <;> positivity
  have hfi : ∀ c : ℝ, IntegrableOn f (Icc (-c) c) := fun c ↦
    (hfc0.integrableOn_Icc).indicator hEt.compl
  have hBf : ∀ T : ℝ, Y ≤ T → ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, f t ≤ B * T / Y := by
    intro T hT
    rw [setIntegral_indicator hEt.compl]
    exact hB T hT
  have hB0 : 0 ≤ B := by
    have h1 := hBf Y le_rfl
    have h0 : 0 ≤ ∫ t in {t : ℝ | Y ≤ |t| ∧ |t| ≤ 2 * Y}, f t :=
      integral_nonneg fun t ↦ hf0 t
    rw [mul_div_assoc, div_self hY.ne', mul_one] at h1
    linarith
  set g : ℝ → ℝ≥0∞ := {t : ℝ | Y < |t|}.indicator fun t ↦ ENNReal.ofReal (f t / t ^ 2)
  have hYm : MeasurableSet {t : ℝ | Y < |t|} := measurableSet_lt measurable_const (by fun_prop)
  have hfm : Measurable f := hfc0.measurable.indicator hEt.compl
  have hg : Measurable g := (Measurable.ennreal_ofReal (by fun_prop)).indicator hYm
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hEξ : MeasurableSet (tSet Et) := hEt.preimage (by fun_prop)
  have hpt : ∀ ξ, ((bandAll Y)ᶜ ∩ (tSet Et)ᶜ).indicator
      (fun ξ ↦ ENNReal.ofReal (‖LSeries a (sArg ξ) / sArg ξ‖ ^ 2)) ξ ≤ g (2 * Real.pi * ξ) := by
    intro ξ
    by_cases hξ : ξ ∈ (bandAll Y)ᶜ ∩ (tSet Et)ᶜ
    · have hξ' : 2 * Real.pi * ξ ∈ {t : ℝ | Y < |t|} := by
        simpa [bandAll] using hξ.1
      have hξE : 2 * Real.pi * ξ ∈ Etᶜ := hξ.2
      simp only [g]; rw [indicator_of_mem hξ, indicator_of_mem hξ']
      refine ENNReal.ofReal_le_ofReal ?_
      have ht : 0 < (2 * Real.pi * ξ) ^ 2 := by
        have : 0 < |2 * Real.pi * ξ| := hY.trans hξ'
        rw [← sq_abs]; positivity
      have hs := sq_le_norm_sArg_sq ξ
      simp only [f, indicator_of_mem hξE, norm_div, div_pow]
      rw [← sArg_eq]
      exact div_le_div_of_nonneg_left (by positivity) ht hs
    · rw [indicator_of_notMem hξ]; exact zero_le
  have hL : ∫⁻ ξ in (bandAll Y)ᶜ ∩ (tSet Et)ᶜ,
      ENNReal.ofReal (‖LSeries a (sArg ξ) / sArg ξ‖ ^ 2) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2)) := by
    rw [← lintegral_indicator ((measurableSet_bandAll Y).compl.inter hEξ.compl)]
    calc _ ≤ ∫⁻ ξ, g (2 * Real.pi * ξ) := lintegral_mono hpt
      _ = ENNReal.ofReal (|(2 * Real.pi)⁻¹|) * ∫⁻ t, g t := lintegral_comp_mul_left hg hπ.ne'
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          ∫⁻ t in {t : ℝ | Y < |t|}, ENNReal.ofReal (f t / t ^ 2) := by
        rw [abs_of_pos (inv_pos.2 hπ), lintegral_indicator hYm]
      _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal (2 * B / Y ^ 2) := by
        gcongr
        exact lintegral_tail_le_of_integrableOn hfi hf0 hY hBf
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ by positivity)
    ((continuous_LSeries_div_sArg hX hsupp).norm.pow 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL

lemma integral_bandMid_masked {Et : Set ℝ} (hEt : MeasurableSet Et) (T₀ Y : ℝ) :
    ∫ ξ, ‖(bandMid T₀ Y ∩ (tSet Et)ᶜ).indicator (fun ξ ↦ LSeries a (sArg ξ)) ξ‖ ^ 2 =
      (2 * Real.pi)⁻¹ *
        ∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ Y} \ Et, ‖LSeries a (1 + t * I)‖ ^ 2 := by
  set S' := {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ Y} \ Et
  have hS' : MeasurableSet S' :=
    ((measurableSet_le measurable_const (g := fun t : ℝ ↦ |t|) (by fun_prop)).inter
      (measurableSet_le (f := fun t : ℝ ↦ |t|) (by fun_prop) measurable_const)).diff hEt
  set f : ℝ → ℝ := fun t ↦ ‖LSeries a (1 + t * I)‖ ^ 2
  have hpt : (fun ξ ↦ ‖(bandMid T₀ Y ∩ (tSet Et)ᶜ).indicator (fun ξ ↦ LSeries a (sArg ξ)) ξ‖ ^ 2) =
      fun ξ ↦ S'.indicator f (2 * Real.pi * ξ) := by
    funext ξ
    by_cases hξ : ξ ∈ bandMid T₀ Y ∩ (tSet Et)ᶜ
    · have hξ' : 2 * Real.pi * ξ ∈ S' := ⟨hξ.1, hξ.2⟩
      rw [indicator_of_mem hξ, indicator_of_mem hξ', sArg_eq]
    · have hξ' : 2 * Real.pi * ξ ∉ S' := fun h ↦ hξ ⟨h.1, h.2⟩
      rw [indicator_of_notMem hξ, indicator_of_notMem hξ']; simp
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [hpt, Measure.integral_comp_mul_left (fun t ↦ S'.indicator f t), integral_indicator hS',
    abs_of_pos (inv_pos.2 hπ), smul_eq_mul]

end LSeries

/-- **Masked MR16 Lemma 14.** -/
theorem mr16_masked {a : ℕ → ℂ} {X T₀ h₁ h₂ : ℝ} (hX : 2 ≤ X) (hT₀ : 1 ≤ T₀) (hh₁ : 2 ≤ h₁)
    (h12 : h₁ ≤ h₂) (h2X : h₂ ≤ X / T₀ ^ 3) (ha1 : ∀ m, ‖a m‖ ≤ 1)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0)
    (S : Finset ℝ) (r : ℝ) (hr : 0 ≤ r) (hS : ∀ s ∈ S, T₀ + r ≤ |s|) {B : ℝ}
    (hB : ∀ T : ℝ, X / (2 * h₁) ≤ T →
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ nearSet S r,
          ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B) :
    (1 / X) * ∫ x in Ioc X (2 * X),
        ‖winDif (fun u ↦ Phi a ⌊4 * X⌋₊ u - 𝓕⁻ ((tSet (nearSet S r)).indicator
          fun ξ ↦ LSeries a (sArg ξ) / sArg ξ) u) h₁ h₂ x‖ ^ 2 ≤
      500 * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁} \ nearSet S r,
        ‖LSeries a (1 + t * I)‖ ^ 2) + B) := by
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
  set Et := nearSet S r with hEtdef
  have hEt : MeasurableSet Et := measurableSet_nearSet S r
  set E := tSet Et with hEdef
  have hE : MeasurableSet E := hEt.preimage (by fun_prop)
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
  set R := ∑ s ∈ S, |s| + |r|
  have hESub : E ⊆ {ξ | |2 * Real.pi * ξ| ≤ R} := fun ξ hξ ↦ nearSet_subset S r hξ
  have hELo : ∀ ξ ∈ E, ξ ∉ bandLo T₀ := by
    intro ξ hξ hlo
    simp only [hEdef, tSet, hEtdef, nearSet, mem_setOf_eq, mem_iUnion, mem_Icc,
      exists_prop] at hξ
    obtain ⟨s, hs, h1, h2⟩ := hξ
    have := hS s hs
    have hlo' : |2 * Real.pi * ξ| < T₀ := hlo
    rw [abs_lt] at hlo'
    cases abs_cases s <;> linarith
  have hLoSub : bandLo T₀ ⊆ {ξ | |2 * Real.pi * ξ| ≤ T₀} := fun ξ hξ ↦
    (show |2 * Real.pi * ξ| < T₀ from hξ).le
  have hMidSub : bandMid T₀ Y ∩ Eᶜ ⊆ {ξ | |2 * Real.pi * ξ| ≤ Y} := fun ξ hξ ↦ hξ.1.2
  have hmidE : MeasurableSet (bandMid T₀ Y ∩ Eᶜ) := (measurableSet_bandMid T₀ Y).inter hE.compl
  have hallE : MeasurableSet (bandAll Y ∪ E) := (measurableSet_bandAll Y).union hE
  have hAllESub : bandAll Y ∪ E ⊆ {ξ | |2 * Real.pi * ξ| ≤ max Y R} := by
    rintro ξ (h | h)
    · exact (show |2 * Real.pi * ξ| ≤ Y from h).trans (le_max_left _ _)
    · exact (show |2 * Real.pi * ξ| ≤ R from hESub h).trans (le_max_right _ _)
  have iLo := hint (measurableSet_bandLo T₀) hLoSub hFc
  have iMid := hint hmidE hMidSub hFc
  have iE := hint hE hESub hFc
  have iAllE := hint hallE hAllESub hFc
  -- a.e. continuity of the masked indicators
  set Z0 := {ξ : ℝ | |2 * Real.pi * ξ| = T₀} ∪ {ξ : ℝ | |2 * Real.pi * ξ| = Y} ∪
    tSet (nearEnds S r : Set ℝ)
  have hZ0 : volume Z0 = 0 :=
    measure_union_null (measure_union_null (null_abs_eq _) (null_abs_eq _)) (null_tSet_finset _)
  have hcabs : Continuous fun ξ : ℝ ↦ |2 * Real.pi * ξ| := by fun_prop
  have key : ∀ ξ ∉ Z0, ∀ᶠ η in 𝓝 ξ, ((|2 * Real.pi * η| ≤ T₀ ↔ |2 * Real.pi * ξ| ≤ T₀) ∧
      (|2 * Real.pi * η| < T₀ ↔ |2 * Real.pi * ξ| < T₀)) ∧
      ((|2 * Real.pi * η| ≤ Y ↔ |2 * Real.pi * ξ| ≤ Y) ∧
      (|2 * Real.pi * η| < Y ↔ |2 * Real.pi * ξ| < Y)) ∧ (η ∈ E ↔ ξ ∈ E) := by
    intro ξ hξ
    simp only [Z0, mem_union, mem_setOf_eq, not_or] at hξ
    exact (hcabs.continuousAt.eventually (eventually_side hξ.1.1)).and
      ((hcabs.continuousAt.eventually (eventually_side hξ.1.2)).and
        (tSet_nearSet_loc S r hξ.2))
  have cMid : ∀ {G : ℝ → ℂ}, Continuous G →
      ∀ᵐ ξ, ContinuousAt ((bandMid T₀ Y ∩ Eᶜ).indicator G) ξ := fun hG ↦
    ae_continuousAt_indicator hG hZ0 fun ξ hξ ↦ by
      filter_upwards [key ξ hξ] with η hη
      simp only [bandMid, mem_inter_iff, mem_setOf_eq, mem_compl_iff, hη.2.2]
      simp only [← not_lt (b := T₀), hη.1.2, hη.2.1.1]
  have cAllE : ∀ᵐ ξ, ContinuousAt ((bandAll Y ∪ E).indicator F) ξ :=
    ae_continuousAt_indicator hFc hZ0 fun ξ hξ ↦ by
      filter_upwards [key ξ hξ] with η hη
      simp only [bandAll, mem_union, mem_setOf_eq, hη.2.1.1, hη.2.2]
  -- the decomposition
  set Plo := 𝓕⁻ ((bandLo T₀).indicator F) with hPlo
  set Pmid := 𝓕⁻ ((bandMid T₀ Y ∩ Eᶜ).indicator F) with hPmid
  set PE := 𝓕⁻ (E.indicator F) with hPE
  set Q : ℝ → ℂ := fun u ↦ Φ u - PE u with hQ
  set Phh : ℝ → ℂ := fun u ↦ Q u - Plo u - Pmid u with hPhh
  have hPloc : Continuous Plo := continuous_fourierInv_of_integrable iLo
  have hPmidc : Continuous Pmid := continuous_fourierInv_of_integrable iMid
  have hPEc : Continuous PE := continuous_fourierInv_of_integrable iE
  have hQm : Measurable Q := (measurable_Phi a N).sub hPEc.measurable
  have hPhhm : Measurable Phh := (hQm.sub hPloc.measurable).sub hPmidc.measurable
  have hsplit : Q = Plo + Pmid + Phh := by funext u; simp only [Pi.add_apply, Phh]; ring
  have hind : (bandAll Y ∪ E).indicator F =
      ((bandLo T₀).indicator F + (bandMid T₀ Y ∩ Eᶜ).indicator F) + E.indicator F := by
    funext ξ
    simp only [Pi.add_apply]
    by_cases hξE : ξ ∈ E
    · rw [indicator_of_mem (show ξ ∈ bandAll Y ∪ E from Or.inr hξE), indicator_of_notMem (hELo ξ hξE),
        indicator_of_notMem (fun h ↦ h.2 hξE), indicator_of_mem hξE]
      simp
    · by_cases h1 : ξ ∈ bandLo T₀
      · have h1' : |2 * Real.pi * ξ| < T₀ := h1
        rw [indicator_of_mem (show ξ ∈ bandAll Y ∪ E from Or.inl (show |2 * Real.pi * ξ| ≤ Y from h1'.le.trans hTY)),
          indicator_of_mem h1, indicator_of_notMem (fun h ↦ not_le.2 h1' h.1.1),
          indicator_of_notMem hξE]
        simp
      · have h1' : ¬ |2 * Real.pi * ξ| < T₀ := h1
        by_cases h2 : ξ ∈ bandAll Y
        · rw [indicator_of_mem (show ξ ∈ bandAll Y ∪ E from Or.inl h2), indicator_of_notMem h1,
            indicator_of_mem (show ξ ∈ bandMid T₀ Y ∩ Eᶜ from ⟨⟨not_lt.1 h1', h2⟩, hξE⟩), indicator_of_notMem hξE]
          simp
        · rw [indicator_of_notMem (show ξ ∉ bandAll Y ∪ E by rintro (h | h); exacts [h2 h, hξE h]),
            indicator_of_notMem h1, indicator_of_notMem (fun h ↦ h2 h.1.2),
            indicator_of_notMem hξE]
          simp
  have hPall : Plo + Pmid + PE = 𝓕⁻ ((bandAll Y ∪ E).indicator F) := by
    rw [hind, fourierInv_add_of_integrable (iLo.add iMid) iE,
      fourierInv_add_of_integrable iLo iMid]
  set M := ∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁} \ Et, ‖LSeries a (1 + t * I)‖ ^ 2 with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ ↦ by positivity
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hB' : ∀ T : ℝ, Y ≤ T →
      ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ Et, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B * T / Y := by
    intro T hT
    have hT0 : 0 < T := hY.trans_le hT
    have hXT : X / (2 * h₁) ≤ T := by
      refine le_trans ?_ hT
      rw [hYdef]; exact div_le_div_of_nonneg_left hX0.le hh₁0 (by linarith)
    have h := hB T hXT
    set I0 := ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ Et, ‖LSeries a (1 + t * I)‖ ^ 2
    rw [le_div_iff₀ hY]
    have e : X / (h₁ * T) * I0 * T = I0 * Y := by rw [hYdef]; field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_right h hT0.le
  have hB0 : 0 ≤ B := by
    have h1 := hB' Y le_rfl
    have h0 : 0 ≤ ∫ t in {t : ℝ | Y ≤ |t| ∧ |t| ≤ 2 * Y} \ Et, ‖LSeries a (1 + t * I)‖ ^ 2 :=
      integral_nonneg fun _ ↦ by positivity
    rw [mul_div_assoc, div_self hY.ne', mul_one] at h1
    linarith
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
    set G := (bandMid T₀ Y ∩ Eᶜ).indicator Ahat
    have hG : Integrable G := hint hmidE hMidSub hAc
    have hK : ∀ ξ, ‖G ξ‖ ≤ 4 := fun ξ ↦
      (norm_indicator_le_norm_self (s := bandMid T₀ Y ∩ Eᶜ) (f := Ahat) (a := ξ)).trans (hAb ξ)
    have hc := cMid hAc
    have h := integral_winDif_mid_le hG hK hc hX0 hh₁0 h12 h2X1
    have hPm : 𝓕⁻ (fun ξ ↦ G ξ / sArg ξ) = Pmid := by
      rw [hPmid]; congr 1; funext ξ
      simp only [G, F, indicator]; split_ifs <;> simp
    rw [hPm, integral_bandMid_masked hEt] at h
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
    have hcont := cAllE
    rw [← hFΦ] at iAllE hcont
    obtain ⟨hi1, hi2⟩ := integral_norm_sub_proj (integrable_Phi a N) (norm_Phi_le a N)
      (ae_continuousAt_Phi a N) hallE iAllE hcont
    rw [hFΦ] at hi1 hi2
    have hPhh' : Phh = fun u ↦ Φ u - 𝓕⁻ ((bandAll Y ∪ E).indicator F) u := by
      funext u; rw [← hPall]; simp only [Phh, Q, Pi.add_apply]; ring
    have hL2 : ∫⁻ u, ‖Phh u‖ₑ ^ 2 ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2)) := by
      simp_rw [← henorm, hPhh']
      rw [← ofReal_integral_eq_lintegral_ofReal hi1 (ae_of_all _ fun _ ↦ by positivity), hi2,
        compl_union]
      exact ENNReal.ofReal_le_ofReal (integral_tail_le_masked hX0 hsupp hEt hY hB')
    calc ∫⁻ x, ‖winDif Phh h₁ h₂ x‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ x in Icc X (2 * X), ‖winDif Phh h₁ h₂ x‖ₑ ^ 2 :=
          lintegral_mono_set Ioc_subset_Icc_self
      _ ≤ _ := hW
      _ ≤ ENNReal.ofReal (432 * X ^ 3 / h₁ ^ 2) *
          ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2)) := by gcongr
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  -- combine
  have hmeas : ∀ g : ℝ → ℂ, Measurable g →
      Measurable fun x ↦ ENNReal.ofReal (‖winDif g h₁ h₂ x‖ ^ 2) := fun g hg ↦
    ((measurable_winDif hg h₁ h₂).norm.pow_const 2).ennreal_ofReal
  change (1 / X) * ∫ x, ‖winDif Q h₁ h₂ x‖ ^ 2 ∂μ ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ by positivity)
    ((measurable_winDif hQm h₁ h₂).norm.pow_const 2).aestronglyMeasurable]
  set R' := 3 * (9 / T₀ * X + 12 * X * ((2 * Real.pi)⁻¹ * M) +
    432 * X ^ 3 / h₁ ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B / Y ^ 2))) with hRdef
  have hL : ∫⁻ x, ENNReal.ofReal (‖winDif Q h₁ h₂ x‖ ^ 2) ∂μ ≤ ENNReal.ofReal R' := by
    have hpt : ∀ x, ENNReal.ofReal (‖winDif Q h₁ h₂ x‖ ^ 2) ≤ ENNReal.ofReal 3 *
        (ENNReal.ofReal (‖winDif Plo h₁ h₂ x‖ ^ 2) + ENNReal.ofReal (‖winDif Pmid h₁ h₂ x‖ ^ 2) +
          ENNReal.ofReal (‖winDif Phh h₁ h₂ x‖ ^ 2)) := by
      intro x
      have e : winDif Q h₁ h₂ x = winDif Plo h₁ h₂ x + winDif Pmid h₁ h₂ x + winDif Phh h₁ h₂ x := by
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
      _ = ENNReal.ofReal R' := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num)]
  have hR0 : 0 ≤ R' := by positivity
  have hRX : R' = X * (27 / T₀ + 18 / Real.pi * M + 1296 / Real.pi * B) := by
    rw [hRdef, hYdef]; field_simp; ring
  have hbound := ENNReal.toReal_le_of_le_ofReal hR0 hL
  have h18 : 18 / Real.pi ≤ 500 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1296 : 1296 / Real.pi ≤ 500 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h27 : 27 / T₀ ≤ 500 * (1 / T₀) := by rw [mul_one_div]; gcongr; norm_num
  calc 1 / X * (∫⁻ x, ENNReal.ofReal (‖winDif Q h₁ h₂ x‖ ^ 2) ∂μ).toReal ≤ 1 / X * R' :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 27 / T₀ + 18 / Real.pi * M + 1296 / Real.pi * B := by
        rw [hRX]; field_simp
    _ ≤ 500 * (1 / T₀ + M + B) := by
        nlinarith [mul_le_mul_of_nonneg_right h18 hM0, mul_le_mul_of_nonneg_right h1296 hB0]

end Erdos385.Parseval

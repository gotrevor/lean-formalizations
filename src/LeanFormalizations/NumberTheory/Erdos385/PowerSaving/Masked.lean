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

Proof plan (85%): rerun `mr16_core` with `Pmid' = 𝓕⁻(1_{mid∖E} F)` and
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
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ ⋃ s ∈ S, Icc (s - r) (s + r),
          ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B) :
    (1 / X) * ∫ x in Ioc X (2 * X),
        ‖winDif (fun u ↦ Phi a ⌊4 * X⌋₊ u - 𝓕⁻ ((tSet (⋃ s ∈ S, Icc (s - r) (s + r))).indicator
          fun ξ ↦ LSeries a (sArg ξ) / sArg ξ) u) h₁ h₂ x‖ ^ 2 ≤
      500 * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁} \ ⋃ s ∈ S, Icc (s - r) (s + r),
        ‖LSeries a (1 + t * I)‖ ^ 2) + B) := by
  sorry

end Erdos385.Parseval

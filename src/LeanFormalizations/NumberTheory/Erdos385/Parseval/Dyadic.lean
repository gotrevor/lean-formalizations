/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The dyadic tail bound

If `∫_{T ≤ |t| ≤ 2T} f ≤ B T / T₁` for every `T ≥ T₁`, then `∫⁻_{|t| > T₁} f/t² ≤ 2B/T₁²`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Erdos385.Parseval

/-- The dyadic blocks cover the tail. -/
lemma exists_block {T₁ t : ℝ} (hT : 0 < T₁) (ht : T₁ < |t|) :
    ∃ k : ℕ, 2 ^ k * T₁ ≤ |t| ∧ |t| ≤ 2 * (2 ^ k * T₁) := by
  have hex : ∃ k : ℕ, |t| ≤ 2 ^ (k + 1) * T₁ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|t| / T₁) (by norm_num : (1 : ℝ) < 2)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hT] at hk
    have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
    nlinarith
  classical
  let k := Nat.find hex
  refine ⟨k, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simp; exact ht.le
    · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      have e : Nat.find hex - 1 + 1 = k := Nat.sub_add_cancel hpos
      rw [e] at this
      exact (not_le.mp this).le
  · have := Nat.find_spec hex
    rw [pow_succ] at this
    linarith

theorem lintegral_tail_le {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) {T₁ B : ℝ}
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
    have hint : IntegrableOn f (blk k) := (hf.integrableOn_Icc).mono_set hsub
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

end Erdos385.Parseval

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Cover
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.LayerCake

/-!
# Erdős #385 power saving: near-set integrals by interval maxima (phase E9b)

* `integral_nearSet_le_sum`: `∫_{nearSet S 1} f ≤ Σ_s 2 f(τ_s)`, `τ_s` a maximiser of `f` on
  `[s − 1, s + 1]`;
* `card_filter_le_four_mul`: for `1`-separated `S` and `|τ s − s| ≤ 1`, the four classes
  `⌊s⌋ ≡ r (mod 4)` have `1`-separated `τ`-images, so a count bound for separated sets of `τ`
  values gives `4×` that bound for `S`.
-/

namespace Erdos385.Parseval

open MeasureTheory Set

/-- A maximiser of a continuous function on `[s − 1, s + 1]`. -/
lemma exists_max_Icc {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    ∃ τ ∈ Icc (s - 1) (s + 1), ∀ t ∈ Icc (s - 1) (s + 1), f t ≤ f τ := by
  obtain ⟨τ, hτ, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith : s - 1 ≤ s + 1))
    hf.continuousOn
  exact ⟨τ, hτ, fun t ht => hmax ht⟩

theorem integral_nearSet_le_sum {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (S : Finset ℝ) (τ : ℝ → ℝ) (hτ : ∀ s ∈ S, ∀ t ∈ Icc (s - 1) (s + 1), f t ≤ f (τ s)) :
    ∫ t in nearSet S 1, f t ≤ ∑ s ∈ S, 2 * f (τ s) := by
  classical
  have hint : ∀ s : ℝ, Integrable ((Icc (s - 1) (s + 1)).indicator f) := fun s =>
    (hf.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  calc ∫ t in nearSet S 1, f t = ∫ t, (nearSet S 1).indicator f t :=
        (integral_indicator (measurableSet_nearSet S 1)).symm
    _ ≤ ∫ t, ∑ s ∈ S, (Icc (s - 1) (s + 1)).indicator f t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => indicator_nonneg
          (fun t _ => hf0 t) t) (integrable_finset_sum _ fun s _ => hint s)
          (Filter.Eventually.of_forall fun t => ?_)
        by_cases ht : t ∈ nearSet S 1
        · rw [indicator_of_mem ht]
          simp only [nearSet, mem_iUnion] at ht
          obtain ⟨s, hs, hts⟩ := ht
          calc f t = (Icc (s - 1) (s + 1)).indicator f t := (indicator_of_mem hts _).symm
            _ ≤ _ := Finset.single_le_sum (f := fun s => (Icc (s - 1) (s + 1)).indicator f t)
                (fun s _ => indicator_nonneg (fun t _ => hf0 t) t) hs
        · rw [indicator_of_notMem ht]
          exact Finset.sum_nonneg fun s _ => indicator_nonneg (fun t _ => hf0 t) t
    _ = ∑ s ∈ S, ∫ t in Icc (s - 1) (s + 1), f t := by
        rw [integral_finset_sum _ fun s _ => hint s]
        exact Finset.sum_congr rfl fun s _ => integral_indicator measurableSet_Icc
    _ ≤ ∑ s ∈ S, 2 * f (τ s) := by
        refine Finset.sum_le_sum fun s hs => ?_
        calc ∫ t in Icc (s - 1) (s + 1), f t ≤ ∫ t in Icc (s - 1) (s + 1), f (τ s) :=
              setIntegral_mono_on (hf.continuousOn.integrableOn_compact isCompact_Icc)
                (integrableOn_const (by simp)) measurableSet_Icc (hτ s hs)
          _ = 2 * f (τ s) := by
              rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
                ENNReal.toReal_ofReal (by linarith)]
              ring

/-- Points of a `1`-separated set in the same class mod `4` of `⌊·⌋` are `> 3` apart. -/
lemma sep_of_mod4 {S : Finset ℝ} (hS : Separated S) {s s' : ℝ} (hs : s ∈ S) (hs' : s' ∈ S)
    (hne : s ≠ s') (hr : ⌊s⌋ % 4 = ⌊s'⌋ % 4) : 3 < |s - s'| := by
  have hfl : ⌊s⌋ ≠ ⌊s'⌋ := by
    intro h
    have := Int.abs_sub_lt_one_of_floor_eq_floor h
    linarith [hS s hs s' hs' hne]
  have h4 : 4 ≤ |⌊s⌋ - ⌊s'⌋| := by
    have hd : (4 : ℤ) ∣ ⌊s⌋ - ⌊s'⌋ := Int.ModEq.dvd hr.symm
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by rintro rfl; apply hfl; linarith
    rw [hk, abs_mul]
    have : 1 ≤ |k| := Int.one_le_abs hk0
    norm_num; linarith
  have h4' : (4 : ℝ) ≤ |(⌊s⌋ : ℝ) - ⌊s'⌋| := by exact_mod_cast h4
  have a1 := Int.floor_le s
  have a2 := Int.lt_floor_add_one s
  have b1 := Int.floor_le s'
  have b2 := Int.lt_floor_add_one s'
  rcases le_abs'.1 h4' with h | h <;> [rw [abs_sub_comm]; skip] <;>
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)

theorem card_filter_le_four_mul {S : Finset ℝ} (hS : Separated S) (τ : ℝ → ℝ)
    (hτ : ∀ s ∈ S, |τ s - s| ≤ 1) (p : ℝ → Prop) [DecidablePred p] {B : ℝ}
    (hB : ∀ T : Finset ℝ, Separated T → (∀ t ∈ T, ∃ s ∈ S, τ s = t ∧ p s) → (T.card : ℝ) ≤ B) :
    ((S.filter p).card : ℝ) ≤ 4 * B := by
  classical
  have hsplit : (S.filter p).card = ∑ r ∈ Finset.range 4,
      ((S.filter p).filter fun s => ⌊s⌋ % 4 = r).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext s
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨hs, hp⟩
        refine ⟨(⌊s⌋ % 4).toNat, ?_, ⟨hs, hp⟩, ?_⟩
        · have := Int.emod_lt_of_pos ⌊s⌋ (by norm_num : (0 : ℤ) < 4); omega
        · have := Int.emod_nonneg ⌊s⌋ (by norm_num : (4 : ℤ) ≠ 0); omega
      · rintro ⟨r, -, h, -⟩; exact h
    · intro r _ r' _ hrr'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro s h1 h2
      exact hrr' (by have := (Finset.mem_filter.1 h1).2; have := (Finset.mem_filter.1 h2).2; omega)
  rw [hsplit, Nat.cast_sum]
  have : ∀ r ∈ Finset.range 4, ((((S.filter p).filter fun s => ⌊s⌋ % 4 = r).card : ℕ) : ℝ) ≤ B := by
    intro r _
    set Sr := (S.filter p).filter fun s => ⌊s⌋ % 4 = r
    have hmem : ∀ s ∈ Sr, s ∈ S ∧ p s ∧ ⌊s⌋ % 4 = r := fun s hs => by
      simp only [Sr, Finset.mem_filter] at hs; exact ⟨hs.1.1, hs.1.2, hs.2⟩
    have hinj : Set.InjOn τ Sr := by
      intro s hs s' hs' h
      by_contra hne
      obtain ⟨a1, -, a3⟩ := hmem s hs
      obtain ⟨b1, -, b3⟩ := hmem s' hs'
      have h3 := sep_of_mod4 hS a1 b1 hne (a3.trans b3.symm)
      have := hτ s a1
      have := hτ s' b1
      have : |s - s'| ≤ 2 := by
        have e : s - s' = (τ s' - s') - (τ s - s) := by rw [h]; ring
        rw [e]; exact (abs_sub _ _).trans (by linarith)
      linarith
    rw [← Finset.card_image_of_injOn hinj]
    refine hB _ ?_ ?_
    · intro t ht t' ht' hne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht'
      have hss : s ≠ s' := fun h => hne (by rw [h])
      obtain ⟨a1, -, a3⟩ := hmem s hs
      obtain ⟨b1, -, b3⟩ := hmem s' hs'
      have h3 := sep_of_mod4 hS a1 b1 hss (a3.trans b3.symm)
      have := hτ s a1
      have := hτ s' b1
      have e : s - s' = (τ s - τ s') - (τ s - s) + (τ s' - s') := by ring
      have : |s - s'| ≤ |τ s - τ s'| + 2 := by
        rw [e]
        calc |τ s - τ s' - (τ s - s) + (τ s' - s')|
            ≤ |τ s - τ s' - (τ s - s)| + |τ s' - s'| := abs_add_le _ _
          _ ≤ |τ s - τ s'| + |τ s - s| + |τ s' - s'| := by
              gcongr; exact abs_sub _ _
          _ ≤ _ := by linarith
      linarith
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
      exact ⟨s, (hmem s hs).1, rfl, (hmem s hs).2.1⟩
  calc ∑ r ∈ Finset.range 4, ((((S.filter p).filter fun s => ⌊s⌋ % 4 = r).card : ℕ) : ℝ)
      ≤ ∑ r ∈ Finset.range 4, B := Finset.sum_le_sum this
    _ = 4 * B := by simp

end Erdos385.Parseval

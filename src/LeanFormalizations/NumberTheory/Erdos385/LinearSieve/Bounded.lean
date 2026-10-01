/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.UpperAt
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Normalized

/-!
# Boundedness and monotonicity of the normalised upper function `bUp` (phase E5)

`bSeq_bdd`: the limsup defining `bUp s` is of an eventually bounded sequence (Selberg via
`upperAt_of_theta` at level `s + 1`), so `bUp` is not a junk value; `bUp_mono'`: `bUp` is monotone.
-/

namespace LeanFormalizations.Erdos385.LinearSieve
open Filter

lemma siftMax_anti_z (N : ℕ) {z z' : ℕ} (h : z ≤ z') : siftMax N z' ≤ siftMax N z := by
  obtain ⟨lo, r, hr⟩ := Nat.sSup_mem (s := {c | ∃ lo r, c = sift lo N r z'})
    ⟨_, 0, fun _ => 0, rfl⟩ (bddAbove_sift N z')
  change siftMax N z' = _ at hr
  rw [hr]
  exact (sift_anti_z lo N r h).trans (le_siftMax lo N r z)

/-- The normalised upper sequence at level `s`. -/
noncomputable def bSeq (s : ℝ) (N : ℕ) : ℝ :=
  (siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N

lemma bSeq_nonneg (s : ℝ) (N : ℕ) : 0 ≤ bSeq s N := by
  unfold bSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg this
    positivity

/-- `b`'s sequence is eventually bounded at every level `s > 0`. -/
theorem bSeq_bdd {s : ℝ} (hs : 0 < s) : IsBoundedUnder (· ≤ ·) atTop (bSeq s) := by
  set θ : ℝ := 1 / (2 * (s + 2)) with hθ
  have hθpos : 0 < θ := by positivity
  have hθhalf : θ < 1 / 2 := by
    rw [hθ, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hθs : θ * (s + 1) < 1 := by
    rw [hθ, div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
  obtain ⟨N₀, hN₀⟩ := upperAt_of_theta (s := s + 1) (θ := θ) (θ' := θ / 2) (δ := 1)
    (by linarith) (by positivity) (by linarith) hθhalf hθs one_pos
  -- eventually `N^{1/(s+1)} ≤ ⌊N^{1/s}⌋`
  have hgap : 0 < 1 / s - 1 / (s + 1) := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt hs (by linarith)
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / s - 1 / (s + 1)) :=
    ((tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  refine ⟨1 / (θ / 2) + 1 / 4, eventually_atTop.mpr ⟨max (max N₀ N₁) 1, fun N hN => ?_⟩⟩
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hz : (N : ℝ) ^ (1 / (s + 1)) ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
    have hA : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (s + 1)) := Real.one_le_rpow h1 (by positivity)
    have hsplit : (N : ℝ) ^ (1 / s) = (N : ℝ) ^ (1 / s - 1 / (s + 1)) * (N : ℝ) ^ (1 / (s + 1)) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have := Nat.sub_one_lt_floor ((N : ℝ) ^ (1 / s))
    rw [hsplit] at this ⊢
    have hB := hN₁ N hN1
    nlinarith [mul_le_mul_of_nonneg_right hB (by linarith : (0:ℝ) ≤ (N : ℝ) ^ (1 / (s + 1)))]
  have hb := hN₀ N hN0 _ hz
  show bSeq s N ≤ _
  unfold bSeq
  rw [div_le_iff₀ hNpos]
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h]; simp; positivity
  · have hlog : 0 < Real.log N := Real.log_pos h
    rw [le_div_iff₀ hlog] at hb
    nlinarith

/-- **`b` is monotone** on `(0, ∞)`. -/
theorem bUp_mono' : MonotoneOn bUp (Set.Ioi 0) := by
  intro s hs s' hs' hss'
  have hs0 : (0 : ℝ) < s := hs
  change limsup (bSeq s) atTop ≤ limsup (bSeq s') atTop
  refine limsup_le_limsup (Eventually.of_forall fun N => ?_)
    (isCoboundedUnder_le_of_le atTop (bSeq_nonneg s)) (bSeq_bdd hs')
  unfold bSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg h1
  have hfl : ⌊(N : ℝ) ^ (1 / s')⌋₊ ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le h1 (one_div_le_one_div_of_le hs0 hss'))
  have := siftMax_anti_z N hfl
  have : (siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ siftMax N ⌊(N : ℝ) ^ (1 / s')⌋₊ := by
    exact_mod_cast this
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hlog) (by positivity)

/-- The normalised lower sequence at level `s`. -/
noncomputable def aSeq (s : ℝ) (N : ℕ) : ℝ :=
  (siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N

lemma aSeq_nonneg (s : ℝ) (N : ℕ) : 0 ≤ aSeq s N := by
  unfold aSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg this
    positivity

lemma aSeq_le_bSeq (s : ℝ) (N : ℕ) : aSeq s N ≤ bSeq s N := by
  unfold aSeq bSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg this
  obtain ⟨lo, r, hr⟩ := exists_sift_eq_siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊
  have h : (siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
    rw [← hr]; exact_mod_cast le_siftMax lo N r _
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hlog) (by positivity)

lemma aSeq_cobdd {s : ℝ} (hs : 0 < s) : IsCoboundedUnder (· ≥ ·) atTop (aSeq s) := by
  obtain ⟨B, hB⟩ := bSeq_bdd hs
  exact isCoboundedUnder_ge_of_eventually_le atTop
    ((eventually_map.mp hB).mono fun N h => (aSeq_le_bSeq s N).trans h)

theorem aLow_nonneg' {s : ℝ} (hs : 0 < s) : 0 ≤ aLow s :=
  le_liminf_of_le (aSeq_cobdd hs) (Eventually.of_forall (aSeq_nonneg s))

theorem aLow_mono' : MonotoneOn aLow (Set.Ioi 0) := by
  intro s hs s' hs' hss'
  have hs0 : (0 : ℝ) < s := hs
  change liminf (aSeq s) atTop ≤ liminf (aSeq s') atTop
  refine liminf_le_liminf (Eventually.of_forall fun N => ?_)
    (isBoundedUnder_of ⟨0, aSeq_nonneg s⟩) (aSeq_cobdd hs')
  unfold aSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg h1
  have hfl : ⌊(N : ℝ) ^ (1 / s')⌋₊ ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le h1 (one_div_le_one_div_of_le hs0 hss'))
  have : (siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ siftMin N ⌊(N : ℝ) ^ (1 / s')⌋₊ := by
    exact_mod_cast siftMin_anti_z N hfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hlog) (by positivity)

end LeanFormalizations.Erdos385.LinearSieve

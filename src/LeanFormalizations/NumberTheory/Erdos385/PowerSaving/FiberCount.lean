/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Cover

/-!
# Erdős #385 power saving: counting separated points by fibres (phase E9b, transport)

* `sep_card_window`: `1`-separated points in a window `[c − W, c + W]` number `≤ 2W + 1`;
* `sep_card_fiber`: if each `t ∈ T` has `ρ_t ∈ S` with `abs(|t| − Im ρ_t) ≤ W`, then
  `#T ≤ 2 (2W + 1) #S`.
-/

namespace LeanFormalizations.Erdos385

open Erdos385.Parseval

lemma sep_card_window {S : Finset ℝ} (hS : Separated S) {c W : ℝ} (hW : 0 ≤ W)
    (h : ∀ s ∈ S, |s - c| ≤ W) : (S.card : ℝ) ≤ 2 * W + 1 := by
  have hinj : S.card ≤ (Finset.Icc (0 : ℤ) ⌊2 * W⌋).card := by
    refine Finset.card_le_card_of_injOn (fun s => ⌊s - (c - W)⌋) (fun s hs => ?_)
      (fun s hs s' hs' he => ?_)
    · have := abs_le.1 (h s hs)
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨Int.floor_nonneg.2 (by linarith), Int.floor_mono (by linarith)⟩
    · by_contra hne
      have h1 := hS s hs s' hs' hne
      have a1 := Int.floor_le (s - (c - W))
      have a2 := Int.lt_floor_add_one (s - (c - W))
      have b1 := Int.floor_le (s' - (c - W))
      have b2 := Int.lt_floor_add_one (s' - (c - W))
      simp only at he
      rw [he] at a1 a2
      have : |s - s'| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
      linarith
  have hc : ((Finset.Icc (0 : ℤ) ⌊2 * W⌋).card : ℝ) = ⌊2 * W⌋ + 1 := by
    rw [Int.card_Icc]
    have : (0 : ℤ) ≤ ⌊2 * W⌋ + 1 - 0 := by have := Int.floor_nonneg.2 (by linarith : 0 ≤ 2 * W)
                                           omega
    rw [show ((⌊2 * W⌋ + 1 - 0).toNat : ℝ) = ((⌊2 * W⌋ + 1 - 0 : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg this]
    push_cast; ring
  calc (S.card : ℝ) ≤ (Finset.Icc (0 : ℤ) ⌊2 * W⌋).card := by exact_mod_cast hinj
    _ = ⌊2 * W⌋ + 1 := hc
    _ ≤ 2 * W + 1 := by linarith [Int.floor_le (2 * W)]

lemma separated_mono {S S' : Finset ℝ} (h : S' ⊆ S) (hS : Separated S) : Separated S' :=
  fun s hs s' hs' hne => hS s (h hs) s' (h hs') hne

lemma sep_card_fiber {T : Finset ℝ} (hT : Separated T) {S : Finset ℂ} {W : ℝ} (hW : 0 ≤ W)
    (f : ℝ → ℂ) (hf : ∀ t ∈ T, f t ∈ S ∧ abs (|t| - (f t).im) ≤ W) :
    (T.card : ℝ) ≤ 2 * (2 * W + 1) * S.card := by
  classical
  have hsum := Finset.card_eq_sum_card_fiberwise (f := f) (s := T) (t := S) (fun t ht => (hf t ht).1)
  have hfib : ∀ ρ ∈ S, ((T.filter fun t => f t = ρ).card : ℝ) ≤ 2 * (2 * W + 1) := by
    intro ρ _
    set F := T.filter fun t => f t = ρ
    have hsplit : F = F.filter (fun t => 0 ≤ t) ∪ F.filter (fun t => ¬ 0 ≤ t) :=
      (Finset.filter_union_filter_not_eq _ _).symm
    have hFsep : Separated F := separated_mono (Finset.filter_subset _ _) hT
    have h1 : ((F.filter (fun t => 0 ≤ t)).card : ℝ) ≤ 2 * W + 1 := by
      refine sep_card_window (separated_mono (Finset.filter_subset _ _) hFsep) (c := ρ.im) hW
        fun s hs => ?_
      simp only [F, Finset.mem_filter] at hs
      have := (hf s hs.1.1).2
      rw [hs.1.2, abs_of_nonneg hs.2] at this; exact this
    have h2 : ((F.filter (fun t => ¬ 0 ≤ t)).card : ℝ) ≤ 2 * W + 1 := by
      refine sep_card_window (separated_mono (Finset.filter_subset _ _) hFsep) (c := -ρ.im) hW
        fun s hs => ?_
      simp only [F, Finset.mem_filter] at hs
      have := (hf s hs.1.1).2
      rw [hs.1.2, abs_of_neg (not_le.1 hs.2)] at this
      rw [show s - -ρ.im = -(-s - ρ.im) by ring, abs_neg]; exact this
    have hle := Finset.card_union_le (F.filter (fun t => 0 ≤ t)) (F.filter (fun t => ¬ 0 ≤ t))
    rw [← hsplit] at hle
    have : (F.card : ℝ) ≤ ((F.filter (fun t => 0 ≤ t)).card : ℝ) +
        ((F.filter (fun t => ¬ 0 ≤ t)).card : ℝ) := by exact_mod_cast hle
    linarith
  rw [hsum]
  push_cast
  calc ∑ ρ ∈ S, ((T.filter fun t => f t = ρ).card : ℝ) ≤ ∑ _ρ ∈ S, 2 * (2 * W + 1) :=
        Finset.sum_le_sum hfib
    _ = 2 * (2 * W + 1) * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end LeanFormalizations.Erdos385

namespace LeanFormalizations.Erdos385

open Erdos385.Parseval

/-- `sep_card_fiber` with the fibre map given existentially. -/
lemma sep_card_fiber' {T : Finset ℝ} (hT : Separated T) {S : Finset ℂ} {W : ℝ} (hW : 0 ≤ W)
    (hf : ∀ t ∈ T, ∃ ρ ∈ S, abs (|t| - ρ.im) ≤ W) :
    (T.card : ℝ) ≤ 2 * (2 * W + 1) * S.card := by
  classical
  let f : ℝ → ℂ := fun t => if h : ∃ ρ ∈ S, abs (|t| - ρ.im) ≤ W then h.choose else 0
  refine sep_card_fiber hT hW f fun t ht => ?_
  have h := hf t ht
  simp only [f, dif_pos h]
  exact h.choose_spec

end LeanFormalizations.Erdos385

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional

/-!
# Erdős #385, phase E8: a short window of positions coprime to the small primes

By the linear-sieve lower bound on `(Y/2, Y]` with sifting range `Y^{4/9} ≥ y`, at least
`c Y / log Y` positions `a` have `a ≢ s (mod p)` for every prime `p ≤ y`; splitting `(Y/2, Y]` into
`≤ 2Y/y` blocks of length `y`, one block holds `≥ (c/2) y / log Y` of them (`exists_window`).
The window replaces the fixed window `[1, y]` of `Exceptional.lean`, whose population has no
deterministic lower bound.
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open LeanFormalizations.Literature Finset

theorem exists_window (h2 : LinearSieveIntervalLower) : ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℕ, ∀ y Y : ℕ,
    y₀ ≤ y → (y : ℝ) ≤ (Y : ℝ) ^ ((4 : ℝ) / 9) → ∀ s : ℕ, ∃ A : Finset ℕ,
      c * y / Real.log Y ≤ A.card ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ Y) ∧
      (∀ a ∈ A, ∀ p, p.Prime → p ≤ y → s % p ≠ a % p) ∧ (∀ a ∈ A, ∀ b ∈ A, b < a + y) := by
  classical
  obtain ⟨c0, hc0, Y₀, hY₀⟩ := h2 (1 / 18) (by norm_num)
  refine ⟨c0 / 2, by positivity, max Y₀ 2, fun y Y hy hyY s => ?_⟩
  have hy2 : 2 ≤ y := le_of_max_le_right hy
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  -- `y ≤ Y`
  have hYpos : (0 : ℝ) < Y := by
    by_contra h
    push_neg at h
    have hY0 : (Y : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [hY0, Real.zero_rpow (by norm_num)] at hyY
    linarith
  have hY1 : (1 : ℝ) ≤ Y := by
    have : 0 < Y := by exact_mod_cast hYpos
    exact_mod_cast this
  have hyYle : (y : ℝ) ≤ Y := hyY.trans (Real.rpow_le_self_of_one_le hY1 (by norm_num))
  have hyYn : y ≤ Y := by exact_mod_cast hyYle
  have hYY0 : Y₀ ≤ Y := (le_of_max_le_left hy).trans hyYn
  have hG := hY₀ Y hYY0 (fun _ => s)
  set G := (Ioc (Y / 2) Y).filter fun a =>
    ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2 - 1 / 18) → a % q ≠ s % q with hGdef
  have hset : {a : ℕ | Y / 2 < a ∧ a ≤ Y ∧
      ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2 - 1 / 18) → a % q ≠ s % q} = ↑G := by
    ext a; simp [hGdef, and_assoc]
  rw [hset, Set.ncard_coe_finset] at hG
  set f : ℕ → ℕ := fun a => (a - (Y / 2 + 1)) / y
  set t := range (Y / y + 1)
  have hft : ∀ a ∈ G, f a ∈ t := by
    intro a ha
    have := (mem_Ioc.1 (mem_filter.1 ha).1).2
    exact mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  set b : ℝ := c0 / 2 * y / Real.log Y
  have htcard : ((t.card : ℕ) : ℝ) ≤ 2 * Y / y := by
    simp only [t, card_range]
    push_cast
    have h1 : ((Y / y : ℕ) : ℝ) ≤ (Y : ℝ) / y := Nat.cast_div_le
    have h2 : (1 : ℝ) ≤ Y / y := by rw [le_div_iff₀ (by linarith)]; linarith
    have h3 : 2 * (Y : ℝ) / y = Y / y + Y / y := by ring
    linarith
  have hb : t.card • b ≤ (G.card : ℝ) := by
    rw [nsmul_eq_mul]
    calc (t.card : ℝ) * b ≤ 2 * Y / y * b := by gcongr
      _ = c0 * Y / Real.log Y := by simp only [b]; field_simp
      _ ≤ _ := hG
  obtain ⟨i, -, hi⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hft
    ⟨0, mem_range.2 (Nat.succ_pos _)⟩ hb
  refine ⟨G.filter (f · = i), hi, fun a ha => ?_, fun a ha p hp hpy => ?_, fun a ha a' ha' => ?_⟩
  · have := mem_Ioc.1 (mem_filter.1 (mem_filter.1 ha).1).1; omega
  · have hq := (mem_filter.1 (mem_filter.1 ha).1).2 p hp (by
      have : (p : ℝ) ≤ y := by exact_mod_cast hpy
      calc (p : ℝ) ≤ y := this
        _ ≤ (Y : ℝ) ^ ((4 : ℝ) / 9) := hyY
        _ = (Y : ℝ) ^ ((1 : ℝ) / 2 - 1 / 18) := by norm_num)
    exact fun h => hq h.symm
  · obtain ⟨hG1, hf1⟩ := mem_filter.1 ha
    obtain ⟨hG2, hf2⟩ := mem_filter.1 ha'
    have hI1 := mem_Ioc.1 (mem_filter.1 hG1).1
    have hI2 := mem_Ioc.1 (mem_filter.1 hG2).1
    have hypos : 0 < y := by omega
    have e1 := Nat.div_add_mod (a - (Y / 2 + 1)) y
    have e2 := Nat.div_add_mod (a' - (Y / 2 + 1)) y
    have m1 := Nat.mod_lt (a - (Y / 2 + 1)) hypos
    have m2 := Nat.mod_lt (a' - (Y / 2 + 1)) hypos
    simp only [f] at hf1 hf2
    rw [hf1] at e1; rw [hf2] at e2
    omega

end LeanFormalizations.Erdos385.QuasiPower

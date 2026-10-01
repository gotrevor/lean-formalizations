/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Buchstab

/-!
# Normalised extremal sieve functions (phase E5)

`aLow s = liminf_N S⁻(N, ⌊N^{1/s}⌋) log N / N`, `bUp s = limsup_N S⁺(N, ⌊N^{1/s}⌋) log N / N`.
`lower_of_aLow_pos`: `a(s) > 0` gives the crux's normal form `LowerAt`.  Positivity for `s > 2`
(`Leaves.aLow_pos_of_leaves`) is the Jurkat–Richert lower bound `a(s) ≥ 2 log(s−1) · (const)`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Filter

/-- Sifting more primes leaves fewer survivors. -/
lemma sift_anti_z (lo : ℤ) (N : ℕ) (r : ℕ → ℤ) {z z' : ℕ} (h : z ≤ z') :
    sift lo N r z' ≤ sift lo N r z := by
  classical
  unfold sift
  refine Finset.card_le_card fun k hk => ?_
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, fun q hq hqz => hk.2 q hq (lt_of_lt_of_le hqz h)⟩

lemma siftMin_anti_z (N : ℕ) {z z' : ℕ} (h : z ≤ z') : siftMin N z' ≤ siftMin N z := by
  obtain ⟨lo, r, hr⟩ := exists_sift_eq_siftMin N z
  rw [← hr]
  exact (siftMin_le lo N r z').trans (sift_anti_z lo N r h)

/-- Normalised lower sieve function. -/
noncomputable def aLow (s : ℝ) : ℝ :=
  liminf (fun N : ℕ => (siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N) atTop

/-- Normalised upper sieve function. -/
noncomputable def bUp (s : ℝ) : ℝ :=
  limsup (fun N : ℕ => (siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N) atTop

/-- The crux follows from `aLow_pos` by monotonicity in the sifting limit. -/
theorem siftMin_lower_of_aLow_pos (ha : ∀ s : ℝ, 2 < s → 0 < aLow s) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ z : ℕ, (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - ε) → c * N / Real.log N ≤ siftMin N z := by
  intro ε hε
  set ε0 := min ε (1 / 4)
  have hε0 : 0 < ε0 := lt_min hε (by norm_num)
  have hε0q : ε0 ≤ 1 / 4 := min_le_right _ _
  set s : ℝ := 1 / (1 / 2 - ε0) with hs
  have hpos : 0 < 1 / 2 - ε0 := by linarith
  have hs2 : 2 < s := by
    rw [hs, lt_div_iff₀ hpos]; linarith
  have h1s : 1 / s = 1 / 2 - ε0 := by rw [hs, one_div_one_div]
  have hA := ha s hs2
  have hev := eventually_lt_of_lt_liminf (show aLow s / 2 < aLow s by linarith)
    (isBoundedUnder_of ⟨0, fun N => by positivity⟩)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨aLow s / 2, by positivity, max N1 2, fun N hN z hz => ?_⟩
  have hN1' := hN1 N ((le_max_left _ _).trans hN)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have hzle : z ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
    apply Nat.le_floor
    rw [h1s]
    refine hz.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_)
    linarith [min_le_left ε (1 / 4 : ℝ)]
  have hmono : (siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ siftMin N z := by
    exact_mod_cast siftMin_anti_z N hzle
  have key : aLow s / 2 * N / Real.log N ≤ siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
    rw [div_le_iff₀ hlog]
    have := hN1'.le
    rw [le_div_iff₀ hNpos] at this
    linarith
  linarith

/-- From `a(s) > 0`: a uniform lower constant for every `z ≤ N^{1/s}`. -/
theorem lower_of_aLow_pos {s : ℝ} (hs : 0 < s) (ha : 0 < aLow s) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z : ℕ, (z : ℝ) ≤ (N : ℝ) ^ (1 / s) →
      c * N / Real.log N ≤ siftMin N z := by
  have hev := eventually_lt_of_lt_liminf (show aLow s / 2 < aLow s by linarith)
    (isBoundedUnder_of ⟨0, fun N => by positivity⟩)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨aLow s / 2, by positivity, max N1 2, fun N hN z hz => ?_⟩
  have hN1' := hN1 N ((le_max_left _ _).trans hN)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have hzle : z ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ := Nat.le_floor hz
  have hmono : (siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ siftMin N z := by
    exact_mod_cast siftMin_anti_z N hzle
  have key : aLow s / 2 * N / Real.log N ≤ siftMin N ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
    rw [div_le_iff₀ hlog]
    have := hN1'.le
    rw [le_div_iff₀ hNpos] at this
    linarith
  linarith

end LeanFormalizations.Erdos385.LinearSieve

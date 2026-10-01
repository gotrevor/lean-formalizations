/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Rate

/-!
# Erdős #385 power saving: from windows to the global count (phase E9b)

`almost_all_of_badWindowPowerSaving`: a per-window power saving
`#badWindow δ Z ≤ A Z^{1−c'}` gives `#{n ≤ X : F(n) < n + (1 − δ)√n} ≤ C X^{1−c}`.
Same covering as `Gen.almost_all_F385_rate` (`card_le_of_windows`, head `n < 2√X` split off),
with `η = A (√X)^{−c'}` and `c = min(c'/2, 1/2)`.
-/

namespace LeanFormalizations.Erdos385

open Real

/-- Per-window power saving for the δ-exceptional set. -/
def BadWindowPowerSaving (δ : ℝ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∃ A : ℝ, 0 < A ∧ ∃ Z₁ : ℝ, 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
    ((badWindow δ Z).ncard : ℝ) ≤ A * Z ^ (1 - c')

theorem almost_all_of_badWindowPowerSaving {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (h : BadWindowPowerSaving δ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * (X : ℝ) ^ (1 - c) := by
  classical
  obtain ⟨c', hc', A, hA, Z₁, hZ₁1, hwin⟩ := h
  obtain ⟨N₀, hcov⟩ := card_le_of_windows hδ hδ' Z₁
  set c := min (c' / 2) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  refine ⟨c, (3 + N₀) + A * (1 + 4 / δ), hc0, fun X hX => ?_⟩
  set E : Set ℕ := {n | (F n : ℝ) < n + (1 - δ) * √n} with hE
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hX0 : (0 : ℝ) < X := by linarith
  set Φ := (X : ℝ) ^ (1 - c) with hΦ
  have hsqΦ : √X ≤ Φ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hXr (by linarith [min_le_right (c' / 2) (1 / 2 : ℝ)])
  have hs1 : 1 ≤ √X := by rw [Real.one_le_sqrt]; exact hXr
  have hΦ1 : 1 ≤ Φ := hs1.trans hsqΦ
  have hrest : 0 ≤ A * (1 + 4 / δ) * Φ := by positivity
  show (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤ _
  by_cases hXN : X < N₀
  · have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆ ↑(Finset.range (X + 1)) := fun n hn => by
      simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_succ_of_le hn.1
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_range] at this
    have hc : (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤ N₀ := by exact_mod_cast (by omega)
    have : (N₀ : ℝ) ≤ N₀ * Φ := le_mul_of_one_le_right (by positivity) hΦ1
    nlinarith
  push Not at hXN
  set E' : Set ℕ := {n | n ∈ E ∧ 2 * √X ≤ n} with hE'
  have hsX0 : 0 < √X := by positivity
  set η := A * (√X) ^ (-c') with hη
  have hη0 : 0 < η := by positivity
  have hW : ∀ Z : ℝ, Z₁ ≤ Z →
      ({n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℝ) ≤ η * Z := by
    intro Z hZ
    have hZ0 : 0 < Z := by linarith
    by_cases hZs : Z < √X
    · have : {n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z} = ∅ := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hE']
        rintro ⟨⟨_, h2⟩, _, h3⟩
        nlinarith
      rw [this, Set.ncard_empty, Nat.cast_zero]; positivity
    · push Not at hZs
      have hsub : {n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z} ⊆
          badWindow δ Z := fun n ⟨⟨hn, _⟩, h1, h2⟩ => ⟨h1, h2, hn⟩
      have hfin : (badWindow δ Z).Finite :=
        (Set.finite_Iic ⌊(1 + δ / 2) * Z⌋₊).subset fun n hn => by
          simp only [Set.mem_Iic]; exact Nat.le_floor hn.2.1
      have h1 : ((({n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℕ)
          : ℝ)) ≤ (badWindow δ Z).ncard := by exact_mod_cast Set.ncard_le_ncard hsub hfin
      have hpow : Z ^ (1 - c') = Z * Z ^ (-c') := by
        rw [sub_eq_add_neg, Real.rpow_add hZ0, Real.rpow_one]
      have hmono : Z ^ (-c') ≤ (√X) ^ (-c') :=
        Real.rpow_le_rpow_of_nonpos hsX0 hZs (by linarith)
      calc _ ≤ ((badWindow δ Z).ncard : ℝ) := h1
        _ ≤ A * Z ^ (1 - c') := hwin Z hZ
        _ = A * (Z * Z ^ (-c')) := by rw [hpow]
        _ ≤ A * (Z * (√X) ^ (-c')) := by gcongr
        _ = η * Z := by rw [hη]; ring
  have hcnt := hcov E' η hη0 hW X hXN
  -- η X ≤ A Φ
  have hηΦ : η * X ≤ A * Φ := by
    rw [hη, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le, hΦ]
    calc (X : ℝ) ^ (1 / 2 * -c') * X = (X : ℝ) ^ (1 - c' / 2) := by
          rw [show (1 : ℝ) - c' / 2 = 1 / 2 * -c' + 1 by ring, Real.rpow_add hX0, Real.rpow_one]
      _ ≤ (X : ℝ) ^ (1 - c) :=
          Real.rpow_le_rpow_of_exponent_le hXr (by linarith [min_le_left (c' / 2) (1 / 2 : ℝ)])
  have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆
      ↑(Finset.range ⌈2 * √X⌉₊) ∪ {n : ℕ | n ≤ X ∧ n ∈ E'} := by
    intro n ⟨hnX, hnE⟩
    by_cases hn : (n : ℝ) < 2 * √X
    · left; simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_ceil.2 hn
    · right; push Not at hn; exact ⟨hnX, hnE, hn⟩
  have hfin2 : {n : ℕ | n ≤ X ∧ n ∈ E'}.Finite :=
    (Set.finite_Iic X).subset fun n hn => hn.1
  have hA1 := Set.ncard_le_ncard hsub ((Finset.finite_toSet _).union hfin2)
  have hA2 := Set.ncard_union_le (↑(Finset.range ⌈2 * √X⌉₊) : Set ℕ) {n : ℕ | n ≤ X ∧ n ∈ E'}
  rw [Set.ncard_coe_finset, Finset.card_range] at hA2
  have hceil : (⌈2 * √X⌉₊ : ℝ) ≤ 2 * √X + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have htot : (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤
      ⌈2 * √X⌉₊ + ({n : ℕ | n ≤ X ∧ n ∈ E'}.ncard : ℝ) := by
    exact_mod_cast hA1.trans hA2
  have hηX : η * (1 + 4 / δ) * X ≤ A * (1 + 4 / δ) * Φ := by
    have : η * X * (1 + 4 / δ) ≤ A * Φ * (1 + 4 / δ) :=
      mul_le_mul_of_nonneg_right hηΦ (by positivity)
    linarith
  have hN : (3 + (N₀ : ℝ)) * √X ≤ (3 + N₀) * Φ :=
    mul_le_mul_of_nonneg_left hsqΦ (by positivity)
  have hN' : 2 * √X + 1 + (N₀ : ℝ) ≤ (3 + N₀) * √X := by
    have : (0 : ℝ) ≤ N₀ := by positivity
    nlinarith
  nlinarith

end LeanFormalizations.Erdos385

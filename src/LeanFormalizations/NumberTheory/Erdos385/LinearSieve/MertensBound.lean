/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.GLower
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Mertens

/-!
# `Π(ξ) ≪ log ξ` (phase E5, step 1b)

`mertensP ξ = 1 / ∏_{p ≤ ξ}(1 − 1/p)`, and Mertens' third theorem (`mertens_third_tendsto_exp`)
gives `∏_{p≤ξ}(1−1/p) · log ξ → e^{C₃} > 0`, so eventually `Π(ξ) ≤ 2 e^{−C₃} log ξ`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset Filter

lemma mertensP_eq_inv (ξ : ℕ) : mertensP ξ = (LeanFormalizations.Mertens.primeProd ξ)⁻¹ := by
  unfold mertensP LeanFormalizations.Mertens.primeProd
  have hset : (range (ξ + 1)).filter Nat.Prime = (Ioc 0 ξ).filter Nat.Prime := by
    ext p; simp only [mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hset, ← prod_inv_distrib]
  refine prod_congr rfl fun p hp => ?_
  have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  field_simp

/-- **`Π(ξ) ≪ log ξ`.** -/
theorem mertensP_le_log : ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
    mertensP ξ ≤ C * Real.log ξ := by
  set L := Real.exp LeanFormalizations.Mertens.mertensThirdConst
  have hL : 0 < L := Real.exp_pos _
  have hev := LeanFormalizations.Mertens.mertens_third_tendsto_exp.eventually
    (Ioi_mem_nhds (show L / 2 < L by linarith))
  obtain ⟨ξ₀, hξ₀⟩ := eventually_atTop.mp hev
  refine ⟨2 / L, by positivity, ξ₀, fun ξ hξ => ?_⟩
  have h := hξ₀ ξ hξ
  have hP := LeanFormalizations.Mertens.primeProd_pos ξ
  rw [mertensP_eq_inv, inv_eq_one_div, div_le_iff₀ hP]
  have : 1 = 2 / L * (L / 2) := by field_simp
  rw [this]
  calc 2 / L * (L / 2) ≤ 2 / L * (LeanFormalizations.Mertens.primeProd ξ * Real.log ξ) :=
        mul_le_mul_of_nonneg_left h.le (by positivity)
    _ = _ := by ring

/-- **Selberg in usable form**: for `2 ≤ ξ < z` (and `ξ ≥ ξ₀`),
`S⁺(N, z) ≤ N / log ξ + (C ξ log ξ)²`. -/
theorem siftMax_le_log : ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℕ, ∀ N z ξ : ℕ, ξ₀ ≤ ξ → 2 ≤ ξ → ξ < z →
    (siftMax N z : ℝ) ≤ N / Real.log ξ + (C * ξ * Real.log ξ) ^ 2 := by
  obtain ⟨C, hC, ξ₀, hξ₀⟩ := mertensP_le_log
  refine ⟨C, hC, ξ₀, fun N z ξ hξ hξ2 hξz => ?_⟩
  have hlog : 0 < Real.log ξ := Real.log_pos (by exact_mod_cast hξ2)
  have h1 := siftMax_le_selberg N z ξ (by omega)
  have hG := log_le_selG hξz
  have hE := selE_le z ξ
  have hE0 : 0 ≤ selE z ξ := sum_nonneg fun d _ => prod_nonneg fun p hp => by
    have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (by linarith) (by linarith)
  have hE' : selE z ξ ≤ C * ξ * Real.log ξ := by
    calc selE z ξ ≤ ξ * mertensP ξ := hE
      _ ≤ ξ * (C * Real.log ξ) := mul_le_mul_of_nonneg_left (hξ₀ ξ hξ) (by positivity)
      _ = _ := by ring
  have h2 : (N : ℝ) / selG z ξ ≤ N / Real.log ξ :=
    div_le_div_of_nonneg_left (by positivity) hlog hG
  have h3 : selE z ξ ^ 2 ≤ (C * ξ * Real.log ξ) ^ 2 := pow_le_pow_left₀ hE0 hE' 2
  linarith

/-- **Explicit Selberg upper bound**: for `ξ₀ ≤ ξ < z`,
`S⁺(N, z) ≤ N / log ξ + (C ξ log ξ)²`. -/
theorem siftMax_le_explicit : ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℕ, 2 ≤ ξ₀ ∧ ∀ N z ξ : ℕ, ξ₀ ≤ ξ → ξ < z →
    (siftMax N z : ℝ) ≤ N / Real.log ξ + (C * ξ * Real.log ξ) ^ 2 := by
  obtain ⟨C, hC, ξ₁, hξ₁⟩ := mertensP_le_log
  refine ⟨C, hC, max ξ₁ 2, le_max_right _ _, fun N z ξ hξ hξz => ?_⟩
  have h2 : (2 : ℝ) ≤ ξ := by exact_mod_cast (le_max_right _ _).trans hξ
  have hlog : 0 < Real.log ξ := Real.log_pos (by linarith)
  have hG := log_le_selG hξz
  have hS := siftMax_le_selberg N z ξ (by omega)
  have hE0 : 0 ≤ selE z ξ := by
    unfold selE
    refine Finset.sum_nonneg fun d hd => Finset.prod_nonneg fun p hp => ?_
    have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (by linarith) (by linarith)
  have hE : selE z ξ ≤ C * ξ * Real.log ξ := by
    calc selE z ξ ≤ ξ * mertensP ξ := selE_le z ξ
      _ ≤ ξ * (C * Real.log ξ) :=
          mul_le_mul_of_nonneg_left (hξ₁ ξ ((le_max_left _ _).trans hξ)) (by linarith)
      _ = _ := by ring
  have h1 : (N : ℝ) / selG z ξ ≤ N / Real.log ξ :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlog hG
  have h3 : selE z ξ ^ 2 ≤ (C * ξ * Real.log ξ) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  linarith

end LeanFormalizations.Erdos385.LinearSieve

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

end LeanFormalizations.Erdos385.LinearSieve

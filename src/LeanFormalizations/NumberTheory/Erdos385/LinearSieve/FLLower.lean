/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Rankin
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.MertensBound

/-!
# Fundamental lemma, lower half (phase E5, step 3(d); session A)

Route: Buchstab from `w = 2`, `S⁻(N,z) ≥ N − Σ_{p<z} S⁺(N/p+1, p)`; the uniform upper
fundamental lemma (hypothesis, session B's step (b)) on each term; the main terms telescope
(`sum_Vw_div`: `Σ_{p<z} V(p)/p = 1 − V(z)`), the errors are summed dyadically in
`u = log N / log p` using `V(p) ≤ A V(z) log z / log p` (`primeProd_log_bounds`).
-/

namespace LeanFormalizations.Erdos385.LinearSieve
open Finset Filter

/-- `V(w) = ∏_{p < w} (1 − 1/p)`. -/
noncomputable def Vw (w : ℕ) : ℝ := LeanFormalizations.Mertens.primeProd (w - 1)

lemma Vw_succ (w : ℕ) (hw : 1 ≤ w) :
    Vw (w + 1) = if w.Prime then Vw w * (1 - (w : ℝ)⁻¹) else Vw w := by
  unfold Vw LeanFormalizations.Mertens.primeProd
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) by
    ext x; simp only [mem_Ioc, mem_insert]; omega, filter_insert]
  split_ifs with hp
  · rw [prod_insert (by simp), mul_comm]
  · rfl

lemma Vw_two : Vw 2 = 1 := by
  simp [Vw, LeanFormalizations.Mertens.primeProd]
  rfl

/-- **Telescoping**: `Σ_{2 ≤ p < z} V(p)/p = 1 − V(z)`. -/
theorem sum_Vw_div (z : ℕ) (hz : 2 ≤ z) :
    ∑ p ∈ (Ico 2 z).filter Nat.Prime, Vw p / p = 1 - Vw z := by
  induction z, hz using Nat.le_induction with
  | base => simp [Vw_two]
  | succ n hn ih =>
    rw [Nat.Ico_succ_right_eq_insert_Ico hn, filter_insert, Vw_succ n (by omega)]
    split_ifs with hp
    · rw [sum_insert (by simp), ih]
      have : (n : ℝ) ≠ 0 := by have := hp.pos; positivity
      field_simp; ring
    · exact ih

/-- A positive sequence converging to a positive limit is bounded above and below on `[n₀, ∞)`. -/
lemma uniform_bounds_of_tendsto {f : ℕ → ℝ} {L : ℝ} (hL : 0 < L) (hf : Tendsto f atTop (nhds L))
    (n₀ : ℕ) (hpos : ∀ n, n₀ ≤ n → 0 < f n) :
    ∃ A₁ A₂ : ℝ, 0 < A₂ ∧ ∀ n, n₀ ≤ n → A₂ ≤ f n ∧ f n ≤ A₁ := by
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (hf.eventually (Ioi_mem_nhds (half_lt_self hL)))
  obtain ⟨B, hB⟩ := hf.bddAbove_range
  set S := (Icc n₀ (max n₀ n₁)).image f
  have hS : S.Nonempty := by simp [S]
  have hmin : 0 < S.min' hS := by
    obtain ⟨n, hn, hfn⟩ := mem_image.mp (S.min'_mem hS)
    rw [← hfn]; exact hpos n (mem_Icc.mp hn).1
  refine ⟨B, min (S.min' hS) (L / 2), lt_min hmin (by linarith), fun n hn => ⟨?_, hB ⟨n, rfl⟩⟩⟩
  by_cases h : n ≤ max n₀ n₁
  · exact (min_le_left _ _).trans (S.min'_le _ (mem_image.mpr ⟨n, mem_Icc.mpr ⟨hn, h⟩, rfl⟩))
  · exact (min_le_right _ _).trans (hn₁ n (by omega)).le

/-- **Uniform Mertens**: `A₂ ≤ ∏_{p≤n}(1−1/p) · log n ≤ A₁` for `n ≥ 2`. -/
theorem primeProd_log_bounds : ∃ A₁ A₂ : ℝ, 0 < A₂ ∧ ∀ n : ℕ, 2 ≤ n →
    A₂ ≤ LeanFormalizations.Mertens.primeProd n * Real.log n ∧
      LeanFormalizations.Mertens.primeProd n * Real.log n ≤ A₁ :=
  uniform_bounds_of_tendsto (Real.exp_pos _) LeanFormalizations.Mertens.mertens_third_tendsto_exp 2
    fun n hn => mul_pos (LeanFormalizations.Mertens.primeProd_pos n)
      (Real.log_pos (by exact_mod_cast hn))

end LeanFormalizations.Erdos385.LinearSieve

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Rankin
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.MertensBound

/-!
# The uniform upper fundamental lemma (phase E5, step 3)

With `ε = 8 / log w`, Rankin's bound and `∏_{p<w}(1 + p^ε/(p−1)) ≤ Π(w−1) e^K`
(`K = 8e⁸(1 + B/log 2)`, Mertens' first theorem) give, for every `w ≥ 2` and level `ξ`,
`G_w(ξ) ≥ Π(w−1)(1 − e^K ξ^{−ε})`, hence

`S⁺(M, w)·(1 − e^K ξ^{−8/log w}) ≤ M / Π(w−1) + E²`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset

/-- The Mertens-first constant `B` with `Σ_{p ≤ N} log p / p ≤ log N + B`. -/
noncomputable def mertB : ℝ := Real.log 4 + 5

lemma mertB_nonneg : 0 ≤ mertB := by
  unfold mertB; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith

/-- The Rankin constant `K = 8e⁸(1 + B/log 2)`. -/
noncomputable def rankK : ℝ := 8 * Real.exp 8 * (1 + mertB / Real.log 2)

lemma rankK_nonneg : 0 ≤ rankK := by
  unfold rankK
  have := mertB_nonneg
  have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  positivity

lemma exp_sub_one_le_mul_exp (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos y]

/-- `Σ_{p<w} log p / p ≤ log w + B`. -/
lemma sum_log_div_le {w : ℕ} (hw : 2 ≤ w) :
    ∑ p ∈ (range w).filter Nat.Prime, Real.log p / (p : ℝ) ≤ Real.log w + mertB := by
  have hset : (range w).filter Nat.Prime = (Ioc 0 (w - 1)).filter Nat.Prime := by
    ext p; simp only [mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  have h := LeanFormalizations.Mertens.primeSumDiv_le (N := w - 1) (by omega)
  rw [hset]
  refine h.trans ?_
  unfold mertB
  have : Real.log ((w - 1 : ℕ) : ℝ) ≤ Real.log w := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < w - 1 by omega))
    exact_mod_cast Nat.sub_le w 1
  linarith

/-- **Rankin's product, Mertens form**: `∏_{p<w}(1 + p^ε/(p−1)) ≤ Π(w−1) e^K` at `ε = 8/log w`. -/
theorem rankin_prod_le {w : ℕ} (hw : 2 ≤ w) :
    ∏ p ∈ (range w).filter Nat.Prime, (1 + (p : ℝ) ^ (8 / Real.log w) / ((p : ℝ) - 1)) ≤
      mertensP (w - 1) * Real.exp rankK := by
  set ε := 8 / Real.log w with hεdef
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hlog2 : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) (by exact_mod_cast hw)
  have hε : 0 ≤ ε := by positivity
  set x : ℕ → ℝ := fun p => ((p : ℝ) ^ ε - 1) / p
  have hfac : ∀ p ∈ (range w).filter Nat.Prime,
      1 + (p : ℝ) ^ ε / ((p : ℝ) - 1) ≤ (p : ℝ) / ((p : ℝ) - 1) * Real.exp (x p) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
    have hx := Real.add_one_le_exp (x p)
    have hpos : 0 < (p : ℝ) / ((p : ℝ) - 1) := div_pos (by linarith) (by linarith)
    have : 1 + (p : ℝ) ^ ε / ((p : ℝ) - 1) = (p : ℝ) / ((p : ℝ) - 1) * (x p + 1) := by
      have h0 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h0' : (p : ℝ) ≠ 0 := by linarith
      simp only [x]; field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hx hpos.le
  have hxle : ∀ p ∈ (range w).filter Nat.Prime, x p ≤ ε * Real.exp 8 * (Real.log p / p) := by
    intro p hp
    obtain ⟨hpw, hpp⟩ := mem_filter.mp hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have hlogpw : Real.log p ≤ Real.log w :=
      Real.log_le_log hp0 (by exact_mod_cast (mem_range.mp hpw).le)
    have hrp : (p : ℝ) ^ ε = Real.exp (ε * Real.log p) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
    have hεl : ε * Real.log p ≤ 8 := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hlogw]; nlinarith
    have h1 := exp_sub_one_le_mul_exp (ε * Real.log p)
    have h2 : Real.exp (ε * Real.log p) ≤ Real.exp 8 := Real.exp_le_exp.mpr hεl
    simp only [x]
    rw [hrp, div_le_iff₀ hp0]
    have : ε * Real.exp 8 * (Real.log p / p) * p = ε * Real.log p * Real.exp 8 := by
      field_simp
    rw [this]
    have := mul_nonneg hε hlogp
    nlinarith
  have hsum : ∑ p ∈ (range w).filter Nat.Prime, x p ≤ rankK := by
    calc ∑ p ∈ (range w).filter Nat.Prime, x p
        ≤ ∑ p ∈ (range w).filter Nat.Prime, ε * Real.exp 8 * (Real.log p / p) := sum_le_sum hxle
      _ = ε * Real.exp 8 * ∑ p ∈ (range w).filter Nat.Prime, Real.log p / p := by rw [mul_sum]
      _ ≤ ε * Real.exp 8 * (Real.log w + mertB) :=
          mul_le_mul_of_nonneg_left (sum_log_div_le hw) (by positivity)
      _ = 8 * Real.exp 8 * (1 + mertB / Real.log w) := by rw [hεdef]; field_simp
      _ ≤ rankK := by
          unfold rankK
          have := mertB_nonneg
          have : mertB / Real.log w ≤ mertB / Real.log 2 :=
            div_le_div_of_nonneg_left this (Real.log_pos (by norm_num)) hlog2
          gcongr
  have hMP : mertensP (w - 1) = ∏ p ∈ (range w).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1) := by
    unfold mertensP; rw [Nat.sub_add_cancel (by omega)]
  calc _ ≤ ∏ p ∈ (range w).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1) * Real.exp (x p)) := by
        refine prod_le_prod (fun p hp => ?_) hfac
        have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ p by linarith) ε
        have : 0 ≤ (p : ℝ) ^ ε / ((p : ℝ) - 1) := div_nonneg this (by linarith)
        linarith
    _ = mertensP (w - 1) * Real.exp (∑ p ∈ (range w).filter Nat.Prime, x p) := by
        rw [prod_mul_distrib, hMP, Real.exp_sum]
    _ ≤ mertensP (w - 1) * Real.exp rankK := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) ?_
        rw [hMP]; exact prod_nonneg fun p hp => by
          have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
          exact div_nonneg (by linarith) (by linarith)

/-- `Π(n) > 0`. -/
lemma mertensP_pos (n : ℕ) : 0 < mertensP n := by
  unfold mertensP
  exact prod_pos fun p hp => by
    have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
    exact div_pos (by linarith) (by linarith)

lemma selE_nonneg (z ξ : ℕ) : 0 ≤ selE z ξ := by
  unfold selE
  refine sum_nonneg fun d hd => prod_nonneg fun p hp => ?_
  have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact div_nonneg (by linarith) (by linarith)

/-- **Uniform upper fundamental lemma** (multiplicative form):
`S⁺(M, w)·(1 − e^K ξ^{−8/log w}) ≤ M/Π(w−1) + E_w(ξ)²`. -/
theorem siftMax_mul_le (M : ℕ) {w ξ : ℕ} (hw : 2 ≤ w) (hξ : 1 ≤ ξ) :
    (siftMax M w : ℝ) * (1 - Real.exp rankK * (ξ : ℝ) ^ (-(8 / Real.log w))) ≤
      M / mertensP (w - 1) + selE w ξ ^ 2 := by
  set η := Real.exp rankK * (ξ : ℝ) ^ (-(8 / Real.log w)) with hη
  set PP := mertensP (w - 1)
  have hPP : 0 < PP := mertensP_pos _
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hR := mertensP_sub_selG_le w ξ hξ (ε := 8 / Real.log w) (by positivity)
  have hP := rankin_prod_le hw
  have hξr : 0 ≤ (ξ : ℝ) ^ (-(8 / Real.log w)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hG : PP * (1 - η) ≤ selG w ξ := by
    have : (ξ : ℝ) ^ (-(8 / Real.log w)) *
        ∏ p ∈ (range w).filter Nat.Prime, (1 + (p : ℝ) ^ (8 / Real.log w) / ((p : ℝ) - 1)) ≤
        (ξ : ℝ) ^ (-(8 / Real.log w)) * (PP * Real.exp rankK) :=
      mul_le_mul_of_nonneg_left hP hξr
    rw [hη]; nlinarith
  have hS0 : (0 : ℝ) ≤ siftMax M w := Nat.cast_nonneg _
  have hE := sq_nonneg (selE w ξ)
  have hM0 : (0 : ℝ) ≤ M / PP := div_nonneg (Nat.cast_nonneg _) hPP.le
  rcases le_or_gt (1 - η) 0 with h | h
  · nlinarith
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hGpos : 0 < selG w ξ := lt_of_lt_of_le (mul_pos hPP h) hG
  have hS := siftMax_le_selberg M w ξ hξ
  have h1 : (M : ℝ) / selG w ξ * (1 - η) ≤ M / PP := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hGpos hPP]
    have := Nat.cast_nonneg (α := ℝ) M
    nlinarith
  nlinarith

end LeanFormalizations.Erdos385.LinearSieve

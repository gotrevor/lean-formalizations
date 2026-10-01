/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import PrimeNumberTheoremAnd.Consequences
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Rough

/-!
# `φ ≥ 1` for `s > 1`: rough numbers via the prime number theorem

`Φ(N, N^{1/s}) ≥ π(N) − N^{1/s}` and `π(N) log N / N → 1` (PNT+, `pi_alt`).
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset Filter Asymptotics

lemma primeCounting_le_card_Icc_add (N z : ℕ) :
    Nat.primeCounting N ≤ ((Icc z N).filter Nat.Prime).card + z := by
  classical
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow]
  calc ((range (N + 1)).filter Nat.Prime).card
      ≤ ((Icc z N).filter Nat.Prime ∪ range z).card := by
        refine card_le_card fun p hp => ?_
        simp only [mem_filter, mem_range] at hp
        simp only [mem_union, mem_filter, mem_Icc, mem_range]
        by_cases h : p < z
        · exact Or.inr h
        · exact Or.inl ⟨⟨by omega, by omega⟩, hp.2⟩
    _ ≤ _ := (card_union_le _ _).trans (by simp)

/-- **PNT boundary**: for `s > 1`, eventually `Φ(N, ⌊N^{1/s}⌋) log N / N ≥ 1 − δ`. -/
theorem rough_norm_ge {s δ : ℝ} (hs : 1 < s) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, 1 - δ ≤ (rough N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  have hc' : Tendsto c atTop (nhds 0) := by
    simpa using hc.tendsto_div_nhds_zero
  have hc2 := (hc'.comp tendsto_natCast_atTop_atTop).eventually
    (Metric.ball_mem_nhds 0 (show 0 < δ / 2 by positivity))
  set r := 1 - 1 / s
  have hr : 0 < r := by
    have : 1 / s < 1 := by rw [div_lt_one (by linarith)]; exact hs
    simp only [r]; linarith
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ r) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have hlog2 := (hlog.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))
  filter_upwards [hc2, hlog2, eventually_ge_atTop 2] with N hN1 hN2 hN3
  simp only [Function.comp, Real.dist_eq, sub_zero] at hN1 hN2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  set z := ⌊(N : ℝ) ^ (1 / s)⌋₊
  have hz : (z : ℝ) ≤ (N : ℝ) ^ (1 / s) := Nat.floor_le (by positivity)
  have hpiN := hpi N
  rw [Nat.floor_natCast] at hpiN
  have hcount : (Nat.primeCounting N : ℝ) ≤ rough N z + z := by
    have h1 := primeCounting_le_card_Icc_add N z
    have h2 := primes_le_rough N z
    exact_mod_cast h1.trans (by omega)
  -- π(N) log N / N = 1 + c N
  have hpinorm : (Nat.primeCounting N : ℝ) * Real.log N / N = 1 + c N := by
    rw [hpiN]; field_simp
  -- z log N / N ≤ δ/2
  have hzpow : (N : ℝ) ^ (1 / s) * (N : ℝ) ^ r = N := by
    rw [← Real.rpow_add hNpos]; simp [r]
  have hzterm : (z : ℝ) * Real.log N / N ≤ δ / 2 := by
    have hNr' : 0 < (N : ℝ) ^ r := by positivity
    calc (z : ℝ) * Real.log N / N ≤ (N : ℝ) ^ (1 / s) * Real.log N / N := by gcongr
      _ = Real.log N / (N : ℝ) ^ r := by
          rw [div_eq_div_iff hNpos.ne' hNr'.ne']; linear_combination Real.log N * hzpow
      _ ≤ δ / 2 := hN2.le
  have habs := (abs_lt.mp hN1).1
  have key : (Nat.primeCounting N : ℝ) * Real.log N / N ≤
      (rough N z : ℝ) * Real.log N / N + (z : ℝ) * Real.log N / N := by
    rw [← add_div, ← add_mul]; gcongr
  linarith

end LeanFormalizations.Erdos385.LinearSieve

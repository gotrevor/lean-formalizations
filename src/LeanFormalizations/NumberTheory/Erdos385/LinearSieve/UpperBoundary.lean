/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.MertensBound
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Normalized

/-!
# `b(s) ≤ 2` for `0 < s ≤ 2` (phase E5, step 1 in the limit)

From `siftMax_le_explicit` with `ξ = ⌊N^{1/2−δ}⌋`: `S⁺ log N / N ≤ 1/(1/2−2δ) + C² log³N/N^{2δ}`.
This is the boundary datum `b ≤ 2 ≤ β` on `[1, 2]` for the comparison principle.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Filter

/-- For each small `δ`, eventually `S⁺(N, N^{1/s}) log N / N ≤ 1/(1/2 − 2δ) + δ`. -/
lemma siftMax_norm_eventually {s δ : ℝ} (hs0 : 0 < s) (hs : s ≤ 2) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    ∀ᶠ N : ℕ in atTop,
      (siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N ≤ 1 / (1 / 2 - 2 * δ) + δ := by
  obtain ⟨C, hC, ξ₀, hξ₀2, hexp⟩ := siftMax_le_explicit
  have hT : Tendsto (fun x : ℝ => Real.log x ^ (3 : ℝ) / x ^ (2 * δ)) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop 3 (by positivity)).tendsto_div_nhds_zero
  have hT' := (hT.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds (show (0 : ℝ) < δ / C ^ 2 by positivity))
  have hP := ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 2 (ξ₀ : ℝ))
  filter_upwards [hT', hP, eventually_ge_atTop 2] with N hN3 hNδ hN2
  simp only [Function.comp] at hN3 hNδ
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  set x : ℝ := (N : ℝ) ^ (1 / 2 - δ) with hx
  set ξ : ℕ := ⌊x⌋₊ with hξ
  have hNd2 : (2 : ℝ) ≤ (N : ℝ) ^ δ := (le_max_left _ _).trans hNδ
  -- x = N^{1/2-2δ} * N^δ ≥ 2 N^{1/2-2δ}
  have hsplit : x = (N : ℝ) ^ (1 / 2 - 2 * δ) * (N : ℝ) ^ δ := by
    rw [hx, ← Real.rpow_add hNpos]; ring_nf
  have hy1 : (N : ℝ) ^ δ ≤ (N : ℝ) ^ (1 / 2 - 2 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hypos : 0 < (N : ℝ) ^ (1 / 2 - 2 * δ) := by positivity
  have hx2 : 2 ≤ x := by rw [hsplit]; nlinarith
  have hξge : (N : ℝ) ^ (1 / 2 - 2 * δ) ≤ ξ := by
    have h1 : x - 1 < ξ := Nat.sub_one_lt_floor x
    have : 2 * (N : ℝ) ^ (1 / 2 - 2 * δ) ≤ x := by rw [hsplit]; nlinarith
    linarith
  have hξ₀ : ξ₀ ≤ ξ := by
    have : (ξ₀ : ℝ) ≤ ξ := ((le_max_right _ _).trans hNδ).trans (hy1.trans hξge)
    exact_mod_cast this
  have hξle : (ξ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hξz : ξ < ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
    have : ((ξ + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / s) := by
      push_cast
      have h12 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / s) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by rw [div_le_div_iff₀ (by norm_num) hs0]; linarith)
      have : (N : ℝ) ^ (1 / 2 : ℝ) = x * (N : ℝ) ^ δ := by
        rw [hx, ← Real.rpow_add hNpos]; ring_nf
      nlinarith
    exact Nat.lt_of_succ_le (Nat.le_floor this)
  have hB := hexp N _ ξ hξ₀ hξz
  have hξ1 : (1 : ℝ) < ξ := by
    have : (2 : ℝ) ≤ ξ := by exact_mod_cast le_trans hξ₀2 hξ₀
    linarith
  have hlogξ : (1 / 2 - 2 * δ) * Real.log N ≤ Real.log ξ := by
    rw [← Real.log_rpow hNpos]
    exact Real.log_le_log (by positivity) hξge
  have hlogξpos : 0 < Real.log ξ := Real.log_pos hξ1
  have hlogξN : Real.log ξ ≤ Real.log N := Real.log_le_log (by linarith) (by
    have : x ≤ N := by
      rw [hx]; calc (N : ℝ) ^ (1 / 2 - δ) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = N := Real.rpow_one _
    linarith)
  -- term 1
  have hA : (N : ℝ) / Real.log ξ * Real.log N / N ≤ 1 / (1 / 2 - 2 * δ) := by
    rw [mul_div_assoc, div_mul_div_comm, mul_comm (N : ℝ), ← div_mul_div_comm, div_self hNpos.ne',
      mul_one, div_le_div_iff₀ hlogξpos (by linarith)]
    linarith
  -- term 2
  have hBterm : (C * ξ * Real.log ξ) ^ 2 * Real.log N / N ≤ δ := by
    have hx2' : x ^ 2 = (N : ℝ) / (N : ℝ) ^ (2 * δ) := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, eq_div_iff (by positivity),
        ← Real.rpow_add hNpos]; ring_nf; exact Real.rpow_one _
    have hl3 : Real.log N ^ (3 : ℝ) = Real.log N ^ 3 := by exact_mod_cast Real.rpow_natCast _ 3
    rw [hl3, div_lt_div_iff₀ (by positivity) (by positivity)] at hN3
    have hNd : 0 < (N : ℝ) ^ (2 * δ) := by positivity
    have e1 : (C * ξ * Real.log ξ) ^ 2 ≤ C ^ 2 * x ^ 2 * Real.log N ^ 2 := by
      rw [mul_pow, mul_pow]
      have := pow_le_pow_left₀ (by positivity) hξle 2
      have := pow_le_pow_left₀ hlogξpos.le hlogξN 2
      gcongr
    rw [hx2'] at e1
    rw [div_le_iff₀ hNpos]
    calc (C * ξ * Real.log ξ) ^ 2 * Real.log N
        ≤ C ^ 2 * ((N : ℝ) / (N : ℝ) ^ (2 * δ)) * Real.log N ^ 2 * Real.log N :=
          mul_le_mul_of_nonneg_right e1 hlogN.le
      _ = C ^ 2 * Real.log N ^ 3 * N / (N : ℝ) ^ (2 * δ) := by ring
      _ ≤ δ * N := by
          rw [div_le_iff₀ hNd]
          have : C ^ 2 * Real.log N ^ 3 < δ * (N : ℝ) ^ (2 * δ) := by
            linarith
          nlinarith
  have hfin : (siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N ≤
      ((N : ℝ) / Real.log ξ + (C * ξ * Real.log ξ) ^ 2) * Real.log N / N := by
    gcongr
  calc _ ≤ _ := hfin
    _ = (N : ℝ) / Real.log ξ * Real.log N / N + (C * ξ * Real.log ξ) ^ 2 * Real.log N / N := by
        ring
    _ ≤ _ := add_le_add hA hBterm

/-- **`b(s) ≤ 2` on `(0, 2]`.** -/
theorem bUp_le_two {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 2) : bUp s ≤ 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := min (1 / 16) (ε / 40)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 16 := min_le_left _ _
  have hδ2 : δ ≤ ε / 40 := min_le_right _ _
  have hb : bUp s ≤ 1 / (1 / 2 - 2 * δ) + δ := by
    unfold bUp
    refine limsup_le_of_le ?_ (siftMax_norm_eventually hs0 hs hδ (by linarith))
    exact IsBoundedUnder.isCoboundedUnder_le (isBoundedUnder_of ⟨0, fun N => by positivity⟩)
  have : 1 / (1 / 2 - 2 * δ) ≤ 2 + 16 * δ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

end LeanFormalizations.Erdos385.LinearSieve

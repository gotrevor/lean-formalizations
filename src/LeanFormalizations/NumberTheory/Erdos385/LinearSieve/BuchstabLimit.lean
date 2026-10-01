/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Mertens

/-!
# Toward the limit Buchstab inequalities (phase E5, step 2)

`tendsto_primeRecip_window`: `Σ_{N^{1/t'} < p ≤ N^{1/t}} 1/p → log(t'/t)` (Mertens' second theorem,
`mertens_second_tendsto`).  Plan for `buchstab_limit_a`: split `t ∈ [s, s']` into finitely many bins,
bound each `S⁺(N/p, p)` by `(b(t_{i+1}−1)+δ)(N/p)/log(N/p)` (monotone in the level, so one `N₀`
per bin), sum with this window lemma, then upper Riemann sums of the monotone `b(t−1)/(t−1)`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve
open Filter Topology

/-- `log ⌊N^a⌋ / log N → a`. -/
lemma tendsto_log_floor_rpow_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log ⌊(N : ℝ) ^ a⌋₊ / Real.log N) atTop (𝓝 a) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hN
  have hinv : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
    hlog.const_div_atTop _
  have hlow : Tendsto (fun N : ℕ => a - Real.log 2 / Real.log N) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [((tendsto_rpow_atTop ha).comp hN).eventually_ge_atTop 2,
      hN.eventually_ge_atTop 2] with N hx hN2
    simp only [Function.comp] at hx
    have hl : 0 < Real.log N := Real.log_pos (by linarith)
    have hxpos : 0 < (N : ℝ) ^ a := by linarith
    have hfl : (N : ℝ) ^ a / 2 ≤ ⌊(N : ℝ) ^ a⌋₊ := by
      have := Nat.sub_one_lt_floor ((N : ℝ) ^ a); linarith
    have h := Real.log_le_log (by positivity) hfl
    rw [Real.log_div hxpos.ne' (by norm_num), Real.log_rpow (by linarith)] at h
    rw [le_div_iff₀ hl, sub_mul, div_mul_cancel₀ _ hl.ne']
    linarith
  · filter_upwards [((tendsto_rpow_atTop ha).comp hN).eventually_ge_atTop 2,
      hN.eventually_ge_atTop 2] with N hx hN2
    simp only [Function.comp] at hx
    have hl : 0 < Real.log N := Real.log_pos (by linarith)
    have hfl0 : (0 : ℝ) < ⌊(N : ℝ) ^ a⌋₊ := by
      have := Nat.sub_one_lt_floor ((N : ℝ) ^ a); linarith
    have h := Real.log_le_log hfl0 (Nat.floor_le (by linarith))
    rw [Real.log_rpow (by linarith)] at h
    rw [div_le_iff₀ hl]; linarith

/-- **Mertens window**: `Σ_{N^{1/t'} < p ≤ N^{1/t}} 1/p → log (t'/t)`. -/
theorem tendsto_primeRecip_window {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t') :
    Tendsto (fun N : ℕ => LeanFormalizations.Mertens.primeRecipSum ⌊(N : ℝ) ^ (1 / t)⌋₊ -
      LeanFormalizations.Mertens.primeRecipSum ⌊(N : ℝ) ^ (1 / t')⌋₊) atTop
      (𝓝 (Real.log (t' / t))) := by
  have ht' : 0 < t' := ht.trans_le htt'
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hfl : ∀ a : ℝ, 0 < a → Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ a⌋₊) atTop atTop := fun a ha =>
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp hN)
  set f := fun M : ℕ => LeanFormalizations.Mertens.primeRecipSum M - Real.log (Real.log M)
  have hf := LeanFormalizations.Mertens.mertens_second_tendsto
  have h1 := hf.comp (hfl (1 / t) (by positivity))
  have h2 := hf.comp (hfl (1 / t') (by positivity))
  -- ratio of logs
  have hr1 := tendsto_log_floor_rpow_div (a := 1 / t) (by positivity)
  have hr2 := tendsto_log_floor_rpow_div (a := 1 / t') (by positivity)
  have hratio : Tendsto (fun N : ℕ => Real.log (Real.log ⌊(N : ℝ) ^ (1 / t)⌋₊ / Real.log N) -
      Real.log (Real.log ⌊(N : ℝ) ^ (1 / t')⌋₊ / Real.log N)) atTop
      (𝓝 (Real.log (1 / t) - Real.log (1 / t'))) :=
    ((Real.continuousAt_log (by positivity)).tendsto.comp hr1).sub
      ((Real.continuousAt_log (by positivity)).tendsto.comp hr2)
  have hlim : Real.log (1 / t) - Real.log (1 / t') = Real.log (t' / t) := by
    rw [Real.log_div ht'.ne' ht.ne', one_div, one_div, Real.log_inv, Real.log_inv]; ring
  rw [hlim] at hratio
  have hsum := (h1.sub h2).add hratio
  rw [sub_self, zero_add] at hsum
  refine hsum.congr' ?_
  have hev : ∀ a : ℝ, 0 < a → ∀ᶠ N : ℕ in atTop, 1 < Real.log ⌊(N : ℝ) ^ a⌋₊ := fun a ha =>
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp (hfl a ha)).eventually_gt_atTop 1
  filter_upwards [hev (1 / t) (by positivity), hev (1 / t') (by positivity),
    (Real.tendsto_log_atTop.comp hN).eventually_gt_atTop 0] with N e1 e2 e3
  simp only [Function.comp_apply] at e3 ⊢
  rw [Real.log_div (by linarith) e3.ne', Real.log_div (by linarith) e3.ne']
  ring

end LeanFormalizations.Erdos385.LinearSieve

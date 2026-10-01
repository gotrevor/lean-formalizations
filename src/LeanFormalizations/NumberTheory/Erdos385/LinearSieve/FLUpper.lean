/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.FLUniform
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Bounded
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.BuchstabLimit
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.DelaySolution
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.MertensConstant

/-!
# The upper half of the fundamental lemma (phase E5, step 3)

`siftMax_mul_le` at `w = ⌊N^{1/s}⌋`, `ξ = ⌊N^{1/3}⌋` has `ξ^{−8/log w} ≤ e^{−2s}`, and
`log N / Π(w−1) → e^{−γ} s` (Mertens' third theorem).  Hence
`b(s) ≤ e^{−γ} s / (1 − e^K e^{−2s})`, and so `b(s) ≤ e^{−γ}s + M e^{−s}` for `s ≥ 2`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Filter Topology Finset

/-- `log (⌊N^a⌋ − 1) / log N → a`. -/
lemma tendsto_log_floor_sub_one_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log ((⌊(N : ℝ) ^ a⌋₊ - 1 : ℕ) : ℝ) / Real.log N) atTop (𝓝 a) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hN
  have hinv : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
    hlog.const_div_atTop _
  have hlow : Tendsto (fun N : ℕ => a - Real.log 2 / Real.log N) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [((tendsto_rpow_atTop ha).comp hN).eventually_ge_atTop 4,
      hN.eventually_ge_atTop 2] with N hx hN2
    simp only [Function.comp] at hx
    have hl : 0 < Real.log N := Real.log_pos (by linarith)
    have hxpos : 0 < (N : ℝ) ^ a := by linarith
    have hfl1 : 1 ≤ ⌊(N : ℝ) ^ a⌋₊ := Nat.one_le_floor_iff _ |>.mpr (by linarith)
    have hfl : (N : ℝ) ^ a / 2 ≤ ((⌊(N : ℝ) ^ a⌋₊ - 1 : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor ((N : ℝ) ^ a)
      rw [Nat.cast_sub hfl1]; push_cast; linarith
    have h := Real.log_le_log (by positivity) hfl
    rw [Real.log_div hxpos.ne' (by norm_num), Real.log_rpow (by linarith)] at h
    rw [le_div_iff₀ hl, sub_mul, div_mul_cancel₀ _ hl.ne']
    linarith
  · filter_upwards [((tendsto_rpow_atTop ha).comp hN).eventually_ge_atTop 4,
      hN.eventually_ge_atTop 2] with N hx hN2
    simp only [Function.comp] at hx
    have hl : 0 < Real.log N := Real.log_pos (by linarith)
    have hfl1 : 1 ≤ ⌊(N : ℝ) ^ a⌋₊ := Nat.one_le_floor_iff _ |>.mpr (by linarith)
    have hfl0 : (0 : ℝ) < ((⌊(N : ℝ) ^ a⌋₊ - 1 : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor ((N : ℝ) ^ a)
      rw [Nat.cast_sub hfl1]; push_cast; linarith
    have hle : ((⌊(N : ℝ) ^ a⌋₊ - 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ a := by
      rw [Nat.cast_sub hfl1]; push_cast; linarith [Nat.floor_le (show (0:ℝ) ≤ (N : ℝ) ^ a by linarith)]
    have h := Real.log_le_log hfl0 hle
    rw [Real.log_rpow (by linarith)] at h
    rw [div_le_iff₀ hl]; linarith

/-- **Mertens' third theorem at the sifting limit**: `log N / Π(⌊N^{1/s}⌋ − 1) → e^{−γ} s`. -/
theorem tendsto_log_div_mertensP {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => Real.log N / mertensP (⌊(N : ℝ) ^ (1 / s)⌋₊ - 1)) atTop
      (𝓝 (mertC * s)) := by
  set n : ℕ → ℕ := fun N => ⌊(N : ℝ) ^ (1 / s)⌋₊ - 1
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hn : Tendsto n atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ (1 / s)⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by positivity)).comp hN)
    exact (tendsto_sub_atTop_nat 1).comp h1
  have hM := LeanFormalizations.Mertens.mertens_third_classical_eGamma.comp hn
  have hr := (tendsto_log_floor_sub_one_div (a := 1 / s) (by positivity)).inv₀
    (by positivity : (1 / s : ℝ) ≠ 0)
  have hprod := hM.mul hr
  rw [one_div, inv_inv, ← mertC] at hprod
  refine hprod.congr' ?_
  filter_upwards [hn.eventually_ge_atTop 2, hN.eventually_ge_atTop 2] with N hn2 hN2
  have hlogn : 0 < Real.log (n N : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  simp only [Function.comp, mertensP_eq_inv, div_inv_eq_mul, mertC, n] at *
  field_simp

/-- `C² (log N)³ / N^{1/3} → 0`. -/
lemma tendsto_log_cube_div {C : ℝ} :
    Tendsto (fun N : ℕ => C ^ 2 * Real.log N ^ 3 / (N : ℝ) ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (show (0 : ℝ) < 1 / 3 by norm_num)).tendsto_div_nhds_zero
  have h2 := (h.comp tendsto_natCast_atTop_atTop).const_mul (C ^ 2)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  simp only [Function.comp]
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- **Upper fundamental lemma at a level**: `b(s) ≤ e^{−γ}s / (1 − e^K e^{−2s})`. -/
theorem bUp_le_rate {s : ℝ} (hs : 1 ≤ s) (hη : Real.exp rankK * Real.exp (-2 * s) < 1) :
    bUp s ≤ mertC * s / (1 - Real.exp rankK * Real.exp (-2 * s)) := by
  obtain ⟨C, hC, ξ₀, hξ₀⟩ := mertensP_le_log
  set η := Real.exp rankK * Real.exp (-2 * s) with hηdef
  set D := 1 - η with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  have hs0 : 0 < s := by linarith
  set g : ℕ → ℝ := fun N => (Real.log N / mertensP (⌊(N : ℝ) ^ (1 / s)⌋₊ - 1) +
    C ^ 2 * Real.log N ^ 3 / (N : ℝ) ^ (1 / 3 : ℝ)) / D with hgdef
  have hg : Tendsto g atTop (𝓝 (mertC * s / D)) := by
    have := ((tendsto_log_div_mertensP hs0).add (tendsto_log_cube_div (C := C))).div_const D
    rw [add_zero] at this; exact this
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hz3 : ∀ᶠ N : ℕ in atTop, 3 ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ :=
    (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by positivity)).comp hN)).eventually_ge_atTop 3
  have hξ : ∀ᶠ N : ℕ in atTop, ξ₀ ≤ ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ :=
    (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp hN)).eventually_ge_atTop ξ₀
  have h12 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 12 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).comp hN).eventually_ge_atTop 2
  have hmain : ∀ᶠ N : ℕ in atTop, bSeq s N ≤ g N := by
    filter_upwards [hz3, hξ, h12, eventually_ge_atTop 2] with N hz3 hξN h12 hN2
    set z := ⌊(N : ℝ) ^ (1 / s)⌋₊
    set ξ := ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊
    set L := Real.log N
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
    have hNpos : (0 : ℝ) < N := by linarith
    have hL : 0 < L := Real.log_pos hN1
    set t := (N : ℝ) ^ (1 / 3 : ℝ)
    set q := (N : ℝ) ^ (1 / 4 : ℝ)
    have ht3 : t ^ 3 = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    have htq : t = (N : ℝ) ^ (1 / 12 : ℝ) * q := by
      show (N : ℝ) ^ (1 / 3 : ℝ) = _
      rw [← Real.rpow_add hNpos]; norm_num
    have hq1 : 1 ≤ q := Real.one_le_rpow hN1.le (by norm_num)
    have ht2 : 2 ≤ t := by nlinarith
    have htpos : 0 < t := by linarith
    have hξlow : t / 2 ≤ ξ := by have := Nat.sub_one_lt_floor t; linarith
    have hξ1 : 1 ≤ ξ := by
      have : (1 : ℝ) ≤ ξ := by linarith
      exact_mod_cast this
    have hξpos : (0 : ℝ) < ξ := by exact_mod_cast hξ1
    have hξq : q ≤ ξ := by nlinarith
    have hlogξ : L / 4 ≤ Real.log ξ := by
      have h := Real.log_le_log (by linarith) hξq
      rw [Real.log_rpow hNpos] at h; linarith
    have hξt : (ξ : ℝ) ≤ t := Nat.floor_le htpos.le
    have hlogξL : Real.log ξ ≤ L := by
      have h := Real.log_le_log hξpos hξt
      rw [Real.log_rpow hNpos] at h; linarith
    have hz : (3 : ℝ) ≤ z := by exact_mod_cast hz3
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    have hzN : Real.log z ≤ L / s := by
      have h := Real.log_le_log (by linarith) (Nat.floor_le (Real.rpow_nonneg hNpos.le (1 / s)))
      rw [Real.log_rpow hNpos] at h; linarith [show 1 / s * L = L / s by ring]
    -- the Rankin factor
    have hηN : Real.exp rankK * (ξ : ℝ) ^ (-(8 / Real.log z)) ≤ η := by
      rw [hηdef]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [Real.rpow_def_of_pos hξpos, Real.exp_le_exp]
      have h1 : s * Real.log z ≤ L := by
        rw [le_div_iff₀ hs0] at hzN; linarith
      rw [mul_neg, ← mul_div_assoc, neg_le_neg_iff.symm, neg_neg, neg_mul, neg_neg,
        le_div_iff₀ hlogz]
      nlinarith
    have hU := siftMax_mul_le N (w := z) (ξ := ξ) (by omega) hξ1
    have hS0 : (0 : ℝ) ≤ siftMax N z := Nat.cast_nonneg _
    have hSD : (siftMax N z : ℝ) * D ≤ N / mertensP (z - 1) + selE z ξ ^ 2 := by
      refine le_trans ?_ hU
      exact mul_le_mul_of_nonneg_left (by rw [hDdef]; linarith) hS0
    -- the error term
    have hE : selE z ξ ≤ t * (C * L) := by
      calc selE z ξ ≤ ξ * mertensP ξ := selE_le z ξ
        _ ≤ t * (C * L) := by
          apply mul_le_mul hξt _ (mertensP_pos _).le htpos.le
          exact (hξ₀ ξ hξN).trans (mul_le_mul_of_nonneg_left hlogξL hC.le)
    have hE2 : selE z ξ ^ 2 ≤ (t * (C * L)) ^ 2 := pow_le_pow_left₀ (selE_nonneg _ _) hE 2
    have hPP := mertensP_pos (z - 1)
    show siftMax N z * L / N ≤ _
    rw [hgdef]
    simp only
    rw [div_le_div_iff₀ hNpos hD]
    have key : (siftMax N z : ℝ) * D * L ≤ (N / mertensP (z - 1) + (t * (C * L)) ^ 2) * L :=
      mul_le_mul_of_nonneg_right (hSD.trans (by linarith)) hL.le
    have hid : (N / mertensP (z - 1) + (t * (C * L)) ^ 2) * L =
        (L / mertensP (z - 1) + C ^ 2 * L ^ 3 / t) * N := by
      rw [← ht3]; field_simp
    nlinarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hev := hg.eventually (gt_mem_nhds (show mertC * s / D < mertC * s / D + δ by linarith))
  refine limsup_le_of_le (isBoundedUnder_of ⟨0, bSeq_nonneg s⟩).isCoboundedUnder_le ?_
  filter_upwards [hmain, hev] with N h1 h2
  exact (h1.trans h2.le)

lemma mertC_pos : 0 < mertC := Real.exp_pos _

/-- `b(s) ≤ e^{−γ}s + 2e^{−γ}e^K e^{−s}` once `e^K e^{−2s} ≤ 1/2`. -/
lemma bUp_le_large {s : ℝ} (hs : 1 ≤ s) (hη : Real.exp rankK * Real.exp (-2 * s) ≤ 1 / 2) :
    bUp s ≤ mertC * s + 2 * mertC * Real.exp rankK * Real.exp (-s) := by
  set η := Real.exp rankK * Real.exp (-2 * s) with hηdef
  have hη0 : 0 ≤ η := by positivity
  have h := bUp_le_rate hs (by linarith)
  have hC := mertC_pos
  have hD : 0 < 1 - η := by linarith
  refine h.trans ?_
  rw [div_le_iff₀ hD]
  have hse : s * Real.exp (-s) ≤ 1 := by
    have := Real.add_one_le_exp s
    have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-s)]
  have hsplit : η = Real.exp rankK * Real.exp (-s) * Real.exp (-s) := by
    rw [hηdef, mul_assoc, ← Real.exp_add (-s), show -s + -s = -2 * s by ring]
  have hK := Real.exp_pos rankK
  have he := Real.exp_pos (-s)
  -- `C s (1 + 2η)(1 − η) ≥ C s` and `2Csη ≤ 2Ce^K e^{−s}`
  have h1 : mertC * s ≤ (mertC * s + 2 * mertC * s * η) * (1 - η) := by
    have : 0 ≤ mertC * s * η * (1 - 2 * η) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  have h2 : 2 * mertC * s * η ≤ 2 * mertC * Real.exp rankK * Real.exp (-s) := by
    rw [hsplit]
    have : s * Real.exp (-s) * (Real.exp rankK * Real.exp (-s)) ≤
        1 * (Real.exp rankK * Real.exp (-s)) :=
      mul_le_mul_of_nonneg_right hse (by positivity)
    nlinarith
  nlinarith

/-- **The upper half of the fundamental lemma**: `b(s) ≤ e^{−γ}s + M e^{−s}` for `s ≥ 2`. -/
theorem bUp_le_fl : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 2 ≤ s → bUp s ≤ mertC * s + M * Real.exp (-s) := by
  set s₀ := max 2 ((rankK + Real.log 2) / 2)
  have hs₀ : 2 ≤ s₀ := le_max_left _ _
  have hlarge : ∀ s, s₀ ≤ s → Real.exp rankK * Real.exp (-2 * s) ≤ 1 / 2 := by
    intro s hs
    have h : rankK + -2 * s ≤ -Real.log 2 := by
      have := le_max_right 2 ((rankK + Real.log 2) / 2); linarith
    rw [← Real.exp_add]
    calc Real.exp (rankK + -2 * s) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr h
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  set A := 2 * mertC * Real.exp rankK
  set B₀ := mertC * s₀ + A * Real.exp (-s₀)
  have hA : 0 ≤ A := by have := mertC_pos; positivity
  have hB₀ : 0 ≤ B₀ := by have := mertC_pos; positivity
  refine ⟨max A (B₀ * Real.exp s₀), le_max_of_le_left hA, fun s hs => ?_⟩
  have he := Real.exp_pos (-s)
  rcases le_or_gt s₀ s with h | h
  · refine (bUp_le_large (by linarith) (hlarge s h)).trans ?_
    have : A * Real.exp (-s) ≤ max A (B₀ * Real.exp s₀) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) he.le
    linarith
  · have hb := bUp_mono' (show s ∈ Set.Ioi 0 by simp; linarith)
      (show s₀ ∈ Set.Ioi 0 by simp; linarith) h.le
    have h0 := bUp_le_large (by linarith) (hlarge s₀ le_rfl)
    have hC := mertC_pos
    have : B₀ ≤ B₀ * Real.exp s₀ * Real.exp (-s) := by
      rw [mul_assoc, ← Real.exp_add]
      exact le_mul_of_one_le_right hB₀ (Real.one_le_exp (by linarith))
    have h3 : B₀ * Real.exp s₀ * Real.exp (-s) ≤ max A (B₀ * Real.exp s₀) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) he.le
    have : 0 ≤ mertC * s := by positivity
    linarith

end LeanFormalizations.Erdos385.LinearSieve

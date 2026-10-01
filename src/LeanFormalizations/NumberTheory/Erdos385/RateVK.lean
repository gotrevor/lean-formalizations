/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.Rate
import LeanFormalizations.NumberTheory.Erdos385.Headline
import LeanFormalizations.NumberTheory.Erdos385.RateVK.RateGen

/-!
# Erdős #385: the sharp rate `exp(−(log X)^{1/3−ε})` (phase E3d)

One frozen statement, `almost_all_F385_rate_VK`: from Vinogradov–Korobov and the de la Vallée
Poussin PNT, for each `δ ∈ (0, 1/4)` and `ε > 0`,
`#{n ≤ X : F(n) < n + (1 − δ)√n} ≤ C X exp(−(log X)^{1/3 − ε})`.
This is the rate the source argument gives (`DOOR-ALMOSTALL-ERDOS-385.md`, check (3), 80%), and it is
the limit of the method: the only saving is the VK pointwise bound for a prime sum of length `√X`.

## Route (DONE 2026-10-01, axiom-clean: the E3 pipeline re-run at a general exponent `a < 1/3` in
`RateVK/General.lean` + `RateVK/RateGen.lean`, `a = 1/3 − min(ε,1/6)/2`, PNT input from DLVP via
`pntExp_of_DLVP`; VK's `ε` in `primeP_small` is `(1/3 − a)/2`)

E3's pieces are tuned to `MediumPNTStatement` (saving `exp(−(κ/2)(log Z)^{1/10})`).  Re-run them
with the scale `T₀ = exp((log Z)^{1/3})`, `h₂ = X/T₀³`, and the three discharged inputs
(`Erdos385.mr16Lemma14_holds`, `montgomeryVaughanMVT_holds`, `mediumPNTStatement_holds` are proved;
use them directly):

1. **Long average** (replaces `longAverage_lower`'s use of MediumPNT).  The `h₂`-averages of the
   witness coefficients are `≥ c₁ δ / log² Z`: it needs primes `q` in intervals of length
   `≍ √Z exp(−3(log Z)^{1/3})` at height `√Z`, and `DLVPStatement` gives error
   `√Z exp(−c √(log √Z))`, which is `o` of that length because `√(log Z) ≫ (log Z)^{1/3}`.
   State a `longAverage_lower_DLVP` mirroring `longAverage_lower` with the new `paramH2`.
2. **Variance** (replaces `variance_small`'s parameter choice).  The three terms of MR16 Lemma 14:
   `1/T₀ = exp(−(log Z)^{1/3})`; the middle range `≤ sup_{T₀ ≤ |t| ≤ 2Z} |P(1+it)|² · ∫|Q|²` with
   `SmoothPrimeSumVK` (from `smoothPrimeSumVK_of_VKZ`) at `P = √Z`, `T = max(√Z, 2|t|)`, giving
   `|P(1+it)| ≪ T₀^{−B} + exp(−(log Z)^{1/3−ε/2}/3)` (Mellin decay for small `|t|`, VK otherwise),
   and MVT for `Q`; the tail as in E3.  So the variance is `≪ exp(−(log Z)^{1/3−ε/2}/4)`.
3. **Per window**: `card_badWindow_le` with `μ = c₁δ/log² Z` gives
   `#badWindow ≤ C Z (log Z)⁴ exp(−(log Z)^{1/3−ε/2}/4)`.
4. **Sum over windows**: `card_le_of_windows` (`Rate.lean`) and the split at `√X`, exactly as in
   `almost_all_F385_rate`; absorb `(log)^4` and the constant `1/4` into the `ε/2` slack.

If E3's lemmas hard-wire `MediumPNTStatement` or the `1/10` scale, add parametrised copies rather
than editing frozen statements.  If a step stalls, state it as a NAMED sub-lemma with a disclosed
hole plus an English paragraph and a confidence; that is an acceptable finish.

Frozen: this statement, every statement in `AlmostAll.lean`/`Rate.lean`, and everything in
`Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Real LeanFormalizations.Literature

/-- de la Vallée Poussin's error term implies the error `x exp(−c (log x)^a)` for `0 < a ≤ 1/2`. -/
theorem pntExp_of_DLVP (h : DLVPStatement) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) : Gen.PNTExp a := by
  obtain ⟨c, hc, hO⟩ := h
  refine ⟨c, hc, hO.trans (Asymptotics.IsBigO.of_bound 1 ?_)⟩
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hL : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hpow : Real.log x ^ a ≤ Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hL ha'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity),
    one_mul]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hx0.le

/-- **Theorem A with the sharp rate** `exp(−(log X)^{1/3−ε})`. -/
theorem almost_all_F385_rate_VK (h3 : VKZeroFreeLogDeriv) (h5 : DLVPStatement) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * X * Real.exp (-(Real.log X ^ ((1 : ℝ) / 3 - ε))) := by
  classical
  set m := min ε (1 / 6) with hm
  have hm0 : 0 < m := lt_min hε (by norm_num)
  have hm6 : m ≤ 1 / 6 := min_le_right _ _
  set a := 1 / 3 - m / 2 with ha
  haveI : Fact (0 < a) := ⟨by rw [ha]; linarith⟩
  haveI : Fact (a < 1 / 3) := ⟨by rw [ha]; linarith⟩
  obtain ⟨c, hc, C, hC⟩ := Gen.almost_all_F385_rate (a := a) _root_.Erdos385.mr16Lemma14_holds
    _root_.Erdos385.montgomeryVaughanMVT_holds h3
    (pntExp_of_DLVP h5 (by rw [ha]; linarith) (by rw [ha]; linarith)) hδ hδ'
  set e := (1 : ℝ) / 3 - ε with he
  -- eventually `L^e ≤ c L^a`
  have hev : ∀ᶠ L : ℝ in Filter.atTop, L ^ e ≤ c * L ^ a := by
    filter_upwards [Filter.eventually_ge_atTop 1,
      (tendsto_rpow_atTop (show 0 < m / 2 by positivity)).eventually_ge_atTop (1 / c)] with L hL hLc
    have h1 : L ^ e ≤ L ^ (1 / 3 - m) :=
      Real.rpow_le_rpow_of_exponent_le hL (by rw [he]; linarith [min_le_left ε (1 / 6)])
    have h2 : L ^ a = L ^ (m / 2) * L ^ (1 / 3 - m) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; rw [ha]; ring
    have h3' : 1 ≤ c * L ^ (m / 2) := by rwa [div_le_iff₀' hc] at hLc
    have : 0 ≤ L ^ (1 / 3 - m) := by positivity
    rw [h2]; nlinarith
  have hevN : ∀ᶠ X : ℕ in Filter.atTop, Real.log X ^ e ≤ c * Real.log X ^ a :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hev
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hevN
  set M := ∑ n ∈ Finset.range (X₀ + 1), Real.exp (Real.log n ^ e) with hM
  have hM0 : ∀ n ≤ X₀, Real.exp (Real.log n ^ e) ≤ M := fun n hn =>
    Finset.single_le_sum (f := fun n : ℕ => Real.exp (Real.log n ^ e))
      (fun _ _ => (Real.exp_pos _).le) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
  refine ⟨|C| + 2 * M, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  set Φ := Real.exp (-(Real.log X ^ e)) with hΦ
  have hΦ0 : 0 < Φ := Real.exp_pos _
  have hcnt0 : (0 : ℝ) ≤ ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) :=
    Nat.cast_nonneg _
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  rcases le_or_gt X₀ X with hXX | hXX
  · have hb := hC X hX
    have hexp : Real.exp (-c * Real.log X ^ a) ≤ Φ :=
      Real.exp_le_exp.2 (by have := hX₀ X hXX; linarith)
    have hC0 : 0 ≤ C * X * Real.exp (-c * Real.log X ^ a) := hcnt0.trans hb
    have : C * X * Real.exp (-c * Real.log X ^ a) ≤ |C| * X * Φ := by
      have hC' : 0 ≤ C := by
        by_contra hneg; push_neg at hneg
        have : C * X * Real.exp (-c * Real.log X ^ a) < 0 :=
          mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by linarith)) (Real.exp_pos _)
        linarith
      rw [abs_of_nonneg hC']
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    have : 0 ≤ 2 * M * X * Φ := by positivity
    nlinarith
  · have hsub : {n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n} ⊆
        ↑(Finset.range (X + 1)) := fun n hn => by
      simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_succ_of_le hn.1
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_range] at h1
    have h1' : ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤ 2 * X := by
      have : (({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℕ) : ℝ) ≤
          ((X + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have hEΦ : 1 ≤ M * Φ := by
      have h := hM0 X hXX.le
      have : Real.exp (Real.log X ^ e) * Φ = 1 := by rw [hΦ, ← Real.exp_add]; simp
      nlinarith
    have : 2 * X ≤ 2 * M * X * Φ := by nlinarith
    have : 0 ≤ |C| * X * Φ := by positivity
    nlinarith

end LeanFormalizations.Erdos385

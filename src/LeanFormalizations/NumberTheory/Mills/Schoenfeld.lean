/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Caldwell–Cheng (2005), Lemma 5: under RH there is a prime between consecutive cubes

The analytic half of the Mills-digits route.  Schoenfeld's RH bound
`|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657` gives, with `a = n³`, `b = (n+1)³`,

  `π(b) − π(a) > ∫ₐᵇ dt/log t − (√a log a + √b log b)/(8π)`.

Bounding the integral below by `(b − a)/log b`, and `√a log a ≤ √b log b`, it suffices that
`4π (b − a) > √b (log b)²`.  With `m = n + 1` that reads `4π(3n² + 3n + 1) > √(m³) · 9 log²m`,
and the elementary inequality `9 log²m < 32 √m` (four terms of the exponential series) turns the
right side into `32 m²`; `4π(3n² + 3n + 1) > 32 (n+1)²` already for `n ≥ 12`.

`n = 1, …, 13` are explicit witnesses.
-/
import Mathlib
import LeanFormalizations.Literature.Primes
import LeanFormalizations.NumberTheory.Mills.Basic

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-! ### Prime counting -/

/-- `π a < π b` exhibits a prime in `(a, b]`. -/
theorem exists_prime_of_primeCounting_lt {a b : ℕ}
    (h : Nat.primeCounting a < Nat.primeCounting b) :
    ∃ p, p.Prime ∧ a < p ∧ p ≤ b := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hab : a ≤ b := by
    by_contra hba
    push Not at hba
    have := Nat.monotone_primeCounting hba.le
    omega
  have key : {x ∈ Finset.range (b + 1) | x.Prime} = {x ∈ Finset.range (a + 1) | x.Prime} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hp⟩
      refine ⟨?_, hp⟩
      rcases Nat.lt_or_ge a x with hax | hax
      · exact absurd (show x ≤ b by omega) (hcon x hp hax)
      · omega
    · rintro ⟨hx, hp⟩
      exact ⟨by omega, hp⟩
  have e1 : Nat.primeCounting b = ({x ∈ Finset.range (b + 1) | x.Prime}).card :=
    Nat.count_eq_card_filter_range (p := Nat.Prime) (b + 1)
  have e2 : Nat.primeCounting a = ({x ∈ Finset.range (a + 1) | x.Prime}).card :=
    Nat.count_eq_card_filter_range (p := Nat.Prime) (a + 1)
  rw [e1, e2, key] at h
  exact absurd h (lt_irrefl _)

/-! ### The integrand `1/log t` -/

theorem one_div_log_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  have hsub : Set.Icc a b ⊆ ({0}ᶜ : Set ℝ) := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h0
    rw [h0] at ht
    linarith [ht.1]
  refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono hsub) ?_
  intro t ht
  exact ne_of_gt (Real.log_pos (by linarith [ht.1]))

/-- The integrand is decreasing, so the integral dominates `(b − a)/log b`. -/
theorem le_log_integral {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ ∫ t in a..b, 1 / Real.log t := by
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hmono : ∀ x ∈ Set.Icc a b, (1 / Real.log b) ≤ 1 / Real.log x := by
    intro x hx
    have hx1 : (1:ℝ) < x := by linarith [hx.1]
    exact one_div_le_one_div_of_le (Real.log_pos hx1) (Real.log_le_log (by linarith) hx.2)
  have := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (one_div_log_intervalIntegrable ha hab) hmono
  rwa [intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_one_div] at this

/-! ### The elementary inequality `9 log²m < 32 √m` -/

theorem nine_log_sq_lt_sqrt {m : ℝ} (hm : 1 ≤ m) : 9 * Real.log m ^ 2 < 32 * Real.sqrt m := by
  have hmpos : (0:ℝ) < m := by linarith
  set u := Real.log m with hu
  have hu0 : 0 ≤ u := Real.log_nonneg hm
  have hsqrt : Real.sqrt m = Real.exp (u / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hmpos]
    congr 1
    rw [hu]; ring
  have hser := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ u / 2 by linarith) 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at hser
  norm_num [Nat.factorial] at hser
  rw [hsqrt]
  nlinarith [hser, hu0, mul_nonneg hu0 (sq_nonneg (u - 5)), sq_nonneg u]

/-- `log m < 2 m^(1/4)`: the same series bound, repackaged for Saito's Lemma 3.8. -/
theorem log_lt_two_rpow {m : ℝ} (hm : 1 ≤ m) : Real.log m < 2 * m ^ ((1:ℝ)/4) := by
  have hmpos : (0:ℝ) < m := by linarith
  have h9 := nine_log_sq_lt_sqrt hm
  set v : ℝ := m ^ ((1:ℝ)/4) with hv
  have hvpos : 0 < v := Real.rpow_pos_of_pos hmpos _
  have hsq : v ^ (2:ℕ) = Real.sqrt m := by
    rw [hv, ← Real.rpow_natCast (m ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hmpos.le,
      Real.sqrt_eq_rpow]
    norm_num
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlt : Real.log m ^ (2:ℕ) < (2 * v) ^ (2:ℕ) := by
    rw [← hsq] at h9
    nlinarith [h9, hvpos]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

/-! ### Lemma 5 for `n ≥ 14` -/

theorem primeBetweenCubes_large (hS : Schoenfeld1976) (hRH : RiemannHypothesis)
    {n : ℕ} (hn : 14 ≤ n) : ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3 := by
  obtain ⟨C, hC⟩ := hS hRH
  have hn14 : (14:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set m : ℝ := (n:ℝ) + 1 with hm
  set a : ℝ := (n:ℝ) ^ 3 with ha
  set b : ℝ := m ^ 3 with hb
  have hm1 : (1:ℝ) ≤ m := by rw [hm]; linarith
  have hmpos : (0:ℝ) < m := by linarith
  have hcube : (14:ℝ) ^ 3 ≤ (n:ℝ) ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num) hn14 3
  have ha2657 : (2657:ℝ) ≤ a := by rw [ha]; norm_num at hcube; linarith
  have hab : a ≤ b := by
    rw [ha, hb, hm]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hb2657 : (2657:ℝ) ≤ b := le_trans ha2657 hab
  have hapos : (0:ℝ) < a := by linarith
  have hbpos : (0:ℝ) < b := by linarith
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  -- floors
  have hfa : ⌊a⌋₊ = n ^ 3 := by
    rw [ha, show ((n:ℝ)) ^ 3 = ((n ^ 3 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hfb : ⌊b⌋₊ = (n + 1) ^ 3 := by
    rw [hb, hm, show ((n:ℝ) + 1) ^ 3 = (((n + 1) ^ 3 : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_natCast]
  -- Schoenfeld at both ends
  have hCa := hC a ha2657
  have hCb := hC b hb2657
  rw [hfa] at hCa
  rw [hfb] at hCb
  -- split the integral
  have hsplit : (∫ t in (2:ℝ)..a, 1 / Real.log t) + (∫ t in a..b, 1 / Real.log t)
      = ∫ t in (2:ℝ)..b, 1 / Real.log t :=
    intervalIntegral.integral_add_adjacent_intervals
      (one_div_log_intervalIntegrable le_rfl (by linarith))
      (one_div_log_intervalIntegrable (by linarith) hab)
  -- the main inequality: `4π(b − a) > √b (log b)²`
  have hpi : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
  have hlogb3 : Real.log b = 3 * Real.log m := by
    rw [hb, Real.log_pow]; push_cast; ring
  have hsqrtb : Real.sqrt b * Real.sqrt m = m ^ 2 := by
    rw [← Real.sqrt_mul (by positivity), hb, show m ^ 3 * m = (m ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hkey : Real.sqrt b * Real.log b ^ 2 < 32 * m ^ 2 := by
    have h9 := nine_log_sq_lt_sqrt hm1
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hbpos
    calc Real.sqrt b * Real.log b ^ 2 = Real.sqrt b * (9 * Real.log m ^ 2) := by
          rw [hlogb3]; ring
      _ < Real.sqrt b * (32 * Real.sqrt m) := by
          exact mul_lt_mul_of_pos_left h9 hsb
      _ = 32 * (Real.sqrt b * Real.sqrt m) := by ring
      _ = 32 * m ^ 2 := by rw [hsqrtb]
  have hbma : b - a = 3 * (n:ℝ) ^ 2 + 3 * (n:ℝ) + 1 := by rw [hb, ha, hm]; ring
  have hmain : Real.sqrt b * Real.log b ^ 2 < 4 * Real.pi * (b - a) := by
    refine lt_of_lt_of_le hkey ?_
    rw [hbma, hm]
    nlinarith [hpi, hn14]
  -- the integral beats the two error terms
  have hsalb : Real.sqrt a * Real.log a ≤ Real.sqrt b * Real.log b := by
    have h1 : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
    have h2 : Real.log a ≤ Real.log b := Real.log_le_log hapos hab
    have := Real.sqrt_nonneg a
    nlinarith [hloga, Real.sqrt_nonneg a]
  have hJ : Real.sqrt a * Real.log a / (8 * Real.pi)
      + Real.sqrt b * Real.log b / (8 * Real.pi) < ∫ t in a..b, 1 / Real.log t := by
    rw [← add_div]
    refine lt_of_lt_of_le ?_ (le_log_integral (by linarith) hab)
    rw [div_lt_div_iff₀ (by positivity) hlogb]
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hbpos
    nlinarith [hsalb, hmain, hlogb, Real.pi_pos]
  -- conclude `π a < π b`
  have hlt : (Nat.primeCounting (n ^ 3) : ℝ) < (Nat.primeCounting ((n + 1) ^ 3) : ℝ) := by
    have h1 := abs_lt.1 hCa
    have h2 := abs_lt.1 hCb
    have e := hsplit
    nlinarith [h1.1, h1.2, h2.1, h2.2, hJ, e]
  have hltn : Nat.primeCounting (n ^ 3) < Nat.primeCounting ((n + 1) ^ 3) := by
    exact_mod_cast hlt
  obtain ⟨p, hp, hp1, hp2⟩ := exists_prime_of_primeCounting_lt hltn
  refine ⟨p, hp, hp1, lt_of_le_of_ne hp2 ?_⟩
  intro hEq
  rw [hEq] at hp
  have h2 : 2 ≤ n + 1 := by omega
  have hdvd : (n + 1) ∣ (n + 1) ^ 3 := dvd_pow_self _ (by norm_num)
  rcases hp.eq_one_or_self_of_dvd (n + 1) hdvd with h | h
  · omega
  · have hlt3 : (n + 1) ^ 1 < (n + 1) ^ 3 := Nat.pow_lt_pow_right h2 (by norm_num)
    rw [pow_one, ← h] at hlt3
    exact absurd hlt3 (lt_irrefl _)

/-! ### Lemma 5, all `n ≥ 1` -/

theorem primeBetweenCubes_of_schoenfeld' (hS : Schoenfeld1976) (hRH : RiemannHypothesis) :
    PrimeBetweenCubesFrom 1 := by
  intro n _
  rcases le_or_gt 14 n with hbig | hsmall
  · exact primeBetweenCubes_large hS hRH hbig
  · interval_cases n
    · exact ⟨2, by norm_num⟩
    · exact ⟨11, by norm_num⟩
    · exact ⟨29, by norm_num⟩
    · exact ⟨67, by norm_num⟩
    · exact ⟨127, by norm_num⟩
    · exact ⟨223, by norm_num⟩
    · exact ⟨347, by norm_num⟩
    · exact ⟨521, by norm_num⟩
    · exact ⟨733, by norm_num⟩
    · exact ⟨1009, by norm_num⟩
    · exact ⟨1361, by norm_num⟩
    · exact ⟨1733, by norm_num⟩
    · exact ⟨2203, by norm_num⟩

end LeanFormalizations.Mills

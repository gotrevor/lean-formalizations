/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.BadCount
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.ClassCount
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Esymm
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Window
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.MertensSums
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Params
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Final
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve
import LeanFormalizations.NumberTheory.Erdos385.LargeSieve
import LeanFormalizations.NumberTheory.Erdos385.ExceptionalWeak.Sieve

/-!
# Erdős #385: pushing the bad-`n` bound toward the framework ceiling (phase E8, moonshot)

`BadCount.badCountExpBound_holds` proves `#{bad n ≤ X} ≪_ε X exp(−(log X)^{1/2−ε})`
unconditionally (`Exceptional.lean` route, `DOOR-EXCEPTIONAL-ERDOS-385.md` §A2).  §A2 "What blocks"
names two bottlenecks and a ceiling `X^{1−o(1)}` (`L ≤ X^{o(1)}`).  This phase attacks both
bottlenecks.  Two frozen targets:

**Both PROVED (2026-10-01), unconditionally** — via the window route in `QuasiPower/` (not the
Freedman plan below, which caps at exponent 1/2).

* `badCountExp_threeQuarters` (milestone, 35%): exponent `3/4 − ε`;
* `badCountQuasiPower_holds` (moonshot, 20%): `X exp(−c log X/(log log X)²)`, i.e. a saving
  `X^{o(1)}` that is a power of `log` away from the ceiling.

A lap that finds a gap has made progress: name the failing step as a sub-lemma, record why it fails
(a `¬` statement or a counterexample if the step is false), and say which weaker exponent survives.

## Route

Keep the dyadic block, `y ≍ log X`, `Q = X^{1/3}`, `s = n mod primorial y`, `U(s)` and the
forbidden-class step exactly as in `Exceptional.lean` (reuse `Exceptional/*`, `ExceptionalWeak/*`;
the weak large sieve `LSWith` suffices).  Change two steps.

1. **Large sieve with many primes** (step 2).  Take `d` = products of `j` distinct primes of
   `pool y R`, `R = ⌊Q^{1/j}⌋`, with `j ≍ (log X)^{θ}` (milestone `θ = 3/4`) or
   `j ≍ log X/(log log X)²` (moonshot), and `K ≍ y/log y` classes per prime.  `Exceptional/Analytic`
   (`pool_weight_ge`, `rho_bound`, `eventually_L_conditions`) is written for `j ≍ (log X)^{1/2}`;
   generalize it.  Need `R > y`, i.e. `j log y < (1/3) log X`; Mertens gives
   `Σ_{p ∈ pool} 1/p ≥ log(log R/log y) − O(1)`, and `L ≥ (K Σ 1/p/(e j))^j` once `K Σ 1/p ≥ e² j`.
   At the moonshot `j`, `K/j ≍ log log X` and `L ≥ exp(c log X · log log log X/(log log X)²)`.
2. **Tail of `u(s)` beyond McDiarmid** (step 3), the crux.  McDiarmid charges the worst-case
   influence `y/q` of a prime `q` near `z = y^{1/2}`, so the tail is `exp(−c y^{1/2−ε})`; to beat
   `1/2` the tail must be `≤ exp(−y^{θ})`.  Plan: a Bernstein/Freedman martingale over the primes
   `q ∈ (z, y]` revealed in increasing order, with the increment at `q` = the number of surviving
   positions in the class `s mod q`.  Its conditional variance is `≤ (max class count)·|U|/q`, and
   on a **good event** where the survivors are equidistributed mod each `q` (class counts
   `≤ 2|U|/q + y^{1/4}`), the increments are `≤ 2y/(q log y) + y^{1/4}`.  Freedman then gives
   `exp(−c y^{3/4}/log y)` for the deviation `≍ y/log y`, provided the good event fails with
   probability `≤ exp(−y^{3/4})`.  The good event is itself a tail bound for sifted counts in
   progressions of length `y/q` (a smaller copy of the same problem: recurse, or bound it with the
   fundamental lemma plus McDiarmid on the primes `≤ q`).  For the moonshot, iterate scales.
   Finite-average Freedman/Bernstein is not in mathlib: prove it as a named theorem by the same
   finite-average induction as `McDiarmid/Core.lean` (Bernstein's mgf lemma
   `E e^{λD} ≤ exp(λ² v (e^{λb} − 1 − λb)/(λb)²)` in place of Hoeffding's lemma).
3. **Sum** as in `Exceptional/Main`, `Terms`.

Sub-lemmas worth naming early: `freedmanFinite` (2), `goodEvent_tail` (2), `pool_weight_ge_general`
(1).  If `goodEvent_tail` is false at the claimed strength, record the counterexample and the
exponent it permits.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

/-- Milestone: the bad set has size `≪_ε X exp(−(log X)^{3/4−ε})`. -/
def BadCountExpThreeQuarters : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 3 / 4 → ∃ C : ℝ, ∀ X : ℕ, 3 ≤ X →
    ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ)
      ≤ C * X * Real.exp (-(Real.log X) ^ ((3 : ℝ) / 4 - ε))

/-- Moonshot: the bad set has size `≪ X exp(−c log X/(log log X)²)`. -/
def BadCountQuasiPower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℕ, 16 ≤ X →
    ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ)
      ≤ C * X * Real.exp (-(c * Real.log X / Real.log (Real.log X) ^ 2))

set_option maxHeartbeats 1000000 in
/-- **Moonshot proved**: `#bad ≤ C X exp(−log X/(32400 (log log X)²))`.  Route: `QuasiPower.bound_m`
with `m = ⌊(log₂ X/8)^{1/4}⌋`, then `QuasiPower.term_pool`, `term_main`, `exp_target_ge`. -/
theorem badCountQuasiPower_holds : BadCountQuasiPower := by
  classical
  obtain ⟨C, hC1, hCl⟩ := Exceptional.exists_lsWith arithLargeSieveWeak_holds
  obtain ⟨m₀, hb⟩ := QuasiPower.bound_m hCl (by linarith) linearSieveIntervalLower_holds
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = max m₀ 18000 := ⟨_, rfl⟩
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℕ, X₁ = 2 ^ (8 * M ^ 4 + 9) := ⟨_, rfl⟩
  refine ⟨1 / 32400, by norm_num, max (2 + 2 * C) X₁, fun X hX => ?_⟩
  have hset : {n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n} =
      ↑((Finset.Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n) := by
    ext n; simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h1⟩, h2, h3⟩
    · rintro ⟨⟨_, h1⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  rw [hset, Set.ncard_coe_finset]
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  rw [← hL]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ℓ = Nat.log 2 X := ⟨_, rfl⟩
  have hℓX : 2 ^ ℓ ≤ X := by rw [hℓ]; exact Nat.pow_log_le_self 2 (by omega)
  have hXℓ : X < 2 ^ (ℓ + 1) := by rw [hℓ]; exact Nat.lt_pow_succ_log_self (by norm_num) X
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hLlo : (ℓ : ℝ) * Real.log 2 ≤ L := by
    rw [hL, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hℓX)
  have hLhi : L < ((ℓ + 1 : ℕ) : ℝ) := by
    have : L < ((ℓ + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [hL, ← Real.log_pow]
      exact Real.log_lt_log hX0 (by exact_mod_cast hXℓ)
    have h0 : (0 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = Nat.sqrt (Nat.sqrt (ℓ / 8)) := ⟨_, rfl⟩
  have hm4 : 8 * m ^ 4 ≤ ℓ := by
    have h1 : m ^ 2 ≤ Nat.sqrt (ℓ / 8) := by rw [hm]; exact Nat.sqrt_le' _
    have h2 : Nat.sqrt (ℓ / 8) ^ 2 ≤ ℓ / 8 := Nat.sqrt_le' _
    have h3 : (m ^ 2) ^ 2 ≤ Nat.sqrt (ℓ / 8) ^ 2 := Nat.pow_le_pow_left h1 2
    have : m ^ 4 = (m ^ 2) ^ 2 := by ring
    omega
  have hm4' : ℓ + 1 ≤ 8 * (m + 1) ^ 4 + 8 := by
    have h1 : Nat.sqrt (ℓ / 8) < (m + 1) ^ 2 := by
      rw [hm]; exact Nat.lt_succ_sqrt' _
    have h2 : ℓ / 8 < (Nat.sqrt (ℓ / 8) + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have h3 : (Nat.sqrt (ℓ / 8) + 1) ^ 2 ≤ ((m + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
    have : (m + 1) ^ 4 = ((m + 1) ^ 2) ^ 2 := by ring
    omega
  have hcard : (((Finset.Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ) ≤ X := by
    have := (Finset.card_filter_le (Finset.Icc 1 X) fun n => 5 ≤ n ∧ Bad n)
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    exact_mod_cast this
  by_cases hmM : M ≤ m
  · have hm0 : m₀ ≤ m := le_trans (by rw [hM]; exact le_max_left _ _) hmM
    have hm18 : 18000 ≤ m := le_trans (by rw [hM]; exact le_max_right _ _) hmM
    have hX8 : 2 ^ (8 * m ^ 4) ≤ X := le_trans (Nat.pow_le_pow_right (by norm_num) hm4) hℓX
    have hbd := hb X m hm0 hX8
    have hP := QuasiPower.term_pool (by omega) hX8
    have hT := QuasiPower.term_main hm18
    have hmR : (18000 : ℝ) ≤ m := by exact_mod_cast hm18
    have hLm1 : (m : ℝ) ^ 4 ≤ L := by
      have : ((8 * m ^ 4 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast hm4
      push_cast at this
      have hm40 : (0 : ℝ) ≤ (m : ℝ) ^ 4 := by positivity
      nlinarith
    have hLm2 : L ≤ 137 * (m : ℝ) ^ 4 := by
      have h1 : ((ℓ + 1 : ℕ) : ℝ) ≤ ((8 * (m + 1) ^ 4 + 8 : ℕ) : ℝ) := by exact_mod_cast hm4'
      push_cast at h1
      have h2 : ((m : ℝ) + 1) ^ 4 ≤ 16 * (m : ℝ) ^ 4 := by
        have : (m : ℝ) + 1 ≤ 2 * m := by linarith
        calc ((m : ℝ) + 1) ^ 4 ≤ (2 * m) ^ 4 := by gcongr
          _ = 16 * (m : ℝ) ^ 4 := by ring
      have h3 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ (by linarith)
      push_cast at hLhi
      linarith
    have hE := QuasiPower.exp_target_ge (by linarith) hLm1 hLm2
    obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = Real.exp (-((m : ℝ) ^ 4 / Real.log m ^ 2) / 3600) := ⟨_, rfl⟩
    rw [← hEd] at hP hT hE
    have hE0 : 0 ≤ E := by rw [hEd]; positivity
    have hC0 : (0 : ℝ) ≤ C := by linarith
    have hXX : (0 : ℝ) ≤ X := hX0.le
    have h3 : (m : ℝ) ^ 4 * (C * (X + X) * (23 / 25 : ℝ) ^ (m ^ 4 / (16 * (Nat.log 2 m + 1) ^ 2)))
        ≤ 2 * C * X * E := by
      have : (m : ℝ) ^ 4 * (C * (X + X) * (23 / 25 : ℝ) ^ (m ^ 4 / (16 * (Nat.log 2 m + 1) ^ 2)))
          = 2 * C * X * ((m : ℝ) ^ 4 * (23 / 25 : ℝ) ^ (m ^ 4 / (16 * (Nat.log 2 m + 1) ^ 2))) := by
        ring
      rw [this]; gcongr
    calc _ ≤ _ := hbd
      _ ≤ 2 * X * E + 2 * C * X * E := by linarith
      _ = (2 + 2 * C) * X * E := by ring
      _ ≤ max (2 + 2 * C) X₁ * X * Real.exp (-(1 / 32400 * L / Real.log L ^ 2)) := by
        gcongr; exact le_max_left _ _
  · -- small `X`: `X < X₁`
    have hXX₁ : X ≤ X₁ := by
      have h1 : m + 1 ≤ M := by omega
      have h2 : (m + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left h1 4
      have h3 : 2 ^ (ℓ + 1) ≤ 2 ^ (8 * M ^ 4 + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hX₁]; omega
    have hLe : Real.exp 1 ≤ L := by
      have h16 : Real.log 16 ≤ L := by
        rw [hL]; exact Real.log_le_log (by norm_num) (by exact_mod_cast hX)
      have : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
      linarith [Real.exp_one_lt_d9]
    have hL16 : 1 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]; exact hLe
    have hL0 : 0 ≤ L := by linarith [Real.exp_pos 1]
    have hEx : Real.exp (-L) ≤ Real.exp (-(1 / 32400 * L / Real.log L ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hsq : 1 ≤ Real.log L ^ 2 := one_le_pow₀ hL16
      rw [neg_le_neg_iff, div_le_iff₀ (by linarith)]
      nlinarith
    have hXe : (X : ℝ) * Real.exp (-L) = 1 := by
      rw [Real.exp_neg, hL, Real.exp_log hX0]; field_simp
    have hX₁R : (X : ℝ) ≤ X₁ := by exact_mod_cast hXX₁
    calc _ ≤ (X : ℝ) := hcard
      _ ≤ X₁ := hX₁R
      _ = X₁ * (X * Real.exp (-L)) := by rw [hXe, mul_one]
      _ ≤ max (2 + 2 * C) X₁ * X * Real.exp (-(1 / 32400 * L / Real.log L ^ 2)) := by
        rw [← mul_assoc]; gcongr; exact le_max_right _ _

/-- `L^α ≤ c L/(log L)² + K` for `L ≥ e`, any `0 < α < 3/4`, `c > 0`. -/
theorem rpow_le_quasi {α c : ℝ} (hα0 : 0 < α) (hα : α < 3 / 4) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, Real.exp 1 ≤ L → L ^ α ≤ c * L / Real.log L ^ 2 + K := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 3 / 4 - α := ⟨_, rfl⟩
  have hε0 : 0 < ε := by linarith
  refine ⟨(64 / c) ^ ((3 / 4) / ε), by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hL1 : 1 ≤ L := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hL
  have hlog : 1 ≤ Real.log L := by rw [Real.le_log_iff_exp_le hL0]; exact hL
  have h8 : Real.log L ≤ 8 * L ^ ((1 : ℝ) / 8) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hL0 ((1 : ℝ) / 8))
    rw [Real.log_rpow hL0] at h
    linarith
  have hsq : Real.log L ^ 2 ≤ 64 * L ^ ((1 : ℝ) / 4) := by
    have : (L ^ ((1 : ℝ) / 8)) ^ 2 = L ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    nlinarith
  have hsplit : L = L ^ ((1 : ℝ) / 4) * L ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h14 : 0 < L ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have h34 : 0 < L ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have hmain : c / 64 * L ^ ((3 : ℝ) / 4) ≤ c * L / Real.log L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc c / 64 * L ^ ((3 : ℝ) / 4) * Real.log L ^ 2
        ≤ c / 64 * L ^ ((3 : ℝ) / 4) * (64 * L ^ ((1 : ℝ) / 4)) := by gcongr
      _ = c * (L ^ ((1 : ℝ) / 4) * L ^ ((3 : ℝ) / 4)) := by ring
      _ = c * L := by rw [← hsplit]
  have hq0 : 0 ≤ c * L / Real.log L ^ 2 := by positivity
  have hαε : L ^ α * L ^ ε = L ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hL0, hε]; ring_nf
  have hLε : 0 < L ^ ε := Real.rpow_pos_of_pos hL0 _
  by_cases hcase : 64 / c ≤ L ^ ε
  · have : L ^ α ≤ c / 64 * L ^ ((3 : ℝ) / 4) := by
      rw [← hαε]
      have hα' : 0 < L ^ α := Real.rpow_pos_of_pos hL0 _
      have : 64 ≤ c * L ^ ε := by rwa [div_le_iff₀ hc, mul_comm] at hcase
      nlinarith
    have : (0 : ℝ) ≤ (64 / c) ^ ((3 / 4) / ε) := by positivity
    linarith
  · push_neg at hcase
    have h1 : L ^ α ≤ L ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h2 : L ^ ((3 : ℝ) / 4) = (L ^ ε) ^ ((3 / 4) / ε) := by
      rw [← Real.rpow_mul hL0.le]; congr 1; field_simp
    have h3 : (L ^ ε) ^ ((3 / 4) / ε) ≤ (64 / c) ^ ((3 / 4) / ε) :=
      Real.rpow_le_rpow hLε.le hcase.le (by positivity)
    linarith

/-- **Milestone** (from the moonshot): exponent `3/4 − ε`. -/
theorem badCountExp_threeQuarters : BadCountExpThreeQuarters := by
  intro ε hε hε2
  obtain ⟨c, hc, C, hC⟩ := badCountQuasiPower_holds
  obtain ⟨K, hK0, hK⟩ := rpow_le_quasi (α := 3 / 4 - ε) (by linarith) (by linarith) hc
  refine ⟨max (max C 0 * Real.exp K) (Real.exp 16), fun X hX => ?_⟩
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hcard : ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ) ≤ X := by
    have : {n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n} ⊆ ↑(Finset.Icc 1 X) := by
      intro n hn; simp only [Set.mem_setOf_eq] at hn
      simp only [Finset.coe_Icc, Set.mem_Icc]; omega
    have h := Set.ncard_le_ncard this (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Nat.card_Icc, add_tsub_cancel_right] at h
    exact_mod_cast h
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  rw [← hL]
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hX0]
    have : (3 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [Real.exp_one_lt_d9]
  have hLa : 0 ≤ L ^ ((3 : ℝ) / 4 - ε) := Real.rpow_nonneg (by linarith) _
  by_cases h16 : 16 ≤ X
  · have hCX := hC X h16
    rw [← hL] at hCX
    have hLe : Real.exp 1 ≤ L := by
      have h16' : Real.log 16 ≤ L := by
        rw [hL]; exact Real.log_le_log (by norm_num) (by exact_mod_cast h16)
      have : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
      linarith [Real.exp_one_lt_d9, Real.log_two_gt_d9]
    have hk := hK L hLe
    have hE : Real.exp (-(c * L / Real.log L ^ 2)) ≤
        Real.exp K * Real.exp (-L ^ ((3 : ℝ) / 4 - ε)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    have hE0 : 0 ≤ Real.exp (-(c * L / Real.log L ^ 2)) := (Real.exp_pos _).le
    calc _ ≤ C * X * Real.exp (-(c * L / Real.log L ^ 2)) := hCX
      _ ≤ max C 0 * X * Real.exp (-(c * L / Real.log L ^ 2)) := by
        gcongr; exact le_max_left _ _
      _ ≤ max C 0 * X * (Real.exp K * Real.exp (-L ^ ((3 : ℝ) / 4 - ε))) := by
        gcongr
      _ = max C 0 * Real.exp K * X * Real.exp (-L ^ ((3 : ℝ) / 4 - ε)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push_neg at h16
    have hLX : L ≤ 16 := by
      have := Real.log_le_sub_one_of_pos hX0
      have : (X : ℝ) < 16 := by exact_mod_cast h16
      linarith
    have hpow : L ^ ((3 : ℝ) / 4 - ε) ≤ L := by
      calc L ^ ((3 : ℝ) / 4 - ε) ≤ L ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
        _ = L := Real.rpow_one L
    have h1 : 1 ≤ Real.exp 16 * Real.exp (-L ^ ((3 : ℝ) / 4 - ε)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc _ ≤ (X : ℝ) := hcard
      _ ≤ X * (Real.exp 16 * Real.exp (-L ^ ((3 : ℝ) / 4 - ε))) := le_mul_of_one_le_right hX0.le h1
      _ = Real.exp 16 * X * Real.exp (-L ^ ((3 : ℝ) / 4 - ε)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end LeanFormalizations.Erdos385

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Exceptional
import LeanFormalizations.NumberTheory.Erdos385.LargeSieve
import LeanFormalizations.NumberTheory.Erdos385.McDiarmid
import LeanFormalizations.NumberTheory.Erdos385.ExceptionalWeak.Main

/-!
# Erdős #385: the exceptional-set bound from the linear sieve alone (phase E4d)

Two frozen statements:
* `badCountExpBound_of_weak : ArithLargeSieveWeak → LinearSieveIntervalLower → BadCountExpBound`;
* `badCountExpBound_of_linearSieve : LinearSieveIntervalLower → BadCountExpBound` (one line from the
  first, `arithLargeSieveWeak_holds` (`LargeSieve.lean`) and nothing else).

## Route (90%)

E4's proof (`Exceptional/`) uses the sharp `ArithLargeSieve` only through `sieve_count`
(`Exceptional/Sieve.lean`), and through it `bad_count_le` and `eventually_bad_le`.  Add
constant-carrying copies `sieve_count_weak`, `bad_count_le_weak`, `eventually_bad_le_weak` taking
`ArithLargeSieveWeak` (constant `C`): the sieved term gains a factor `C`, which the final bound
absorbs because the large-sieve saving `L ≥ exp((log X)^{1/2})` beats any constant.  Feed
`mcDiarmidFinite_holds` for McDiarmid.  Do not edit E4's frozen statements; copy and generalise.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **The bad set is exponentially thin**, with the weak-constant large sieve. -/
theorem badCountExpBound_of_weak (h1 : ArithLargeSieveWeak) (h2 : LinearSieveIntervalLower) :
    BadCountExpBound := by
  classical
  obtain ⟨C, hC, hCl⟩ := Exceptional.exists_lsWith h1
  intro ε hε hε2
  obtain ⟨X₀, hX₀⟩ := Exceptional.eventually_bad_le_weak hCl hC h2 mcDiarmidFinite_holds hε hε2
  refine ⟨max (3 + 2 * C) (Real.exp ((Real.log X₀) ^ ((1 : ℝ) / 2 - ε))), fun X hX => ?_⟩
  have hset : {n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n} =
      ↑((Finset.Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n) := by
    ext n; simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h1⟩, h2, h3⟩
    · rintro ⟨⟨_, h1⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  rw [hset, Set.ncard_coe_finset]
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hE0 : 0 < Real.exp (-(Real.log X) ^ ((1 : ℝ) / 2 - ε)) := Real.exp_pos _
  by_cases hXX : X₀ ≤ X
  · calc _ ≤ (3 + 2 * C) * X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 2 - ε)) := hX₀ X hXX
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hcard : (((Finset.Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ) ≤ X := by
      have := (Finset.card_filter_le (Finset.Icc 1 X) fun n => 5 ≤ n ∧ Bad n)
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    have hmono : (Real.log X) ^ ((1 : ℝ) / 2 - ε) ≤ (Real.log X₀) ^ ((1 : ℝ) / 2 - ε) :=
      Real.rpow_le_rpow hlog (Real.log_le_log (by exact_mod_cast (show 0 < X by omega))
        (by exact_mod_cast (show X ≤ X₀ by omega))) (by linarith)
    have : 1 ≤ Real.exp ((Real.log X₀) ^ ((1 : ℝ) / 2 - ε)) *
        Real.exp (-(Real.log X) ^ ((1 : ℝ) / 2 - ε)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc _ ≤ (X : ℝ) := hcard
      _ ≤ X * (Real.exp ((Real.log X₀) ^ ((1 : ℝ) / 2 - ε)) *
          Real.exp (-(Real.log X) ^ ((1 : ℝ) / 2 - ε))) := le_mul_of_one_le_right hX0 this
      _ ≤ max (3 + 2 * C) (Real.exp ((Real.log X₀) ^ ((1 : ℝ) / 2 - ε))) * X *
          Real.exp (-(Real.log X) ^ ((1 : ℝ) / 2 - ε)) := by
        rw [← mul_assoc, mul_comm (X : ℝ)]
        gcongr; exact le_max_right _ _


/-- **The bad set is exponentially thin, assuming only the linear-sieve lower bound.** -/
theorem badCountExpBound_of_linearSieve (h : LinearSieveIntervalLower) : BadCountExpBound :=
  badCountExpBound_of_weak arithLargeSieveWeak_holds h

end LeanFormalizations.Erdos385

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Schanuel ⇒ `log π`, `π^e`, `π^π` (phase 23)

Conditional on `SchanuelConjecture`.  None of these is known unconditionally; even the
irrationality of `π^e` is open.  Pattern: bootstrap Schanuel twice.

1. `z = (1, iπ, log π)`, with exponentials `e, −1, π`.  Here `1, iπ, log π` are `ℚ`-linearly
   independent (`log π` is real and irrational, since `π` is transcendental, and `iπ` is purely
   imaginary), so `trdeg ℚ(π, log π, e) ≥ 3`: **`e, π, log π` are algebraically independent.**
2. `z = (1, iπ, log π, e·log π)`, with exponentials `e, −1, π, π^e`.  Linear independence of the `z` over
   `ℚ` follows from step 1 (a relation would put `log π ∈ ℚ(e)`).  Hence `trdeg ℚ(e, π, log π, π^e) ≥ 4`,
   and **`π^e` is transcendental**, indeed algebraically independent from `e, π, log π`.
3. The same with `π·log π`: **`π^π` is transcendental.**

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.NumberTheory.Transcendence.Schanuel

namespace LeanFormalizations.Schanuel

open LeanFormalizations.Literature

theorem algebraicIndependent_exp_one_pi_log_pi (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ ![Real.exp 1, Real.pi, Real.log Real.pi] := by
  sorry

theorem transcendental_log_pi (hS : SchanuelConjecture) : Transcendental ℚ (Real.log Real.pi) := by
  sorry

theorem algebraicIndependent_pi_rpow_exp_one (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ
      ![Real.exp 1, Real.pi, Real.log Real.pi, Real.pi ^ Real.exp 1] := by
  sorry

theorem transcendental_pi_rpow_exp_one (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.pi ^ Real.exp 1) := by
  sorry

theorem transcendental_pi_rpow_pi (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.pi ^ Real.pi) := by
  sorry

end LeanFormalizations.Schanuel

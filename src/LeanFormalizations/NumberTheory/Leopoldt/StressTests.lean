/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Stress tests for the Leopoldt statement (phase 26)

`Literature.LeopoldtConjecture` is Ren's design; its faithfulness argument is in the file header,
at about 75%.  These tests are meant to catch a mistake.
* **Positive**: when the unit rank is 0 (`ℚ`, imaginary quadratic fields) the conjecture must
  hold, because every multiplicatively independent family of units is empty.
  `leopoldt_of_rank_zero` checks that the statement is not accidentally false.
* **Negative (the hypotheses bite)**: drop the multiplicative-independence hypothesis and the
  statement must become FALSE.  For `ℚ`, take `ε = −1`, `mₙ = 2`, `a = 2`.  Then `(−1)² = 1`, but
  `a ≠ 0`.  `not_leopoldtNoIndep_rat` checks that the independence clause is doing work.
* **Stretch (not frozen)**: Leopoldt for a real quadratic field (unit rank 1), e.g. `ℚ(√2)` at
  `p = 7`.  It reduces to "`ε^a = 1` with `a ∈ ℤ_p` forces `a = 0`" for the fundamental unit, which
  holds because `ε` is not a root of unity.  This would be a genuinely nontrivial positive test.
  Add it if the rank-0 cases go quickly.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Leopoldt

namespace LeanFormalizations.Leopoldt

open NumberField IsDedekindDomain Filter Topology LeanFormalizations.Literature

/-- The broken variant: `LeopoldtConjecture` with the independence hypothesis removed. -/
def LeopoldtNoIndep (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (r : ℕ) (ε : Fin r → (𝓞 K)ˣ) (a : Fin r → ℤ_[p]) (m : ℕ → Fin r → ℤ),
    (∀ i, Tendsto (fun n ↦ ((m n i : ℤ) : ℤ_[p])) atTop (𝓝 (a i))) →
    (∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal →
      Tendsto (fun n ↦ algebraMap K (v.adicCompletion K)
        (∏ i, (((ε i : 𝓞 K) : K)) ^ (m n i))) atTop (𝓝 1)) →
    a = 0

theorem leopoldt_of_rank_zero (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (h : Units.rank K = 0) : LeopoldtConjecture K p := by
  sorry

theorem not_leopoldtNoIndep_rat (p : ℕ) [Fact p.Prime] : ¬ LeopoldtNoIndep ℚ p := by
  sorry

end LeanFormalizations.Leopoldt

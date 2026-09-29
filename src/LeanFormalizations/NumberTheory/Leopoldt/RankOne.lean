/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Leopoldt's conjecture in unit rank 1: the first nontrivial test (phase 27)

The phase-26 tests only showed that the statement is not accidentally false (rank 0 is
degenerate) and that its hypotheses do work.  This file is the test with bite.  Its field is
`ℚ(ζ₈) = CyclotomicField 8 ℚ`: degree 4, totally imaginary, so `r₂ = 2` and the unit rank is `1`.
Mathlib already knows it is a number field.  The prime is `p = 7`, which is unramified (the
conductor is 8).  Leopoldt is **known** here (the field is abelian: Ax–Brumer), so this checks our
statement against a true case.  It is not new math.

Route, from the phase-26 handoff: mathlib at our pin has no p-adic logarithm and no `ℤ_p`-module
structure on principal local units.  Build the minimum:
1. the principal units `U⁽¹⁾ ⊂ (v.adicCompletion K)ˣ`, and the `ℤ_p`-action `ℤ_p × U⁽¹⁾ → U⁽¹⁾` by
   continuity from `ℤ`-powers (`u^{m} ≡ u^{m'}` when `m ≡ m' mod p^k`);
2. torsion-freeness of `U⁽¹⁾` for odd unramified `p`, from the valuation of `(1+x)^p − 1`;
3. the rank-1 case: a fundamental unit `η` has `π(η)` of infinite order, so `π(η)^a = 1` forces
   `a = 0`, and the Lean statement's hypotheses supply exactly that equation, as in the header
   argument of `Literature/Leopoldt.lean`.

Split into named leaves freely; infrastructure lemmas are welcome.  Frozen: the statements below,
every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Leopoldt

namespace LeanFormalizations.Leopoldt

open NumberField LeanFormalizations.Literature

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem rank_cyclotomic_eight : Units.rank (CyclotomicField 8 ℚ) = 1 := by
  sorry

theorem leopoldt_cyclotomic_eight_seven : LeopoldtConjecture (CyclotomicField 8 ℚ) 7 := by
  sorry

end LeanFormalizations.Leopoldt

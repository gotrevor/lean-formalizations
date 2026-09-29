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

## What the route turned out to be (phase 27, 2026-09-29)

The phase-26 plan called for the `ℤ_p`-action on principal units built by continuity, plus
torsion-freeness of `U⁽¹⁾` for odd unramified `p`.  **None of that is needed**, and the result
proved is much stronger than the cyclotomic case: `leopoldt_of_rank_le_one` in
`Leopoldt/PrincipalUnits.lean` is Leopoldt for **every** number field of unit rank `≤ 1` and
**every** prime, with no abelian hypothesis, no `p` odd, no unramifiedness.

Two observations collapse the problem.
* The exponent `N` that makes a unit principal at `v` is prime to `p`, hence a unit of `ℤ_p`, so
  proving `N·a = 0` suffices and one may work with the exponents `N · m n` throughout.  No
  residue-class subsequence (as in the `Literature/Leopoldt.lean` header) is required.
* On a principal unit, raising to an exponent **prime to `p`** does not move the valuation at all:
  `W (θ ^ t − 1) = W (θ − 1)` (`valuation_zpow_sub_one`).  So only the `p`-part of the exponent can
  push `ε ^ m` towards `1`, and `a ≠ 0` in `ℤ_p` bounds that `p`-part (`exists_pow_split`).  The
  valuations `W (ε ^ (N · m n) − 1)` are therefore ≥ the nonzero value `W (ε ^ (N p^k) − 1)`, by
  antitonicity — contradicting the local limit.

Rank `≤ 1` enters only through `card_le_rank`: multiplicative independence of `r` units makes them
`ℤ`-linearly independent in `Additive (𝓞 K)ˣ`, whose `ℤ`-rank is `rank K`.  So `r ≤ 1`, and a
single unit of infinite order is all the local lemma ever sees.  For `r ≥ 2` the local lemma is
genuinely false without Baker–Brumer, which is exactly where the open case of Leopoldt lives.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.NumberTheory.Leopoldt.PrincipalUnits

namespace LeanFormalizations.Leopoldt

open NumberField LeanFormalizations.Literature

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem rank_cyclotomic_eight : Units.rank (CyclotomicField 8 ℚ) = 1 := by
  haveI : IsCyclotomicExtension {8} ℚ (CyclotomicField 8 ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 8 ℚ
  dsimp only [Units.rank]
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 8) (CyclotomicField 8 ℚ) (by decide),
    zero_add, IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 8]
  rfl

theorem leopoldt_cyclotomic_eight_seven : LeopoldtConjecture (CyclotomicField 8 ℚ) 7 :=
  leopoldt_of_rank_le_one 7 (le_of_eq rank_cyclotomic_eight)

end LeanFormalizations.Leopoldt

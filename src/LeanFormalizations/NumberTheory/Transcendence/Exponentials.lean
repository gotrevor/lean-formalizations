/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Four and six exponentials, and more of Schanuel

Phase 16.  It continues `Schanuel.lean`: write down what follows from what we believe.

* **Schanuel ⇒ four exponentials.**  Suppose all four `e^{xᵢyⱼ}` are algebraic.  Then
  `λᵢⱼ = xᵢyⱼ` are logarithms of algebraic numbers satisfying `λ₀₀λ₁₁ = λ₀₁λ₁₀`.  Schanuel, applied
  to a `ℚ`-basis of their span, makes that basis algebraically independent (the exponentials are
  algebraic), and the quadratic relation then forces a rank drop contradicting the independence
  of `x` and `y`.  Waldschmidt (2000) Exercise 1.8; Waldschmidt (2023) §2 sketches it with Roy's
  reformulation.  Case analysis on the dimension of `span_ℚ {λᵢⱼ}` (3 or 4) is the expected
  shape.
* **Four exponentials ⇒ `2^t` or `3^t` transcendental** for irrational `t`: take
  `x = (1, t)`, `y = (log 2, log 3)`.  This is formal-conjectures' `two_pow_three_pow_transcendental`.
* **Six exponentials ⇒ (unconditional)**: if `p₁^t, p₂^t, p₃^t` are integers for three distinct
  primes, then `t ∈ ℕ`.  For irrational `t`, use `x = (1, t)` and `y = log pᵢ`
  (`linearIndependent_log_primes`, proved in phase 15).  For rational `t = a/b`, use
  elementary unique factorization.
* **More Schanuel** (`PENDING_WORK.md`, phase 15): `e, e^e, e^{e^e}` algebraically independent;
  `π` together with logs of distinct primes; `e + log 2`.  Reuse the phase-15 toolkit.

Split into named leaves freely.  Frozen: every statement below, every earlier name, all of
`Literature/`.
-/
import LeanFormalizations.Literature.Exponentials
import LeanFormalizations.NumberTheory.Transcendence.Schanuel

namespace LeanFormalizations.Exponentials

open LeanFormalizations.Literature

/-- Schanuel ⇒ the four exponentials conjecture. -/
theorem fourExponentials_of_schanuel (hS : SchanuelConjecture) : FourExponentialsConjecture := by
  sorry

/-- Four exponentials ⇒ for irrational `t`, `2^t` or `3^t` is transcendental. -/
theorem two_rpow_or_three_rpow_transcendental (h4 : FourExponentialsConjecture) {t : ℝ}
    (ht : Irrational t) :
    Transcendental ℚ ((2 : ℝ) ^ t) ∨ Transcendental ℚ ((3 : ℝ) ^ t) := by
  sorry

/-- **Unconditional**, from the six exponentials theorem: if `pᵢ^t` is an integer for three
distinct primes `pᵢ`, then `t` is a natural number. -/
theorem eq_nat_of_three_primes_rpow (h6 : SixExponentials) {t : ℝ} {p : Fin 3 → Nat.Primes}
    (hp : Function.Injective p) (h : ∀ i, ∃ n : ℕ, ((p i : ℕ) : ℝ) ^ t = n) :
    ∃ n : ℕ, t = n := by
  sorry

/-- Schanuel ⇒ `e, e^e, e^{e^e}` are algebraically independent: take `z = (1, e, e^e)`. -/
theorem algebraicIndependent_exp_tower_three (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ
      ![Real.exp 1, Real.exp (Real.exp 1), Real.exp (Real.exp (Real.exp 1))] := by
  sorry

/-- Schanuel ⇒ `π` together with the logarithms of distinct primes are algebraically
independent: take `z = (iπ, log p₁, …, log pₙ)`. -/
theorem algebraicIndependent_pi_log_primes (hS : SchanuelConjecture) {n : ℕ}
    (p : Fin n → Nat.Primes) (hp : Function.Injective p) :
    AlgebraicIndependent ℚ
      (Fin.cons Real.pi fun i ↦ Real.log (p i : ℕ) : Fin (n + 1) → ℝ) := by
  sorry

/-- Schanuel ⇒ `e + log 2` is transcendental: `e` and `log 2` are algebraically independent,
by taking `z = (1, log 2)`. -/
theorem transcendental_exp_one_add_log_two (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.exp 1 + Real.log 2) := by
  sorry

end LeanFormalizations.Exponentials

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Weakest hypotheses: what already follows from Conjecture 1 (phase 24)

Conjecture 1 (`AlgIndepLogsConjecture`, "weak Schanuel": logarithms of algebraic numbers are
algebraically independent) is the special case of Schanuel where every `e^{zᵢ}` is algebraic.
The fact graph (`FACT-GRAPH.md`) shows several results derived from full Schanuel that should
need only Conjecture 1, and theorems (Gelfond–Schneider, Baker) that Conjecture 1 should imply.
Re-deriving from the weaker node sharpens the graph: it records the *least* hypothesis each fact
needs.

* Conj 1 ⇒ Gelfond–Schneider: if `a^b = c` is algebraic, then `λ₁ = log a` and `λ₂ = b·log a` are
  logarithms of algebraic numbers, `ℚ`-independent since `b` is irrational, yet `λ₂ − bλ₁ = 0` is
  an algebraic relation over `ℚ̄`.  Take the norm to get a relation over `ℚ`.
* Conj 1 ⇒ Baker (inhomogeneous, `Baker1966`): a `ℚ̄`-linear relation with nonzero constant term
  among logarithms, after passing to a `ℚ`-basis, is an algebraic relation.
* Conj 1 ⇒ logarithms of distinct primes are algebraically independent (phase 15 used Schanuel).
* Conj 1 ⇒ `π` together with the logarithms of distinct primes is algebraically independent
  (`iπ` is a logarithm of `−1`; phase 16 used Schanuel).
* Conj 1 ⇒ strong four exponentials.  ⚠️ **Ren, about 70% confident, not checked against a
  source.**  Waldschmidt (2005a) lists consequences of the strong four exponentials problem; that
  it is itself a special case of Conj 1 is my reading.  If it is false or underivable, record why:
  that is an advance.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.NumberTheory.Transcendence.Waldschmidt2023
import LeanFormalizations.NumberTheory.Transcendence.Exponentials

namespace LeanFormalizations.Waldschmidt2023

open LeanFormalizations.Literature

theorem gelfondSchneider_of_algIndepLogs (h : AlgIndepLogsConjecture) : GelfondSchneider1934 := by
  sorry

theorem baker1966_of_algIndepLogs (h : AlgIndepLogsConjecture) : Baker1966 := by
  sorry

theorem algebraicIndependent_log_primes_of_algIndepLogs (h : AlgIndepLogsConjecture) {n : ℕ}
    (p : Fin n → Nat.Primes) (hp : Function.Injective p) :
    AlgebraicIndependent ℚ fun i ↦ Real.log (p i : ℕ) := by
  sorry

theorem algebraicIndependent_pi_log_primes_of_algIndepLogs (h : AlgIndepLogsConjecture) {n : ℕ}
    (p : Fin n → Nat.Primes) (hp : Function.Injective p) :
    AlgebraicIndependent ℚ
      (Fin.cons Real.pi fun i ↦ Real.log (p i : ℕ) : Fin (n + 1) → ℝ) := by
  sorry

theorem strongFourExponentials_of_algIndepLogs (h : AlgIndepLogsConjecture) :
    StrongFourExponentialsConjecture := by
  sorry

end LeanFormalizations.Waldschmidt2023

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# What follows from Schanuel's conjecture

Every theorem here takes `hS : SchanuelConjecture` (`Literature/Schanuel.lean`).  The point
(Trevor, 2026-09-29) is to write down what we believe and see what falls out: a contradiction
with another hypothesis in the repo, a Maze row's `reopenIf` turning out to be implied, or a
surprising corollary.

Three kinds of consequence:

* **Consistency edges**: things already proved unconditionally (Lindemann–Weierstrass,
  Gelfond–Schneider, Nesterenko's `π, e^π`).  Deriving them from Schanuel checks that the
  statement says what we think it says.
* **Open consequences**: `e` and `π` algebraically independent, so `e + π` and `eπ` are
  transcendental; `e, e^e` algebraically independent; logarithms of distinct primes
  algebraically independent (Baker only gives linear independence).
* **Wright towers** (`Maze.lean`, Wright row): for rational non-integer `ω`, every level
  `tower ω n` with `n ≥ 2` is transcendental.  Proof sketch, by induction on `n`: with
  `L = log 2` and `gₖ = tower ω k`, apply Schanuel to `(L, g₁L, …, g_{n-1}L)`.  Linear independence
  of `1, g₁, …, g_{n-1}` comes from the previous step, because `g₁` is algebraic and irrational
  while `L, g₂, …, g_{n-1}` are algebraically independent.  The exponentials are
  `2, g₂, …, gₙ`, so the transcendence degree of `ℚ(L, g₂, …, gₙ)` is at least `n`, which makes
  that set algebraically independent.  This does **not** reach irrationality of the least Wright
  constant: all these levels being transcendental is consistent with every `gₖ` sitting just
  above a prime.

Proof sketches for the other results are the standard ones (Lang, *Introduction to
Transcendental Numbers*; Waldschmidt's surveys): pick `z` so that the exponentials are
algebraic or already in the field, then count.  Split into named leaves freely.  Frozen: every
statement below, and all of `Literature/`.
-/
import LeanFormalizations.Literature.Schanuel
import LeanFormalizations.Literature.GelfondSchneider
import LeanFormalizations.Literature.Lindemann
import LeanFormalizations.NumberTheory.Mills.Wright

namespace LeanFormalizations.Schanuel

open LeanFormalizations.Literature LeanFormalizations.Mills

/-! ## Consistency edges (known unconditionally) -/

/-- Schanuel ⇒ Gelfond–Schneider (real form): take `z = (log a, b log a)`. -/
theorem gelfondSchneider_of_schanuel (hS : SchanuelConjecture) : GelfondSchneider1934 := by
  sorry

/-- Schanuel ⇒ Lindemann–Weierstrass, algebraic-independence form: take `z = u`. -/
theorem lindemannWeierstrassAlgIndep_of_schanuel (hS : SchanuelConjecture) :
    LindemannWeierstrassAlgIndep := by
  sorry

/-- Schanuel ⇒ `π` and `e^π` are algebraically independent: take `z = (iπ, π)`.  Proved
unconditionally by Nesterenko (1996). -/
theorem algebraicIndependent_pi_exp_pi (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ ![Real.pi, Real.exp Real.pi] := by
  sorry

/-! ## Open consequences -/

/-- Schanuel ⇒ `e` and `π` are algebraically independent: take `z = (1, iπ)`. -/
theorem algebraicIndependent_exp_one_pi (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ ![Real.exp 1, Real.pi] := by
  sorry

/-- Schanuel ⇒ `e + π` is transcendental. -/
theorem transcendental_exp_one_add_pi (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.exp 1 + Real.pi) := by
  sorry

/-- Schanuel ⇒ `e · π` is transcendental. -/
theorem transcendental_exp_one_mul_pi (hS : SchanuelConjecture) :
    Transcendental ℚ (Real.exp 1 * Real.pi) := by
  sorry

/-- Schanuel ⇒ `e` and `e^e` are algebraically independent: take `z = (1, e)`. -/
theorem algebraicIndependent_exp_one_exp_exp_one (hS : SchanuelConjecture) :
    AlgebraicIndependent ℚ ![Real.exp 1, Real.exp (Real.exp 1)] := by
  sorry

/-- Schanuel ⇒ logarithms of distinct primes are algebraically independent: take
`z = (log p₁, …, log pₙ)`, which are `ℚ`-linearly independent by unique factorization, with
exponentials `pᵢ ∈ ℚ`. -/
theorem algebraicIndependent_log_primes (hS : SchanuelConjecture) {n : ℕ}
    (p : Fin n → Nat.Primes) (hp : Function.Injective p) :
    AlgebraicIndependent ℚ fun i ↦ Real.log (p i : ℕ) := by
  sorry

/-! ## Wright towers -/

/-- Schanuel ⇒ for rational non-integer `ω`, the numbers `log 2, tower ω 2, …, tower ω n` are
algebraically independent (the induction in the header). -/
theorem algebraicIndependent_wright_tower (hS : SchanuelConjecture) {q : ℚ} (hq : q.den ≠ 1)
    (n : ℕ) :
    AlgebraicIndependent ℚ
      (Fin.cons (Real.log 2) fun i : Fin n ↦ tower (q : ℝ) (i + 2) : Fin (n + 1) → ℝ) := by
  sorry

/-- Schanuel ⇒ every level `n ≥ 2` of the Wright tower at a rational non-integer point is
transcendental.  (Level 2 needs only Gelfond–Schneider: `Maze.WrightLevelTwoTranscendental`.) -/
theorem transcendental_wright_tower (hS : SchanuelConjecture) {q : ℚ} (hq : q.den ≠ 1)
    {n : ℕ} (hn : 2 ≤ n) : Transcendental ℚ (tower (q : ℝ) n) := by
  sorry

end LeanFormalizations.Schanuel

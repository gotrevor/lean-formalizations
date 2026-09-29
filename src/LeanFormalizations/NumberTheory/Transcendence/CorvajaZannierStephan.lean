/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Dubickas's Lemma 6 from Stephan's machine-checked Corvaja–Zannier

R. Stephan formalized all of Corvaja–Zannier 2004 (`rwst/Subspace-Theorems`,
`CorvajaZannier2004/`).  Its Main Theorem and Lemma 4 enter verbatim as
`Literature.Stephan2026CZMain` and `Literature.Stephan2026CZLemma4`.  This file derives the two
phase-9 disclosed statements and `Dubickas2022` from them — wiring, not a CZ proof.  (Phase 13's
`CorvajaZannier.lean` started re-deriving CZ from the Subspace Theorem before this was found; it
is superseded, its disclosed `sorry`s stay.)

## `corvajaZannier_dichotomy_of_czMain`
`Γ = ⟨α⟩ ≤ ℝˣ` (`α > 1` algebraic), `δ = 1`, points `(q, α^(s n))`.  `H(α^(s n)) = H(α)^(s n)`
(`absMulHeight₁` of a power), `H(α) > 1` (`α > 1` is not a root of unity), and
`[ℚ(α^(s n)) : ℚ] ≤ deg α`, so `‖q α^(s n)‖ ≤ e^(−ε s n)` gives the CZ inequality with
`ε' = ε / (2 log H(α))` for large `n` (absorb `q^(−d−ε')` into half the exponent).  Finiteness of
CZ's set, `StrictMono s`, and the hypothesis `hfin` (relate `IsPseudoPisotMul q β` to
`IsPseudoPisot (q β)`; check both definitions) give the claim.  Zero distance: `q α^(s n) ∈ ℤ`
with `> 1` is pseudo-Pisot, so it is covered by `hfin`.

## `corvajaZannier_lemma4_of_czLemma4`
Stephan's form concludes `IsIntegral ℤ α` outright (left disjunct).  Take `α` in `ℂ`, `q_n := q · e_n`
with `e_n = [ℚ(α) : ℚ(αⁿ)] ≤ deg α`, so `log q_n / n → 0`; `Tr_{ℚ(α)/ℚ}(q_n αⁿ) = q · e_n ·
(sum of conjugates of αⁿ) ⋯` — relate `Algebra.trace ℚ ℚ⟮α⟯` to the `aroots` sum of
`minpoly ℚ (αⁿ)` (trace in a tower = degree × trace below; mathlib `Algebra.trace_eq_sum_roots`,
`trace_trace`).  The nonzero integer is `e_n · t`.

## `dubickas2022_of_czMain`
Dubickas's Lemma 6 = Lemma 3 (CZ Main) ∨ Lemma 5 (formalized in `DubickasNoSubspace.lean`), per
`PROBE-DUBICKAS-NOSUBSPACE.md`.  Reassemble phase 9's route with the two derived statements in
place of its two `sorry`s.  `hR` is there in case a rational-power case needs Ridout/Mahler
(`StephanEdges.lean`); drop nothing, it is harmless if unused.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.Literature.Pisot
import LeanFormalizations.NumberTheory.Transcendence.DubickasNoSubspace

namespace LeanFormalizations.Transcendence.Dubickas

open LeanFormalizations.Literature

/-- Phase 9's `corvajaZannier_dichotomy`, from Stephan's CZ Main Theorem. -/
theorem corvajaZannier_dichotomy_of_czMain (hM : Stephan2026CZMain) {α : ℝ}
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ}
    (hq : 0 < q) (s : ℕ → ℕ) (hs : StrictMono s) (hs0 : 0 < s 0)
    (hfin : {n : ℕ | IsPseudoPisotMul q (α ^ s n)}.Finite) :
    ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-(ε * s n)) < |(q : ℝ) * α ^ s n - round ((q : ℝ) * α ^ s n)| := by
  sorry

/-- Phase 9's `corvajaZannier_lemma4`, from Stephan's CZ Lemma 4. -/
theorem corvajaZannier_lemma4_of_czLemma4 (hL : Stephan2026CZLemma4) {α : ℝ}
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {q : ℕ} (hq : 0 < q)
    (hsmall : ∀ w ∈ (minpoly ℚ α).aroots ℂ, ‖w‖ < 1 ∨ ‖w‖ = α)
    {S : Set ℕ} (hS : S.Infinite)
    (htr : ∀ n ∈ S, ∃ t : ℤ, t ≠ 0 ∧
      (q : ℂ) * (((minpoly ℚ (α ^ n)).aroots ℂ).sum) = (t : ℂ)) :
    IsIntegral ℤ α ∨ ∃ (l : ℕ) (r : ℚ), 0 < l ∧ α ^ l = (r : ℝ) := by
  sorry

/-- **Dubickas (2022), Lemma 6, from Stephan's machine-checked Corvaja–Zannier.**  With this,
Dubickas's Theorem 1 (`Dubickas.lean`) rests only on Stephan's theorems. -/
theorem dubickas2022_of_czMain (hM : Stephan2026CZMain) (hL : Stephan2026CZLemma4)
    (hR : Stephan2026Ridout) : Dubickas2022 := by
  sorry

end LeanFormalizations.Transcendence.Dubickas

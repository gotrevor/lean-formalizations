/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional

/-!
# The arithmetic large sieve with an unspecified constant (phase E4c)

`ArithLargeSieveWeak` is `ArithLargeSieve` (`Erdos385Exceptional.lean`) with `C (N + Q²)` in place of
`N + Q²`.  Gallagher's elementary proof gives it (constant `π`, Gallagher 1967, *The large sieve*,
Mathematika 14), while the sharp constant needs Selberg's extremal majorant.  Every application in
this repo tolerates the constant.  `arithLargeSieveWeak_of_sharp` records that it is weaker.
-/

namespace LeanFormalizations.Literature

/-- **The arithmetic large sieve, unspecified constant.** -/
def ArithLargeSieveWeak : Prop :=
  ∃ C : ℝ, ∀ (M N Q : ℕ) (Ω : ℕ → Finset ℕ) (S : Finset ℕ),
    (∀ p, p.Prime → p ≤ Q → Ω p ⊆ Finset.range p ∧ (Ω p).card < p) →
    (∀ n ∈ S, M < n ∧ n ≤ M + N ∧ ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p) →
    (S.card : ℝ) * (∑ q ∈ (Finset.Icc 1 Q).filter Squarefree,
        ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - (Ω p).card)) ≤ C * (N + (Q : ℝ) ^ 2)

theorem arithLargeSieveWeak_of_sharp (h : ArithLargeSieve) : ArithLargeSieveWeak :=
  ⟨1, fun M N Q Ω S hΩ hS => by simpa using h M N Q Ω S hΩ hS⟩

end LeanFormalizations.Literature

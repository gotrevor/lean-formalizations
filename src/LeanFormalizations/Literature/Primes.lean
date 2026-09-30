/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature inputs: prime distribution and Diophantine approximation

Published theorems this repo **uses but does not (yet) prove**.  Each is a `Prop`, never an
`axiom`: a result that depends on one takes it as an explicit hypothesis, so the dependency is
visible in its signature and `#print axioms` stays `[propext, Classical.choice, Quot.sound]`.

Rules for this directory:

* **Faithful or weaker, never stronger.**  Each statement must be implied by the cited result.
  A hypothesis stated too strongly can be false, and a false hypothesis makes every theorem
  that assumes it vacuous.  Where the source's form is awkward in Lean (e.g. `li` with its
  principal value), state a *consequence* of it and say so in the docstring.
* **Cite page and theorem number.**  The docstring is the audit trail.
* Proving one of these is a legitimate side quest; when it lands, the `Prop` stays and gains
  a theorem `foo : Foo` beside it.
-/
import Mathlib

namespace LeanFormalizations.Literature

/-- The number of primes in the real interval `[a, b]` (for `0 ≤ a`). -/
noncomputable def primesIn (a b : ℝ) : ℕ :=
  ((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime).card

/-- **Baker–Harman–Pintz (2001)**, in the form Saito (2024, Theorem 2.1) uses: for `θ = 21/40`
the interval `[x, x + x^θ]` holds `≫ x^θ / log x` primes for all large `x`.

R. C. Baker, G. Harman, J. Pintz, *The difference between consecutive primes. II*,
Proc. London Math. Soc. (3) **83** (2001), 532–562, p. 562. -/
def BakerHarmanPintz2001 : Prop :=
  ∃ d₀ > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X,
    d₀ * x ^ ((21 : ℝ) / 40) / Real.log x ≤ (primesIn x (x + x ^ ((21 : ℝ) / 40)) : ℝ)

/-- **Matomäki (2007)**, in the form Saito (2024, Theorem 3.7) quotes from Matomäki (2010,
Lemma 9): there are `0 < d₁ < 1` and `D > 0` such that for all large `x` and every
`γ ∈ [1/2, 1]`, `[x, 2x]` contains at most `D x^(2/3 − γ)` pairwise disjoint intervals
`[n, n + n^γ]` holding at most `d₁ n^γ / log n` primes.

K. Matomäki, *Large differences between consecutive primes*, Q. J. Math. **58** (2007),
489–518; K. Matomäki, *Prime-representing functions*, Acta Math. Hungar. **128** (2010),
307–314, Lemma 9. -/
def Matomaki2007 : Prop :=
  ∃ d₁ D : ℝ, 0 < d₁ ∧ d₁ < 1 ∧ 0 < D ∧ ∃ X : ℝ, ∀ x ≥ X, ∀ γ ∈ Set.Icc (1 / 2 : ℝ) 1,
    ∀ S : Finset ℝ,
      (∀ n ∈ S, x ≤ n ∧ n + n ^ γ ≤ 2 * x) →
      (S : Set ℝ).PairwiseDisjoint (fun n => Set.Icc n (n + n ^ γ)) →
      (∀ n ∈ S, (primesIn n (n + n ^ γ) : ℝ) ≤ d₁ * n ^ γ / Real.log n) →
      (S.card : ℝ) ≤ D * x ^ ((2 : ℝ) / 3 - γ)

/-- **Mahler (1957)**: for a rational `α > 1` that is not an integer and any `ε > 0`, the
distance from `αⁿ` to the nearest integer eventually exceeds `e^(−εn)`.  (Ineffective; Mahler
derives it from Ridout's `p`-adic Roth theorem.)

K. Mahler, *On the fractional parts of the powers of a rational number. II*, Mathematika **4**
(1957), 122–124.  Quoted as Saito (2024), Theorem 2.5. -/
def Mahler1957 : Prop :=
  ∀ α : ℚ, 1 < α → α.den ≠ 1 → ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
    Real.exp (-(ε * n)) < |(α : ℝ) ^ n - round ((α : ℝ) ^ n)|

/-- **Schoenfeld (1976)**, weakened to what the Mills digits need: under RH,
`|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`.  Stated with `li(x) = li(2) + ∫₂ˣ dt/log t`
and the constant `li(2)` existentially quantified, which Schoenfeld's form implies; only
differences `π(b) − π(a)` are ever used.

L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp.
**30** (1976), 337–360, Corollary 1.  Quoted as Caldwell–Cheng (2005), Lemma 4. -/
def Schoenfeld1976 : Prop :=
  RiemannHypothesis → ∃ C : ℝ, ∀ x ≥ (2657 : ℝ),
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - (C + ∫ t in (2 : ℝ)..x, 1 / Real.log t)| <
      Real.sqrt x * Real.log x / (8 * Real.pi)

/-- **Dudek (2016)**: there is a prime between `n³` and `(n+1)³` for every `n ≥ exp(exp(33.3))`.

A. W. Dudek, *An explicit result for primes between cubes*, arXiv:1401.4233.  The arXiv v1
abstract states the threshold `exp(exp(33.217))`; `exp(exp(33.3))` is the value commonly
cited for the published version (not re-checked against it here).  Either way `33.3` is the
larger threshold, hence the weaker statement, so it is the one used. -/
def Dudek2016 : Prop :=
  ∀ n : ℕ, Real.exp (Real.exp 33.3) ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3

end LeanFormalizations.Literature

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Practical.Basic

/-!
# Literature inputs: practical numbers

Cited, faithful-or-weaker hypothesis `Prop`s (rules: `Literature/Primes.lean` header).

The asymptotic `P(x) ~ c x / log x` comes from Weingartner's treatment of `B_θ` as integers whose
prime factors grow under a recursive constraint, via a Buchstab-type integral equation (Dickman /
Buchstab-function territory).  The repo already owns Buchstab's delay system
(`Erdos385/LinearSieve/DelaySolution.lean`, `RoughOmega.lean`, `RoughLimit.lean`); that is the
machinery a future discharge or an *effective* version would reuse.
-/

namespace LeanFormalizations.Literature

open Filter Topology LeanFormalizations.Practical

/-- `P(x)`, the number of practical numbers in `[1, x]`. -/
noncomputable def practicalCount (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter IsPractical).card

/-- **Weingartner (2015), Theorem 1**: `P(x) = (c x / log x)(1 + O(log log x / log x))` for some
`c > 0`; stated here in the weaker form `P(x) log x / x → c`.
A. Weingartner, *Practical numbers and the distribution of divisors*, arXiv:1405.2585, Thm 1. -/
def Weingartner2015 : Prop :=
  ∃ c > (0 : ℝ), Tendsto (fun x : ℝ => (practicalCount x : ℝ) * Real.log x / x) atTop (𝓝 c)

/-- **Weingartner (2019), Theorem 1**: the constant is `1.336073 < c < 1.336077`.
A. Weingartner, *The constant factor in the asymptotic for practical numbers*,
arXiv:1906.07819, Thm 1 (with Weingartner 2015 for the limit's existence). -/
def Weingartner2019 : Prop :=
  ∃ c : ℝ, 1.336073 < c ∧ c < 1.336077 ∧
    Tendsto (fun x : ℝ => (practicalCount x : ℝ) * Real.log x / x) atTop (𝓝 c)

/-- **Pomerance–Weingartner (2021), Corollary 2**: every sufficiently large odd integer is a prime
plus a practical number.  The threshold is not computed (the proof uses Bombieri–Vinogradov;
§1: "it may be difficult by our methods to get a numerical bound x₀").
C. Pomerance, A. Weingartner, *On primes and practical numbers*, arXiv:2007.11062, Cor. 2. -/
def PomeranceWeingartner2021 : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, Odd n → ∃ p q : ℕ, p.Prime ∧ IsPractical q ∧ n = p + q

/-- **Pomerance–Weingartner (2021), §5.1** (a reported computation): `PrimePlusPracticalOdd`
holds for all odd `1 < n < 2^71`, via their Lemma 9 (`primePlusPractical_window`) with
`M(2^23) = 997427777` and `M(2^35) = 9968601716713`, after a direct search to `10^9`.
Same source, §5.1. -/
def PomeranceWeingartner2021Computation : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → n < 2 ^ 71 → ∃ p q : ℕ, p.Prime ∧ IsPractical q ∧ n = p + q

/-- **Melfi (1996), Theorem 1**: every even positive integer is a sum of two practical numbers
(the even case of Margenstern's Conjecture 7).  As quoted in Pomerance–Weingartner (2021) §1;
G. Melfi, *On two conjectures about practical numbers*, J. Number Theory 56 (1996), 205–210. -/
def Melfi1996 : Prop :=
  ∀ n : ℕ, Even n → 0 < n → ∃ a b : ℕ, IsPractical a ∧ IsPractical b ∧ n = a + b

end LeanFormalizations.Literature

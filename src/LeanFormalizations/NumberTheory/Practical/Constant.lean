/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Practical

/-!
# The practical-number constants on the irrationality spectrum (exploration, 2026-10-05)

**Weingartner's `c = 1.33607…`** (`P(x) ~ c x / log x`).  It has an explicit series
(Weingartner, Math. Comp. 88 (2019), Thm 1; eq. (2) of arXiv:1906.07819):
`c = (1 − e^{−γ})⁻¹ Σ_{n practical} (1/n) (Σ_{p ≤ σ(n)+1} log p/(p − 1) − log n)
∏_{p ≤ σ(n)+1} (1 − 1/p)`.
It is known only to about 6 digits (`1.336073 < c < 1.336077`), and nothing is known about its
irrationality.  That is the same tier as Mertens', Artin's and Brun's constants: an arithmetic
sum over a sieve-defined set, with `e^{−γ}` in front.  No mechanism is known even for
irrationality.  `PracticalConstantIrrational` records the open node.  Related: `K = c e^{−γ}` is
the leading constant in Hughes (arXiv:2609.25446)'s lower bound for Erdős #859's densities `d_t`.

**The binary practical constant** `β = Σ_{n practical} 2^{−n}` sits where the prime constant
`Σ_p 2^{−p}` does: irrational (`practicalBinary_irrational`, elementary), not normal in base 2
(its binary digits have density 0), transcendence open (`PracticalBinaryTranscendental`, as for
the prime constant).
-/

namespace LeanFormalizations.Practical

open Real Filter Topology

/-- The `n`-th term of Weingartner's series for `c` (zero off the practical numbers). -/
noncomputable def weingartnerTerm (n : ℕ) : ℝ :=
  if IsPractical n then
    (1 / (n : ℝ)) *
      ((∑ p ∈ (Finset.range (sigma1 n + 2)).filter Nat.Prime, log p / ((p : ℝ) - 1)) - log n) *
      ∏ p ∈ (Finset.range (sigma1 n + 2)).filter Nat.Prime, (1 - 1 / (p : ℝ))
  else 0

/-- Weingartner's series value. -/
noncomputable def practicalConstant : ℝ :=
  (1 - exp (-eulerMascheroniConstant))⁻¹ * ∑' n, weingartnerTerm n

end LeanFormalizations.Practical

namespace LeanFormalizations.Literature

open Real Filter Topology LeanFormalizations.Practical

/-- **Weingartner (2019), Theorem 1** (A. Weingartner, *On the constant factor in several related
asymptotic estimates*, Math. Comp. 88 (2019), 1883–1902, arXiv:1705.06349; as quoted in
arXiv:1906.07819 eq. (2)): the series converges and its value is the constant in
`P(x) ~ c x / log x`.  Summability is included so a junk `tsum` cannot make this vacuous; the
terms are `O(1/(n log n))` on a set of counting function `≍ x / log x`. -/
def Weingartner2019Series : Prop :=
  Summable weingartnerTerm ∧
    Tendsto (fun x : ℝ => (practicalCount x : ℝ) * log x / x) atTop
      (𝓝 practicalConstant)

end LeanFormalizations.Literature

namespace LeanFormalizations.Practical

open Real

/-- **Open:** `c` is irrational.  No mechanism known. -/
def PracticalConstantIrrational : Prop := Irrational practicalConstant

/-- The binary practical constant `Σ_{n practical} 2^{−n}`. -/
noncomputable def practicalBinary : ℝ := ∑' n, if IsPractical n then (1 / 2 : ℝ) ^ n else 0

/-- **`β` is irrational.**  Route: rational ⇒ its binary digits are eventually periodic with some
period `T` ⇒ (practical numbers are infinite: `2^k`) some class `r mod T` is eventually all
practical; with `g = gcd(r, T)`, Dirichlet gives `n = g p` in that class with `p` prime,
`p > σ(g) + 1`, and `isPractical_iff_inB` says `g p` is not practical.  Believed 99%. -/
theorem practicalBinary_irrational : Irrational practicalBinary := by
  sorry

/-- **Open:** `β` is transcendental (as for the prime constant `Σ_p 2^{−p}`). -/
def PracticalBinaryTranscendental : Prop := Transcendental ℚ practicalBinary

end LeanFormalizations.Practical

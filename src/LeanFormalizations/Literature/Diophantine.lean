/-
# Literature inputs: rational approximation to algebraic numbers

Statements only (see `Literature/Primes.lean` for the rules: faithful or weaker, cited, never an
`axiom`).  These are the bedrock under a large part of irrationality/transcendence theory; this
repo does not prove them.

* `Roth1955` — Thue–Siegel–Roth, exactly as in the Encyclopedia of Mathematics entry.
* `Ridout1958SUnitDen` — a **special case** of Ridout's `p`-adic Roth theorem: when the
  denominators are built from a fixed finite set of primes, the exponent `2` drops to `1`.
  Ridout's full theorem restricts numerator *and* denominator (an `S`-unit part times a
  controlled remaining part) and is what Mahler (1957) derives `Mahler1957` from.  It is not
  stated here yet: its exact hypotheses need checking against Ridout's paper, and a
  misremembered hypothesis could make the statement false.

Open wiring edge (unsized): full Ridout ⇒ `Mahler1957` (Mahler's derivation is short).
-/
import Mathlib

namespace LeanFormalizations.Literature

/-- **Thue–Siegel–Roth (Roth 1955).**  For an irrational algebraic real `α` and `δ > 0`, only
finitely many rationals `p/q` (in lowest terms, `q > 0`) satisfy `|α − p/q| < 1/q^(2+δ)`.

K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika **2** (1955), 1–20.
Statement as in Encyclopedia of Mathematics, "Thue–Siegel–Roth theorem". -/
def Roth1955 : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → Irrational α → ∀ δ > (0 : ℝ),
    {r : ℚ | |α - r| < 1 / (r.den : ℝ) ^ (2 + δ)}.Finite

/-- **Ridout (1958), special case: `S`-unit denominators.**  For an irrational algebraic real
`α`, a finite set `S` of primes and `δ > 0`, only finitely many rationals whose (lowest-terms)
denominator has all prime factors in `S` satisfy `|α − p/q| < 1/q^(1+δ)`.

This is the case "numerator unrestricted, denominator an `S`-unit" (`μ = 1`, `ν = 0` in
Ridout's two-sided form), so it is implied by the full theorem.

D. Ridout, *The `p`-adic generalization of the Thue–Siegel–Roth theorem*, Mathematika **5**
(1958), 40–48. -/
def Ridout1958SUnitDen : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → Irrational α → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    ∀ δ > (0 : ℝ),
      {r : ℚ | (∀ p ∈ r.den.primeFactors, p ∈ S) ∧ |α - r| < 1 / (r.den : ℝ) ^ (1 + δ)}.Finite

end LeanFormalizations.Literature

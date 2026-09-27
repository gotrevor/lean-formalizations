/-
# Literature inputs: rational approximation to algebraic numbers

Statements only (see `Literature/Primes.lean` for the rules: faithful or weaker, cited, never an
`axiom`).  These are the bedrock under a large part of irrationality/transcendence theory; this
repo does not prove them.

* `Roth1955` — Thue–Siegel–Roth, exactly as in the Encyclopedia of Mathematics entry.
* `Ridout1958` — Ridout's Theorem 1, the `p`-adic Roth theorem, stated from the paper.
* `Ridout1958SUnitDen` — the classical corollary (denominators built from a fixed finite set of
  primes, exponent `1 + δ`).  Kept as its own statement; `Ridout1958 → Ridout1958SUnitDen` is an
  open wiring edge.

Open wiring edges: `Ridout1958 → Mahler1957` (Mahler 1957 derives it from Ridout), `Ridout1958 → Ridout1958SUnitDen`, `Ridout1958 → Roth1955` (take `t = 0`).
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

/-- Lets `ℚ_[p]` be formed for a bundled prime `p : Nat.Primes`. -/
instance factPrimeOfPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **Ridout (1958), Theorem 1 — the `p`-adic Thue–Siegel–Roth theorem**, as stated in the
paper.  Let `f ∈ ℤ[X]` have degree `≥ 2`, a real root `ξ`, and for each of the distinct primes
`p₁, …, p_t` a `p_r`-adic root `ξ_r`.  For `κ > 2` only finitely many coprime `(h, q)` with
`q > 0` satisfy
`min(1, |ξ − h/q|) · ∏_r min(1, |q ξ_r − h|_{p_r}) ≤ max(|h|, |q|)^(−κ)`.
(Ridout notes the `p`-adic factors are `|q ξ_r − h|`, not `|ξ_r − h/q|`.)

D. Ridout, *The `p`-adic generalization of the Thue–Siegel–Roth theorem*, Mathematika **5**
(1958), 40–48, Theorem 1 (p. 40).  Local-only full text (gitignored):
`papers/ridout-1958-p-adic-roth.{pdf,txt}`. -/
def Ridout1958 : Prop :=
  ∀ (f : Polynomial ℤ), 2 ≤ f.natDegree →
  ∀ ξ : ℝ, Polynomial.aeval ξ f = 0 →
  ∀ (t : ℕ) (P : Fin t → Nat.Primes), Function.Injective P →
  ∀ ξp : (r : Fin t) → ℚ_[(P r : ℕ)], (∀ r, Polynomial.aeval (ξp r) f = 0) →
  ∀ κ > (2 : ℝ),
    {x : ℤ × ℤ | 0 < x.2 ∧ IsCoprime x.1 x.2 ∧
      min 1 |ξ - (x.1 : ℝ) / x.2| *
          ∏ r, min 1 ‖((x.2 : ℚ_[(P r : ℕ)]) * ξp r - x.1)‖ ≤
        (max |x.1| |x.2| : ℝ) ^ (-κ)}.Finite

end LeanFormalizations.Literature

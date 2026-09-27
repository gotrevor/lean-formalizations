/-
# Literature inputs: rational approximation to algebraic numbers

Statements only (see `Literature/Primes.lean` for the rules: faithful or weaker, cited, never an
`axiom`).  These are the bedrock under a large part of irrationality/transcendence theory; this
repo does not prove them.

* `Roth1955` — Thue–Siegel–Roth, exactly as in the Encyclopedia of Mathematics entry.
* `Ridout1958` — Ridout's Theorem 1, the `p`-adic Roth theorem, stated from the paper.
* `Ridout1957SUnitDen` — the classical corollary of Ridout's *1957* paper (denominators built
  from a fixed finite set of primes, exponent `1 + δ`).  The full 1957 two-sided form is not
  stated as its own `Prop`; `Ridout1957 → Ridout1957SUnitDen` is an edge.
* `Ridout1957` — Ridout's 1957 Theorem, stated from the paper.  Mahler derives `Mahler1957`
  from it (Mahler 1957, §3).

Wiring edges (proved in `NumberTheory/Diophantine/Edges.lean`): `Ridout1957 → Mahler1957`,
`Ridout1957 → Ridout1957SUnitDen`, `Ridout1958 → Roth1955`.
⚠️ `Mahler1957` does NOT come from `Ridout1958`: Mahler (1957, §3) derives it from Ridout's
*other* paper, *Rational approximations to algebraic numbers*, Mathematika **4** (1957),
125–131 (doi:10.1112/s0025579300001182) — the two-sided `S`-unit form with exponent
`γ > α + β` (Mahler's Theorem 3).  The 1958 theorem only reaches exponent `> 2`, too weak for
Mahler's application.
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

/-- **Ridout (1957), special case: `S`-unit denominators.**  For an irrational algebraic real
`α`, a finite set `S` of primes and `δ > 0`, only finitely many rationals whose (lowest-terms)
denominator has all prime factors in `S` satisfy `|α − p/q| < 1/q^(1+δ)`.

The case "numerator unrestricted, denominator an `S`-unit" (`α = 1`, `β = 0`, `q* = 1` in the
two-sided form Mahler (1957, Theorem 3) quotes), so it is implied by Ridout's theorem.

D. Ridout, *Rational approximations to algebraic numbers*, Mathematika **4** (1957), 125–131. -/
def Ridout1957SUnitDen : Prop :=
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

/-- **Ridout (1957), Theorem** — Roth with `S`-unit restrictions, the exponent `2` lowered to
`μ + ν`.  Let `α ≠ 0` be algebraic, `P₁…P_s, Q₁…Q_t` distinct primes, `0 ≤ μ, ν ≤ 1`, `c > 0`.
Restrict to `p = p* · (product of powers of the Pᵢ)`, `q = q* · (product of powers of the Qⱼ)`
with `0 < |p*| ≤ c p^μ`, `0 < q* ≤ c q^ν`.  If `κ > μ + ν`, then `0 < |α − p/q| < q^(−κ)` has
only finitely many solutions `(p, q)`.

Stated for `p, q > 0` (Ridout writes `p^μ`, so `p > 0` is implicit); restricting the solution
set only weakens the statement.  "Distinct primes" is `Disjoint P Q` plus primality.

D. Ridout, *Rational approximations to algebraic numbers*, Mathematika **4** (1957), 125–131,
the Theorem on p. 125.  Local-only full text (gitignored):
`papers/ridout-1957-rational-approximations.{pdf,txt}`. -/
def Ridout1957 : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → α ≠ 0 →
  ∀ P Q : Finset ℕ, (∀ r ∈ P, r.Prime) → (∀ r ∈ Q, r.Prime) → Disjoint P Q →
  ∀ μ ν c κ : ℝ, 0 ≤ μ → μ ≤ 1 → 0 ≤ ν → ν ≤ 1 → 0 < c → μ + ν < κ →
    {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧
      (∃ ps a : ℕ, x.1 = ps * a ∧ (∀ r ∈ a.primeFactors, r ∈ P) ∧
        0 < ps ∧ (ps : ℝ) ≤ c * (x.1 : ℝ) ^ μ) ∧
      (∃ qs b : ℕ, x.2 = qs * b ∧ (∀ r ∈ b.primeFactors, r ∈ Q) ∧
        0 < qs ∧ (qs : ℝ) ≤ c * (x.2 : ℝ) ^ ν) ∧
      0 < |α - (x.1 : ℝ) / x.2| ∧ |α - (x.1 : ℝ) / x.2| < 1 / (x.2 : ℝ) ^ κ}.Finite

end LeanFormalizations.Literature

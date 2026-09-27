/-
# Literature inputs: powers of algebraic numbers, Pisot numbers

Statements only (rules in `Literature/Primes.lean`: faithful or weaker, cited, never an `axiom`).
These are the two inputs Saito (2024) adds, beyond the prime-distribution ones, to get
*transcendence* of `ξ_c` (`c ≥ 4`) and the Pisot alternative for `ξ₃`.

Both are quoted as Saito states them (Theorem 2.6, Lemma 2.7); the primary source,
A. Dubickas, *Transcendency of some constants related to integer sequences of polynomial
iterations*, Ramanujan J. **57** (2022), 569–581 (Lemmas 6 and 8), is not on arXiv and has not
been checked here.  Dubickas's Lemma 6 rests on Corvaja–Zannier, *On the rational
approximations to the powers of an algebraic number*, Acta Math. **193** (2004), 175–191
(`p`-adic Schmidt subspace theorem).
-/
import Mathlib

namespace LeanFormalizations.Literature

/-- A **Pisot number**: a real algebraic integer `β > 1` all of whose other conjugates over `ℚ`
lie in the open unit disc.  (Saito 2024, §1.)  Conjugates are the complex roots of the minimal
polynomial; they are distinct (characteristic zero), so `erase` removes exactly `β`. -/
def IsPisot (β : ℝ) : Prop :=
  1 < β ∧ IsIntegral ℤ β ∧ ∀ z ∈ ((minpoly ℚ β).aroots ℂ).erase (β : ℂ), ‖z‖ < 1

/-- **Dubickas (2022, Lemma 6), from Corvaja–Zannier (2004)** — Saito (2024), Theorem 2.6.
Let `α > 1` be algebraic, `q` a positive integer, `0 < s₁ < s₂ < ⋯` integers.  Either some
`α^(s_m)` is a Pisot number, or for each `ε > 0` there is `k₀` with
`‖q α^(s_k)‖ > e^(−ε s_k)` for all `k ≥ k₀` (`‖·‖` = distance to the nearest integer). -/
def Dubickas2022 : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → 1 < α → ∀ q : ℕ, 0 < q → ∀ s : ℕ → ℕ, StrictMono s → 0 < s 0 →
    (∃ m, IsPisot (α ^ s m)) ∨
    ∀ ε > (0 : ℝ), ∃ k₀ : ℕ, ∀ k ≥ k₀,
      Real.exp (-(ε * s k)) < |(q : ℝ) * α ^ s k - round ((q : ℝ) * α ^ s k)|

/-- **Dubickas (2022, Lemma 8)** — Saito (2024), Lemma 2.7.  Let `β` be a Pisot number of degree
`ℓ ≥ 2` with conjugates `β₁ = β > 1 > |β₂| ≥ ⋯ ≥ |β_ℓ|`.  There is `λ > 0` depending only on `β`
with `|β₂ⁿ + ⋯ + β_ℓⁿ| ≥ |β₂|ⁿ n^(−λ)` for all large `n`.  Here `|β₂|` is the largest modulus
among the conjugates other than `β`. -/
def Dubickas2022PisotGap : Prop :=
  ∀ β : ℝ, IsPisot β → 2 ≤ (minpoly ℚ β).natDegree →
    ∃ lam > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((((minpoly ℚ β).aroots ℂ).erase (β : ℂ)).map (‖·‖)).fold max 0 ^ n * (n : ℝ) ^ (-lam) ≤
        ‖((((minpoly ℚ β).aroots ℂ).erase (β : ℂ)).map (· ^ n)).sum‖

end LeanFormalizations.Literature

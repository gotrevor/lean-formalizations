/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Literature inputs for Erdős #385 / #430

Statements only, never `axiom`s.  Each is faithful-or-weaker to the cited source; the
docstring says which, and how the transcription was checked.  Context:
`ROADMAP-ERDOS-385.md`, `LIT-ERDOS-385.md`, `DOOR-*-ERDOS-385.md`.

* `BBR2015Thm23TwoFactor`: Bank, Bary-Soroker, Rosenzweig, arXiv:1302.0625, Thm 2.3, specialised
  to factorization types with two distinct parts.
* `Gorodetsky2018Thm11`: Gorodetsky, arXiv:1810.00483, Thm 1.1 (fixed `q`).
* `FGKMT2018Eq12`: Ford, Green, Konyagin, Maynard, Tao, *Long gaps between primes*,
  arXiv:1412.5029, eq. (1.2).
* `Granville2022Cor1`: Granville, *Sieving intervals and Siegel zeroes*, arXiv:2010.01211,
  Cor. 1, at `v = 2` only.
* `BrunUniformGap`: a uniform Brun-type upper bound for prime pairs (Halberstam–Richert,
  *Sieve Methods*, Thm 3.11, up to the constant).
-/

open Polynomial Real

namespace LeanFormalizations.Literature

/-! ## Function fields -/

/-- The short interval `f + P_{≤m}`, parametrised by the `m + 1` low coefficients of the shift. -/
noncomputable def shortIntervalPoly {K : Type*} [Field K] (f : K[X]) (m : ℕ)
    (c : Fin (m + 1) → K) : K[X] :=
  f + ∑ i : Fin (m + 1), C (c i) * X ^ (i : ℕ)

/-- `g` has factorization type `(a, b)`: a product of two monic irreducibles of degrees `a`, `b`. -/
def IsTwoPrimeType {K : Type*} [Field K] (a b : ℕ) (g : K[X]) : Prop :=
  ∃ A B : K[X], A.Monic ∧ B.Monic ∧ Irreducible A ∧ Irreducible B ∧
    A.natDegree = a ∧ B.natDegree = b ∧ g = A * B

/-- **Bank–Bary-Soroker–Rosenzweig (2015), Thm 2.3, two-part types.**  For a partition `λ` of `k`,
every `q`, every monic `f` of degree `k` and `3 ≤ m < k`,
`|π_q(f + P_{≤m}; λ) − P(λ) q^{m+1}| ≤ c(k) q^{m+1/2}`, where `P(λ)` is the proportion of
permutations of `S_k` with cycle type `λ`.  Here `λ = (a, b)` with `a < b`, so `P(λ) = 1/(ab)`.

Weaker than the source: only two-part types with distinct parts, and the constant may depend on
`m, a, b` as well as `k`.  Transcribed from the quotation in `LIT-ERDOS-385.md` §1, which was
read from the paper's full text; the theorem itself was not re-opened for this file (90%). -/
def BBR2015Thm23TwoFactor : Prop :=
  ∀ k m a b : ℕ, 3 ≤ m → m < k → a + b = k → 1 ≤ a → a < b →
    ∃ C : ℝ, ∀ (K : Type) [Field K] [Fintype K], ∀ f : K[X], f.Monic → f.natDegree = k →
      |(Nat.card {c : Fin (m + 1) → K // IsTwoPrimeType a b (shortIntervalPoly f m c)} : ℝ)
          - (Fintype.card K : ℝ) ^ (m + 1) / (a * b)|
        ≤ C * (Fintype.card K : ℝ) ^ ((m : ℝ) + 1 / 2)

/-- The factorization type of `g`: the multiset of degrees of its monic irreducible factors. -/
noncomputable def factorType {K : Type*} [Field K] [DecidableEq K] (g : K[X]) : Multiset ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors g).map natDegree

/-- **Gorodetsky (2018), Thm 1.1 (fixed `q`, large degree).**  For any factorization function
`α`, `|⟨α⟩_{I(f₀,h)} − ⟨α⟩_{M_n}| ≤ max|α| · q^{n/2 − h − 1} · e^{O_q(n log log n / log n)}`, with
`I(f₀, h) = {f : deg(f − f₀) ≤ h}`.

Weaker than the source: `α` is bounded by `1`, the bound is only claimed for `n ≥ n₀`, and
`h < n`.  Transcribed from the quotation in `LIT-ERDOS-385.md` §1 (85%: the exact shape of the
`O_q` term was not re-read).  Nontrivial only when `h > n/2`; #385 needs `h < n/2`, which is why the
fixed-`q` route is closed (`Maze.lean`). -/
def Gorodetsky2018Thm11 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], ∃ B : ℝ, ∃ n₀ : ℕ,
    ∀ n h : ℕ, n₀ ≤ n → h < n → ∀ f₀ : K[X], f₀.Monic → f₀.natDegree = n →
      ∀ α : Multiset ℕ → ℝ, (∀ t, |α t| ≤ 1) →
        |(∑ c : Fin (h + 1) → K, α (factorType (shortIntervalPoly f₀ h c)))
              / (Fintype.card K : ℝ) ^ (h + 1)
            - (∑ c : Fin n → K, α (factorType (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ))))
              / (Fintype.card K : ℝ) ^ n|
          ≤ (Fintype.card K : ℝ) ^ ((n : ℝ) / 2 - h - 1)
            * Real.exp (B * n * Real.log (Real.log n) / Real.log n)

/-! ## Sieve extremals -/

/-- **Ford–Green–Konyagin–Maynard–Tao (2018), eq. (1.2).**  `Y(x) ≫ x log x log₃ x / log₂ x`,
where `Y(x)` is the largest `y` such that one residue class `a_p mod p` for each prime `p ≤ x`
covers `{1, …, ⌊y⌋}` (their Definition 1).  Faithful; checked against the arXiv:1412.5029 text,
2026-10-01. -/
def FGKMT2018Eq12 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℕ, x₀ ≤ x → ∃ a : ℕ → ℤ, ∀ t : ℕ, 1 ≤ t →
    (t : ℝ) ≤ c * x * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) →
      ∃ p, p.Prime ∧ p ≤ x ∧ (t : ℤ) ≡ a p [ZMOD p]

/-- Infinitely many Siegel zeroes, in the strong form: for every `ε > 0` there are arbitrarily
large moduli `N` with a primitive quadratic character `χ` whose `L`-function vanishes at some
`β ∈ (1 − ε / log N, 1)`.  ⚠️ Granville's exact hypothesis was not re-read; this is the standard
form (60% that it matches his). -/
def SiegelZerosInfinitelyOften : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∃ (N : ℕ) (_ : NeZero N), N₀ ≤ N ∧ ∃ χ : DirichletCharacter ℂ N,
    χ.IsPrimitive ∧ χ ≠ 1 ∧ χ ^ 2 = 1 ∧
      ∃ β : ℝ, 1 - ε / Real.log N < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ β = 0

/-- Tao's one-scale enemy: arbitrarily long intervals of length `y` in which the classes `0 mod p`,
`p ≤ √y`, leave `o(y / log y)` survivors. -/
def OneScaleSieveEnemy : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Y₀ : ℕ, ∃ x y : ℕ, Y₀ ≤ y ∧
    ({n : ℕ | x < n ∧ n ≤ x + y ∧ ∀ p, p.Prime → p * p ≤ y → ¬ p ∣ n}.ncard : ℝ)
      ≤ ε * y / Real.log y

/-- **Granville (2022), Cor. 1, at `v = 2`.**  Assuming infinitely many Siegel zeroes, the linear
sieve lower bound is sharp for intervals; at `v = 2` (`z = √y`) the lower sieve function `f(2)`
vanishes, so some intervals keep only `o(G(z) y) = o(y / log y)` survivors.

Weaker than the source: `v = 2` only, and nothing is claimed about where the interval sits. -/
def Granville2022Cor1 : Prop :=
  SiegelZerosInfinitelyOften → OneScaleSieveEnemy

/-- **Uniform Brun bound for prime pairs.**  `#{n ≤ X : n, n + h prime} ≪ (h / φ(h)) X / log² X`,
uniformly in `h ≥ 1`.  Halberstam–Richert, *Sieve Methods*, Thm 3.11 has the singular factor
`∏_{2<p∣h} (p−1)/(p−2)`, which is within a constant of `h / φ(h)`.  ⚠️ Citation from memory, not
re-opened (70%). -/
def BrunUniformGap : Prop :=
  ∃ C : ℝ, ∀ X h : ℕ, 3 ≤ X → 1 ≤ h →
    ({n : ℕ | n ≤ X ∧ n.Prime ∧ (n + h).Prime}.ncard : ℝ)
      ≤ C * ((h : ℝ) / (Nat.totient h : ℝ)) * X / Real.log X ^ 2

end LeanFormalizations.Literature

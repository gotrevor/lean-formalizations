/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Structural rank, and Waldschmidt's lower bound (survey §5)

Waldschmidt 2023, §5, Definition 1 (Roy 1995, p. 54; Waldschmidt 2000, Lemma 12.8), checked
against the rendered page.  Let `M` be a complex matrix, and write `M = M₁e₁ + ⋯ + M_t e_t`, where
`e₁, …, e_t` is a `ℚ`-basis of the `ℚ`-span of the entries and each `Mₖ` has rational entries.
The **structural rank** `r_str,ℚ(M)` is the rank of `M₁X₁ + ⋯ + M_t X_t` over `ℚ(X₁, …, X_t)`.  It
does not depend on the basis.  We only take `K = ℚ`.

* `rk(M) ≤ r_str(M)` is "plain".
* **Theorem (Waldschmidt 1981)**: for a matrix of logarithms of algebraic numbers,
  `rk(M) ≥ ½ r_str(M)`.  This is inequality (2) of the survey, entered as `Waldschmidt1981`.
* **Roy (1995)**: Conjecture 1 is equivalent to `rk(M) = r_str(M)` for all such `M`.  The
  forward direction is proved in `NumberTheory/Transcendence/StructuralRank.lean`.
-/
import Mathlib

namespace LeanFormalizations.Literature

open Matrix

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]

/-- `r` is the structural rank of `M` over `ℚ`: some `ℚ`-linearly independent `e : Fin t → ℂ`
and rational matrices `c k` give `M = ∑ₖ (c k) eₖ`, and the generic matrix `∑ₖ (c k) Xₖ` has rank
`r` over `ℚ(X₁, …, X_t)`.  (The rank is basis-independent, so `∃` is faithful.) -/
def IsStructRank (M : Matrix m n ℂ) (r : ℕ) : Prop :=
  ∃ (t : ℕ) (e : Fin t → ℂ) (c : Fin t → Matrix m n ℚ), LinearIndependent ℚ e ∧
    M = ∑ k, (c k).map (fun q : ℚ ↦ (q : ℂ) * e k) ∧
    (∑ k, (c k).map (fun q : ℚ ↦
      algebraMap (MvPolynomial (Fin t) ℚ) (FractionRing (MvPolynomial (Fin t) ℚ))
        (MvPolynomial.C q * MvPolynomial.X k))).rank = r

/-- The entries of `M` are logarithms of algebraic numbers. -/
def IsLogMatrix (M : Matrix m n ℂ) : Prop := ∀ i j, IsAlgebraic ℚ (Complex.exp (M i j))

/-- **Waldschmidt (1981)**, survey inequality (2): a matrix of logarithms of algebraic numbers
has rank at least half its structural rank.  M. Waldschmidt, *Transcendance et exponentielles en
plusieurs variables*, Invent. Math. **63** (1981). -/
def Waldschmidt1981 : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (r : ℕ),
    IsLogMatrix M → IsStructRank M r → r ≤ 2 * M.rank

end LeanFormalizations.Literature

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature and conjecture inputs: sharp six exponentials, and periods / zeta values

## Sharp six exponentials: the correct form of the survey's "shifted" statement

Waldschmidt 2023 (p. 8, rendered page checked) prints the shifted six exponentials statement over
`ℚ` with the conclusion "one at least of the six numbers `e^{xᵢyⱼ−βᵢⱼ}` is transcendental".  **That is
false as printed**: `Waldschmidt2023.not_sixExponentialsShifted` refutes it in the kernel with
`x = (1, √2)`, `y = (1, √2, i)`, `βᵢⱼ = xᵢyⱼ`, so all six exponentials equal `e⁰ = 1`.  This is a
**misprint in the survey**, not a dropped overbar.  The rendered page really says `ℚ`.  The
correct theorem is the *sharp* six exponentials theorem, with the exceptional case restored:
M. Waldschmidt, NCTS lectures 2003 (`articles/pdf/NCTS-10-2003.pdf`, slide 23), and Waldschmidt
2005, Theorem 1.4.

## Periods

Grothendieck's period conjecture is not stated anywhere we know of in Lean.  A faithful statement
needs motives.  We state its standard concrete consequences instead:
* `ZetaValuesAlgIndepConjecture`: `π, ζ(3), ζ(5), ζ(7), …` are algebraically independent.  This
  is a consequence of the period conjecture for mixed Tate motives over `ℤ` (F. Brown, *Mixed Tate
  motives over ℤ*, Ann. of Math. **175** (2012); Kontsevich–Zagier, *Periods* (2001)).  Open.
* `CatalanPiAlgIndepConjecture`: `π` and Catalan's constant `G` are algebraically independent.  `G`
  is a period of mixed Tate motives over `ℤ[i, 1/2]`, and the same philosophy predicts this.  Open;
  even the irrationality of `G` is open.
* `Apery1979`: `ζ(3)` is irrational (R. Apéry, Astérisque **61** (1979)).  Theorem.
* `BallRivoal2001`: infinitely many `ζ(2k+1)` are irrational (K. Ball, T. Rivoal, Invent. Math.
  **146** (2001)).  Theorem.
-/
import Mathlib

namespace LeanFormalizations.Literature

open Complex

/-- **Sharp six exponentials theorem** (Waldschmidt): with `x` (two) and `y` (three)
`ℚ`-linearly independent and six algebraic `βᵢⱼ`, if every `e^{xᵢyⱼ − βᵢⱼ}` is algebraic, then
`xᵢyⱼ = βᵢⱼ` for all `i, j`. -/
def SixExponentialsSharp : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (β : Fin 2 → Fin 3 → ℂ),
    LinearIndependent ℚ x → LinearIndependent ℚ y → (∀ i j, IsAlgebraic ℚ (β i j)) →
    (∀ i j, IsAlgebraic ℚ (exp (x i * y j - β i j))) → ∀ i j, x i * y j = β i j

/-- **Zeta values conjecture** (from Grothendieck's period conjecture): `π, ζ(3), ζ(5), …, ζ(2n+1)`
are algebraically independent, for every `n`. -/
def ZetaValuesAlgIndepConjecture : Prop :=
  ∀ n : ℕ, AlgebraicIndependent ℚ
    (Fin.cons Real.pi fun k : Fin n ↦ (riemannZeta (2 * (k : ℕ) + 3)).re : Fin (n + 1) → ℝ)

/-- Catalan's constant `G = Σ (-1)^k / (2k+1)^2`. -/
noncomputable def catalanG : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2

/-- **Conjecture**: `π` and Catalan's constant are algebraically independent. -/
def CatalanPiAlgIndepConjecture : Prop := AlgebraicIndependent ℚ ![Real.pi, catalanG]

/-- **Apéry (1979)**: `ζ(3)` is irrational. -/
def Apery1979 : Prop := ∃ x : ℝ, Irrational x ∧ riemannZeta 3 = x

/-- **Ball–Rivoal (2001)**: infinitely many odd zeta values are irrational. -/
def BallRivoal2001 : Prop :=
  {k : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta (2 * k + 3) = x}.Infinite

end LeanFormalizations.Literature

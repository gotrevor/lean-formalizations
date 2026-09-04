/-
# The weighted residual matrix has full column rank (Sun, Theorem 2.1) — algebraic core

Field-generic core of §2 of arXiv:2609.04176v1.  The theorem is stated for an **abstract tail
sequence** `T : ℕ → F` satisfying only Sun's recurrence `T m + T (m+1) = 1/(2m+1)^2`
(`IsTailSeq`): that recurrence is the *only* property of the Catalan tails the proof uses, so
the same theorem serves the real tails (`Statement.lean`, over `ℝ`) and the fake rational tails
built from a hypothetical `G = a/q` (`TwoAdic.lean`, over `ℚ`).

## Statement

`resid T B S` is the `(S+3) × S` matrix
`R_{a,j} = Σ_{i=0}^{a+2B} (-1)^i C(a+2B, i) Π_i · T_{i+j}/(2(i+j)+1)`   (paper (2.1)),
rows `a ∈ {0,…,S+2}`, columns `j ∈ {1,…,S}` (here `j = j'.val + 1` for `j' : Fin S`), with
`Π_i = ∏_{h=1}^{B} (2(h+i)+1)^2` (`normaliser B i`).  **`resid_rank`: `rank = S` for `B > S > 0`.**

## Proof plan (the paper's argument, with its two index slips repaired)

⚠️ The paper's write-up (pp. 4–6) expands `T_{i+j}` around `T_i` in (2.4)–(2.8) but its
polynomial `K` in (2.12) uses `(2X+3)^2`, which only annihilates the integers if the expansion is
around **`T_{i+1}`** (the recurrence gives `T_i + T_{i+1} = 1/(2i+1)^2`, not `1/(2i+3)^2`); and
its `P_λ` sums from `k = 0`, where `(2i+1)^2 ∤ Π_i`, so it is not a polynomial.  Both are fixed
by ONE change — expand around `T_{i+1}` with `k ≥ 1` (`IsTailSeq.shift`) — which is what the
paper's own page-4 display already does.  With that repair the argument is:

1. `IsTailSeq.shift`: `T_{i+j+1} = (-1)^j T_{i+1} + Σ_{1≤k≤j} (-1)^{j-k}/(2(i+k)+1)^2`.
2. Hence `f_i := Π_i Σ_j λ_j u_{i+j} = -T_{i+1}·D_λ(i) + P_λ(i)` with
   `D_λ(X) = Σ_j (-1)^j λ_j Π(X)/(2X+2j+1)` (degree ≤ 2B−1, `= L_S·E²·P*_λ` in the paper's
   notation, nonzero when `λ ≠ 0`) and `P_λ` a polynomial of degree ≤ 2B−3 (needs `j ≤ S < B`).
3. `λ` in the right kernel ⟹ the alternating binomial sums of `f` of orders `2B..2B+S+2`
   vanish (`alt_choose_sum_eval_eq_zero` kills the polynomial part) ⟹ `f` agrees on
   `{0,…,2B+S+2}` with a polynomial of degree ≤ 2B−1 (`exists_poly_of_alt_sums_eq_zero`).
4. `A(X) := f(X) − P_λ(X)` has degree ≤ 2B−1 and `A(i) = -T_{i+1} D_λ(i)` for `i ≤ 2B+S+2`, so
   `K(X) := (2X+3)^2 [A(X) D_λ(X+1) + A(X+1) D_λ(X)] + D_λ(X) D_λ(X+1)` vanishes at
   `i = 0,…,2B+S+1` (by the recurrence at `m = i+1`), at `X = −3/2` (a root of `D_λ`), and is
   divisible by `G₀ := gcd(D_λ(X), D_λ(X+1))` of degree `2B−S−2` (roots at negative
   half-integers `≠ −3/2`): `4B+1` zeros against `deg K ≤ 4B`, so `K = 0`.
5. `K = 0` with `D_λ ≠ 0` gives a rational function `R = A/D_λ` with
   `R(X) + R(X+1) = −1/(2X+3)^2` — impossible (`no_rational_solution`).  Hence `λ = 0`.
-/
import Mathlib

namespace LeanFormalizations.Catalan

open Finset Polynomial

variable {F : Type*} [Field F] [CharZero F]

/-- The normaliser `Π_i = ∏_{h=1}^{B} (2(h+i)+1)^2` of Theorem 2.1.  A product of **odd**
squares — the fact `TwoAdic.lean` turns against §9. -/
def normaliser (B i : ℕ) : ℕ := ∏ h ∈ Icc 1 B, (2 * (h + i) + 1) ^ 2

/-- Sun's recurrence (1.4) for an abstract tail sequence: `T m + T (m+1) = 1/(2m+1)^2`.  This is
the *whole* interface between analysis and the algebraic core. -/
def IsTailSeq (T : ℕ → F) : Prop := ∀ m, T m + T (m + 1) = 1 / (2 * (m : F) + 1) ^ 2

/-- The **weighted residual matrix** (paper (2.1)):
`R_{a,j} = Σ_{i=0}^{a+2B} (-1)^i C(a+2B,i) Π_i · T_{i+j}/(2(i+j)+1)`, `(S+3) × S`.
Column index `j' : Fin S` stands for the paper's `j = j'+1 ∈ {1,…,S}`. -/
noncomputable def resid (T : ℕ → F) (B S : ℕ) : Matrix (Fin (S + 3)) (Fin S) F :=
  fun a j => ∑ i ∈ range (a.val + 2 * B + 1),
    (-1 : F) ^ i * ((a.val + 2 * B).choose i : F) * (normaliser B i : F) *
      (T (i + j.val + 1) / (2 * ((i + j.val + 1 : ℕ) : F) + 1))

/-! ### Leaves of the proof plan (see the module docstring) -/

/-- **Finite-difference annihilation** (van Lint–Wilson (13.13)): the `n`-th alternating
binomial sum of a polynomial of degree `< n` vanishes.  Mathlib carries this as
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` + `fwdDiff_iter_eq_sum_shift`. -/
theorem alt_choose_sum_eval_eq_zero (P : F[X]) {n : ℕ} (hP : P.natDegree < n) :
    ∑ i ∈ range (n + 1), (-1 : F) ^ i * (n.choose i : F) * P.eval (i : F) = 0 := by
  sorry

/-- **Corrected (2.3)**, expanded around `T_{i+1}`:
`T_{i+j+1} = (-1)^j T_{i+1} + Σ_{k=1}^{j} (-1)^{j-k} / (2(i+k)+1)^2`.  Induction on `j` from
the recurrence at `m = i + j`. -/
theorem IsTailSeq.shift {T : ℕ → F} (hT : IsTailSeq T) (i j : ℕ) :
    T (i + j + 1) = (-1 : F) ^ j * T (i + 1) +
      ∑ k ∈ Icc 1 j, (-1 : F) ^ (j - k) / (2 * ((i + k : ℕ) : F) + 1) ^ 2 := by
  sorry

/-- **Newton-interpolation degree bound.**  A sequence on `{0,…,N}` whose alternating binomial
sums of every order `n ∈ [m, N]` vanish is the restriction of a polynomial of degree `< m`.
(Interpolate with `Lagrange.interpolate`, then read the vanishing sums as
`Δ^n P (0) = 0` via `fwdDiff_iter_eq_sum_shift`; Newton's formula
`shift_eq_sum_fwdDiff_iter` rebuilds `P` from `Δ^n P (0)`, `n < m`, on all of `ℕ`, and two
polynomials agreeing on `ℕ` are equal.) -/
theorem exists_poly_of_alt_sums_eq_zero (f : ℕ → F) (m N : ℕ)
    (h : ∀ n, m ≤ n → n ≤ N →
      ∑ i ∈ range (n + 1), (-1 : F) ^ i * (n.choose i : F) * f i = 0) :
    ∃ P : F[X], P.degree < m ∧ ∀ i ≤ N, P.eval (i : F) = f i := by
  sorry

/-- **The Gosper-style obstruction** (paper p. 6, sharpened and sign-agnostic): no rational
function `R = A/D` satisfies `R(X) + R(X+1) = c/(2X+3)^2` with `c ≠ 0`.
Proof: WLOG `gcd(A, D) = 1` (the identity is homogeneous of degree 2 in `(A, D)`).  Then
`D(X) ∣ (2X+3)^2 D(X+1)` and `D(X+1) ∣ (2X+3)^2 D(X)`.  In an algebraic closure pick a root
`α` of `D` with `α+1` not a root: it must be `−3/2`; pick a root `β` with `β−1` not a root: it
must be `−1/2`.  Every root class `α + ℤ` therefore has maximum `−3/2` and minimum `−1/2`,
absurd; so `D` is constant, and then `(2X+3)^2 (A(X)+A(X+1)) = c` fails at `X = −3/2`. -/
theorem no_rational_solution (A D : F[X]) (hD : D ≠ 0) (c : F) (hc : c ≠ 0)
    (h : (2 * X + 3) ^ 2 * (A * D.comp (X + 1) + A.comp (X + 1) * D) =
      C c * (D * D.comp (X + 1))) : False := by
  sorry

/-- **The crux** (steps 2–5 of the plan): the right kernel of `resid T B S` is trivial. -/
theorem resid_mulVec_eq_zero {T : ℕ → F} (hT : IsTailSeq T) {B S : ℕ} (hS : 0 < S)
    (hBS : S < B) (lam : Fin S → F) (h : (resid T B S).mulVec lam = 0) : lam = 0 := by
  sorry

/-- **Theorem 2.1** for an abstract tail sequence: `rank (resid T B S) = S` when `B > S > 0`.
Wiring: trivial right kernel ⟹ `mulVecLin` injective ⟹ `rank = finrank (Fin S → F) = S`. -/
theorem resid_rank (T : ℕ → F) (hT : IsTailSeq T) {B S : ℕ} (hS : 0 < S) (hBS : S < B) :
    (resid T B S).rank = S := by
  have hinj : Function.Injective (resid T B S).mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro lam hlam
    exact resid_mulVec_eq_zero hT hS hBS lam hlam
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

end LeanFormalizations.Catalan

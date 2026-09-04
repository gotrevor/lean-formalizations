/-
# N2 — the decomposition: `d_n^s · r_n` is an integer combination of `1, β(2), β(4), …, β(s-1)`

The arithmetic heart.  Partial fractions of `R_n`,

    R_n(t) = Σ_{i=1}^{s} Σ_{k=0}^{n} a_{i,k} / (t+k)^i,

give `r_n = Σ_{i even, 2 ≤ i ≤ s-1} A_i β(i) + A_0` with `A_i = 2^i Σ_k (-1)^{k-1} a_{i,k}`.  Two
facts do the work:

* **integrality** (SIGMA Lemma 1): `d_n^{s-i} a_{i,k} ∈ ℤ`, where `d_n = lcm(1,…,n)`;
* **odd vanishing**: `R_n(-t-n) = R_n(t)` for odd `s`, which kills `A_i` for odd `i`.

The frozen statement below asks only for what the ledger actually consumes: **some** integer
vector `A` with `d_n^s · r_n = A_0 + Σ_i A_i β(2i)`.  That is implied by the finer
`d_n^{s-i} A_i ∈ ℤ` (multiply by `d_n^i`), and it is strictly easier to prove, so it does not
commit the treadmill to a particular partial-fraction route.

✅ Validated numerically (`papers/catalan-beta-validate.py`) at `(n,s) ∈ {(2,5),(4,5),(2,7),(4,7),(6,7)}`:
`d_n^{s-i} a_{i,k} ∈ ℤ`, the odd `A_i` vanish, the decomposition reproduces `r_n`, and every
`d_n^{s-i} A_i`, `d_n^s A_0` has denominator `1`.  **Hypotheses `Odd s`, `Even n` are exactly the
range validated** — do not weaken them without a fresh probe (the Phase 3 `E1` lesson).
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Beta
import LeanFormalizations.NumberTheory.DirichletBeta.Rational

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- `d_n = lcm(1, …, n)`, as in `Mathlib.NumberTheory.Chebyshev`. -/
noncomputable abbrev dn (n : ℕ) : ℕ := Nat.lcmUpto n

/-- **N2 (the decomposition).**  For odd `s ≥ 3` and even `n`, `d_n^s · r_n` is a ℤ-linear
combination of `1` and the even beta values `β(2), β(4), …, β(s-1)`.

The `β` indices are `2i` for `1 ≤ i ≤ (s-1)/2`; at `s = 21` that is `β(2), β(4), …, β(20)`. -/
theorem exists_int_combination {s n : ℕ} (hs : 3 ≤ s) (hodd : Odd s) (hn : Even n) :
    ∃ A : ℕ → ℤ,
      ((dn n : ℝ)) ^ s * rForm s n
        = (A 0 : ℝ) + ∑ i ∈ Icc 1 ((s - 1) / 2), (A i : ℝ) * dirichletBeta (2 * i) := by
  sorry

end LeanFormalizations.DirichletBeta

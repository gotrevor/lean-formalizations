/-
# The rational function `R_n` and the linear form `r_n`

Zudilin 2019 (arXiv:1804.09922) §2, in the elementary rendering of his SIGMA 2018 paper.  For
odd `s ≥ 3` and even `n`,

    R_n(t) = 2^{6n} · (n!)^{s-3} · (2t+n) · ∏_{j=1}^{3n} (t - n + j - ½) / ∏_{j=0}^{n} (t+j)^s
    r_n    = Σ_{ν ≥ 1} (-1)^ν R_n(ν - ½).

The terms with `ν ≤ n` vanish (the `j = n+1-ν` factor of the numerator is `0`), so the sum really
starts at `ν = n+1`.  Substituting `ν = n + 1 + u` clears every subtraction and turns the
numerator product into a ratio of factorials:

    2t + n              = 3n + 1 + 2u
    ∏_{j=1}^{3n}(…)     = (u + 3n)! / u!
    t + j               = (2(n+1+u+j) - 1)/2.

`Rval` below is that shifted form — the one this development freezes.  ✅ Verified numerically
against the source form (termwise **exactly**, and as a sum to 12 digits) at
`(n,s) ∈ {(2,5),(4,5),(2,7),(4,7),(6,7),(2,21),(4,21),(6,21)}`:
`papers/catalan-beta-rval-check.py`.

Rates (`papers/catalan-beta-ledger.py`, `n = 40`): for `s = 21`,
`log|r_n|^{1/n} → -21.657`, while `d_n^{1/n} → e`.  Since `21 < 21.657`, the ledger closes.
-/
import Mathlib

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- `R_n(ν - ½)` at `ν = n + 1 + u`, in the subtraction-free shifted form.  Frozen: every
downstream statement is about this function.

`Rval s n u = 2^{6n} (n!)^{s-3} (3n+1+2u) · (u+3n)!/u! / ∏_{j=0}^{n} ((2(n+1+u+j) - 1)/2)^s`. -/
noncomputable def Rval (s n u : ℕ) : ℚ :=
  2 ^ (6 * n) * (Nat.factorial n : ℚ) ^ (s - 3) * ((3 * n + 1 + 2 * u : ℕ) : ℚ)
    * (Nat.factorial (u + 3 * n) : ℚ) / (Nat.factorial u : ℚ)
    / ∏ j ∈ range (n + 1), ((2 * ((n : ℚ) + 1 + u + j) - 1) / 2) ^ s

/-- Every term of the shifted series is strictly positive. -/
theorem Rval_pos (s n u : ℕ) : 0 < Rval s n u := by
  sorry

/-- **The linear form.**  `r_n = Σ_{u ≥ 0} (-1)^{n+u+1} R_n(n+1+u-½)`, as a real number.  (For
even `n` the leading sign is `-1`, which is why `r_n < 0`; see `Integral.lean`.) -/
noncomputable def rForm (s n : ℕ) : ℝ :=
  ∑' u : ℕ, (-1 : ℝ) ^ (n + u + 1) * (Rval s n u : ℝ)

/-- **R1.**  The defining series of `rForm` converges absolutely for `s ≥ 3`: the terms decay
like `u^{3n + 1 - s(n+1)}`, an exponent `≤ -2` once `s ≥ 3`. -/
theorem summable_Rval {s n : ℕ} (hs : 3 ≤ s) :
    Summable (fun u : ℕ => (Rval s n u : ℝ)) := by
  sorry

end LeanFormalizations.DirichletBeta

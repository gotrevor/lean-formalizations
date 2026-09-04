/-
# N3 — nonvanishing: `r_n < 0` (**the crux**)

`r_n` is a nonzero *number*, and nothing about the ledger proves that; it comes from a positive
integral.  Expanding `(1 - T)/(1 + T)^{3n+2}` (`T = ∏ t_j`) in its binomial series and integrating
term by term (`integral_fintype_prod_eq_prod`, absolutely convergent for `s ≥ 3`) gives

    |r_n| = 2^{6n} (3n+1)!/n!³ · ∫_{[0,1]^s} (1 - T) ∏_j t_j^{n-½}(1-t_j)^n / (1+T)^{3n+2} dt > 0,

each summand being `const · (-1)^ν R_n(ν-½)`.  ✅ Checked numerically at `s = 3, n = 2`
(`papers/catalan-beta-validate.py`, part (c)): `r_n = -176.3156483` against the integral
`+176.3156483` — hence the **sign convention `r_n = -C_n · ∫`**, and `r_n < 0` for even `n`.

`rForm_ne_zero` is the only thing downstream consumes.  It is stated separately so a treadmill lap
that cannot land the sign still owes only nonvanishing.

✅ Sign verified at `(n,s) ∈ {(2,5),(4,5),(2,7),(4,7),(6,7),(2,21),(4,21),(6,21)}` and, via
`papers/catalan-beta-ledger.py` at `n = 40`, for every odd `s` from `7` to `41`.
-/
import Mathlib
import LeanFormalizations.NumberTheory.DirichletBeta.Rational

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- **N3 (the crux).**  For odd `s ≥ 3` and even `n`, the linear form is strictly negative.
The leading term `u = 0` carries the sign `(-1)^{n+1} = -1` and dominates. -/
theorem rForm_neg {s n : ℕ} (hs : 3 ≤ s) (hodd : Odd s) (hn : Even n) : rForm s n < 0 := by
  sorry

/-- **Nonvanishing** — what the ledger consumes. -/
theorem rForm_ne_zero {s n : ℕ} (hs : 3 ≤ s) (hodd : Odd s) (hn : Even n) : rForm s n ≠ 0 :=
  ne_of_lt (rForm_neg hs hodd hn)

end LeanFormalizations.DirichletBeta

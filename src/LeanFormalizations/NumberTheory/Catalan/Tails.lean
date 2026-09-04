/-
# Catalan's constant: tails and Sun's weighted tails (§1 of arXiv:2609.04176v1)

Faithful rendering of the §1 objects of Zhi-Wei Sun, *Catalan's constant is irrational*,
arXiv:2609.04176v1 (3 Sep 2026).  ⚠️ The paper's headline claim (`G ∉ ℚ`) is **false as
proved** — see `TwoAdic.lean` and `papers/sun-2026-catalan-irrationality.md` — but §1–§2 are
sound, and this thread formalises exactly what survives.  Nothing in this directory claims,
or should ever claim, that Catalan's constant is irrational.

* `tail m`      = `T_m = Σ_{r ≥ 0} (-1)^r / (2(m+r)+1)^2`          (paper (1.1));
* `catalanConst` = `G = T_0 = Σ (-1)^k/(2k+1)^2 = 0.91596…`;
* `partialSum m` = `S_{m-1} = Σ_{k < m} (-1)^k/(2k+1)^2`;
* `wtail m`     = `u_m = T_m / (2m+1)`                             (paper (1.2), Sun's weighting).

The algebraic core (`Residual.lean`) consumes ONE analytic fact: the recurrence
`tail_add_tail_succ : T_m + T_{m+1} = 1/(2m+1)^2` (paper (1.4)).  Everything else here is a
sanity anchor ((1.1) as a theorem, the bounds (1.3)).
-/
import Mathlib

namespace LeanFormalizations.Catalan

open Finset

/-- The `m`-th tail `T_m = Σ_{r ≥ 0} (-1)^r / (2(m+r)+1)^2` of the Catalan series (paper (1.1)). -/
noncomputable def tail (m : ℕ) : ℝ := ∑' r : ℕ, (-1 : ℝ) ^ r / (2 * ((m : ℝ) + r) + 1) ^ 2

/-- Catalan's constant `G = β(2) = Σ_{k ≥ 0} (-1)^k / (2k+1)^2`, as the zeroth tail. -/
noncomputable def catalanConst : ℝ := tail 0

/-- The partial sum `S_{m-1} = Σ_{k < m} (-1)^k / (2k+1)^2` (paper §1; note the index shift). -/
noncomputable def partialSum (m : ℕ) : ℝ := ∑ k ∈ range m, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2

/-- Sun's **weighted tail** `u_m = T_m / (2m+1)` (paper (1.2)) — the author's own contribution,
and the reason the residual matrix of §2 has full column rank. -/
noncomputable def wtail (m : ℕ) : ℝ := tail m / (2 * (m : ℝ) + 1)

/-- The tail series converges absolutely (compare with `1/r^2`). -/
theorem summable_tailTerm (m : ℕ) :
    Summable (fun r : ℕ => (-1 : ℝ) ^ r / (2 * ((m : ℝ) + r) + 1) ^ 2) := by
  sorry

/-- **Recurrence (1.4)**: `T_m + T_{m+1} = 1/(2m+1)^2`.  Peel the first term of `T_m`
(`Summable.tsum_eq_zero_add`); the remainder is `-T_{m+1}`.  This is the only analytic input to
`Residual.lean`. -/
theorem tail_add_tail_succ (m : ℕ) : tail m + tail (m + 1) = 1 / (2 * (m : ℝ) + 1) ^ 2 := by
  sorry

/-- **(1.1)**: `T_m = (-1)^m (G - S_{m-1})`.  Induction on `m` from `tail_add_tail_succ`. -/
theorem tail_eq_catalan_sub_partialSum (m : ℕ) :
    tail m = (-1 : ℝ) ^ m * (catalanConst - partialSum m) := by
  sorry

/-- **(1.3), lower half**: `0 < T_m` (alternating series with decreasing terms). -/
theorem tail_pos (m : ℕ) : 0 < tail m := by
  sorry

/-- **(1.3), upper half**: `T_m < 1/(2m+1)^2`. -/
theorem tail_lt (m : ℕ) : tail m < 1 / (2 * (m : ℝ) + 1) ^ 2 := by
  sorry

end LeanFormalizations.Catalan

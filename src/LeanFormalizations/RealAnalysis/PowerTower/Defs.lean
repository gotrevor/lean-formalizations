/-
# Infinite power tower (Euler 1783) — shared definitions

The definitions referenced by the load-bearing statements in `Statement.lean`
(the designated audit surface). They live here so the proof engine and the audit
surface can both refer to them. Audit these against the source:

- `tower x n` is the finite power tower `ⁿx = x^(x^(··^x))` with `n` copies of
  `x`, indexed so `tower x 0 = 1`, `tower x 1 = x`, `tower x 2 = x^x`. The
  exponent is real, so `^` is `Real.rpow` — the correct notion for `xⁱ` with
  irrational intermediate values.
- `eInvE` is Euler's constant `e^(1/e)`, the upper endpoint of the interval of
  convergence `[e^(-e), e^(1/e)]`.

Source: L. Euler, *De formulis exponentialibus replicatis* (1783); modern survey
L. Lóczi, "The strange properties of the infinite power tower", arXiv:1908.05559.
-/
import Mathlib

namespace LeanFormalizations.RealAnalysis.PowerTower

open Real

/-- The finite power tower `tower x n = ⁿx`, i.e. `x ^ (x ^ (… ^ x))` with `n`
copies of `x`. Indexed so that `tower x 0 = 1`, `tower x 1 = x`,
`tower x 2 = x ^ x`. The exponent is real, so `^` is `Real.rpow`. -/
noncomputable def tower (x : ℝ) : ℕ → ℝ
  | 0     => 1
  | (n+1) => x ^ tower x n

/-- Euler's constant `e ^ (1/e) ≈ 1.44467`: the upper endpoint of the interval of
convergence `[e^(-e), e^(1/e)]` for the infinite power tower. -/
noncomputable def eInvE : ℝ := Real.exp (1 / Real.exp 1)

@[simp] theorem tower_zero (x : ℝ) : tower x 0 = 1 := rfl

theorem tower_succ (x : ℝ) (n : ℕ) : tower x (n + 1) = x ^ tower x n := rfl

@[simp] theorem tower_one (x : ℝ) : tower x 1 = x := by
  show x ^ tower x 0 = x
  rw [tower_zero, Real.rpow_one]

/-- Machine-checked anchor: at the upper endpoint `x = e^(1/e)`, the value `L = e`
solves the tower's fixed-point equation `x^L = L`, since `(e^(1/e))^e = e`. This is
the limit the tower converges to at the boundary. (Lives here, not in
`Statement.lean`, because the convergence engine needs it for the `x^t ≤ e` bound
and `Engine.lean` cannot import the audit surface.) -/
theorem endpoint_fixed_point : eInvE ^ Real.exp 1 = Real.exp 1 := by
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have key : 1 / Real.exp 1 * Real.exp 1 = 1 := by field_simp
  rw [eInvE, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, key]

end LeanFormalizations.RealAnalysis.PowerTower

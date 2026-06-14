/-
# Infinite power tower: interval of convergence (upper half) — Euler (1783)

For `x > 0`, the infinite power tower `lim_{n→∞} ⁿx` (with `ⁿx = x^(x^(··^x))`,
`n` copies, here `tower x n`) converges **iff** `x ∈ [e^(-e), e^(1/e)]`
(Euler 1783; numerically `[0.0660, 1.4447]`).

This file is the **designated audit surface** for the *upper* half: the `x ≥ 1`
regime, whose sharp boundary is `e^(1/e)`. There `t ↦ x^t` is increasing, so the
tower is monotone and the analysis is the elementary "monotone bounded by the
least fixed point" argument. (The lower half `e^(-e) ≤ x < 1` is the *oscillating*
regime — `t ↦ x^t` is decreasing, needing 2-cycle stability of `g(t) = x^(x^t)` —
and is deferred to a separate file.)

The two definitions referenced here (`tower`, `eInvE`) live in `Defs.lean`; audit
those alongside this file.

## Status
- `tower_converges` — the convergence direction, **`sorry`** (the analytic core:
  monotone-bounded convergence to the least fixed point).
- `tower_diverges` — divergence past the threshold, **`sorry`** (`x^t > t` for all
  `t`, so the increasing sequence is unbounded).
- `tower_converges_iff` — the headline ("interval of convergence" on `[1,∞)`),
  **PROVED** from the two facts above.
- `endpoint_fixed_point` — machine-checked anchor `(e^(1/e))^e = e`, **PROVED**.

When the engine is built, move the two `sorry`s into an `Engine.lean` sibling and
make the statements here delegate to it (`:= …_engine`), per the repo's
audit-surface doctrine.
-/
import LeanFormalizations.RealAnalysis.PowerTower.Defs

open Real Filter Topology

namespace LeanFormalizations.RealAnalysis.PowerTower

/-- **Convergence on `[1, e^(1/e)]`.** For `1 ≤ x ≤ e^(1/e)` the infinite power
tower `ⁿx` converges to a real limit `L`, which is a fixed point of `t ↦ x^t`
(`x^L = L`) lying in `[1, e]`. (`L` is in fact the least such fixed point; the
value at the top endpoint `x = e^(1/e)` is `L = e`, cf. `endpoint_fixed_point`.) -/
theorem tower_converges {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ eInvE) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L ∧ 1 ≤ L ∧ L ≤ Real.exp 1 := by
  sorry

/-- **Divergence past the threshold.** For `x > e^(1/e)` the tower diverges to
`+∞` (the curve `t ↦ x^t` lies strictly above the diagonal, so the increasing
sequence has no fixed-point ceiling). Together with `tower_converges` this pins
`e^(1/e)` as the sharp upper endpoint of convergence on `[1, ∞)`. -/
theorem tower_diverges {x : ℝ} (hx : eInvE < x) :
    Tendsto (tower x) atTop atTop := by
  sorry

/-- **Sharp upper endpoint (headline).** On `[1, ∞)` the infinite power tower
converges **iff** `x ≤ e^(1/e)`. This is the "interval of convergence" answer for
the increasing regime. Proved here from `tower_converges` and `tower_diverges`,
so only those two analytic facts remain to be discharged. -/
theorem tower_converges_iff {x : ℝ} (hx1 : 1 ≤ x) :
    (∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L)) ↔ x ≤ eInvE := by
  constructor
  · rintro ⟨L, hL⟩
    by_contra h
    push Not at h
    exact not_tendsto_atTop_of_tendsto_nhds hL (tower_diverges h)
  · intro hx2
    obtain ⟨L, hL, _⟩ := tower_converges hx1 hx2
    exact ⟨L, hL⟩

/-- Machine-checked anchor: at the upper endpoint `x = e^(1/e)`, the value `L = e`
solves the tower's fixed-point equation `x^L = L`, since `(e^(1/e))^e = e`. This is
the limit the tower converges to at the boundary. -/
theorem endpoint_fixed_point : eInvE ^ Real.exp 1 = Real.exp 1 := by
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have key : 1 / Real.exp 1 * Real.exp 1 = 1 := by field_simp
  rw [eInvE, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, key]

end LeanFormalizations.RealAnalysis.PowerTower

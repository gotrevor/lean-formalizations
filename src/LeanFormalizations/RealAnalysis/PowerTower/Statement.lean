/-
# Infinite power tower: interval of convergence — Euler (1783)

For `x > 0`, the infinite power tower `lim_{n→∞} ⁿx` (with `ⁿx = x^(x^(··^x))`,
`n` copies, here `tower x n`) converges **iff** `x ∈ [e^(-e), e^(1/e)]`
(Euler 1783; numerically `[0.0660, 1.4447]`).

This file is the **designated audit surface** for the convergence theorem on the
whole interval. The `x ≥ 1` regime has sharp boundary `e^(1/e)` (`t ↦ x^t`
increasing ⟹ tower monotone). The lower regime `e^(-e) ≤ x < 1` is *oscillating*
(`t ↦ x^t` decreasing ⟹ even/odd subsequences, 2-cycle of `g(t) = x^(x^t)`); its
crux is the bifurcation at `e^(-e)` (`EngineLower.two_cycle_collapse`).

The definitions referenced here (`tower`, `eInvE`, `eNegE`) live in `Defs.lean`;
audit those alongside this file.

## Status — PROVED (axiom-clean)
- `tower_converges` — convergence for `1 ≤ x ≤ e^(1/e)`, **PROVED**
  (`tower_converges_engine`: monotone-bounded convergence to a fixed point).
- `tower_diverges` — divergence for `x > e^(1/e)`, **PROVED**.
- `tower_converges_iff` — interval of convergence on `[1,∞)`, **PROVED**.
- `tower_converges_of_mem` — **headline**: convergence on the full Euler interval
  `[e^(-e), e^(1/e)]`, **PROVED** (stitches the upper engine with the lower-half
  `tower_converges_lower`; the lower crux is fully discharged, no axiom).
- `endpoint_fixed_point` / `endpoint_fixed_point_lower` — machine-checked anchors
  `(e^(1/e))^e = e` and `(e^(-e))^(1/e) = 1/e` (in `Defs.lean`).

The real proofs live in the `Engine.lean` / `EngineLower.lean` siblings, per the
repo's audit-surface doctrine; the statements here delegate.
-/
import LeanFormalizations.RealAnalysis.PowerTower.Engine
import LeanFormalizations.RealAnalysis.PowerTower.EngineLower

open Real Filter Topology

namespace LeanFormalizations.RealAnalysis.PowerTower

/-- **Convergence on `[1, e^(1/e)]`.** For `1 ≤ x ≤ e^(1/e)` the infinite power
tower `ⁿx` converges to a real limit `L`, which is a fixed point of `t ↦ x^t`
(`x^L = L`) lying in `[1, e]`. (`L` is in fact the least such fixed point; the
value at the top endpoint `x = e^(1/e)` is `L = e`, cf. `endpoint_fixed_point`.) -/
theorem tower_converges {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ eInvE) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L ∧ 1 ≤ L ∧ L ≤ Real.exp 1 :=
  tower_converges_engine hx1 hx2

/-- **Divergence past the threshold.** For `x > e^(1/e)` the tower diverges to
`+∞` (the curve `t ↦ x^t` lies strictly above the diagonal, so the increasing
sequence has no fixed-point ceiling). Together with `tower_converges` this pins
`e^(1/e)` as the sharp upper endpoint of convergence on `[1, ∞)`. -/
theorem tower_diverges {x : ℝ} (hx : eInvE < x) :
    Tendsto (tower x) atTop atTop :=
  tower_diverges_engine hx

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

/-- **Euler's convergence theorem on the full interval (headline, MANDATORY).**
For every `x ∈ [e^(-e), e^(1/e)]` the infinite power tower `ⁿx` converges to a real
limit `L`, a fixed point of `t ↦ x^t` (`x^L = L`). This stitches the three regimes:
the increasing regime `x ≥ 1` (`tower_converges_engine`, monotone-bounded
convergence) and the oscillating regime `e^(-e) ≤ x < 1` (`tower_converges_lower`,
even/odd subsequences collapse to a common fixed point). The lower endpoint `e^(-e)`
is sharp — its boundary value is `L = 1/e` (cf. `endpoint_fixed_point_lower`).

The lower-half analytic crux (no nontrivial 2-cycle for `x ≥ e^(-e)`) is the
machine-checked `EngineLower.two_cycle_collapse` (NO axiom) — proved via the slope
bound `g'(t) ≤ |log x|/e ≤ 1`: a Banach contraction for `x > e^(-e)`, an
antitone-on-interval argument at the boundary `x = e^(-e)`. This whole theorem is
axiom-clean (`[propext, Classical.choice, Quot.sound]`). -/
theorem tower_converges_of_mem {x : ℝ} (hx : x ∈ Set.Icc eNegE eInvE) :
    ∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L) ∧ x ^ L = L := by
  obtain ⟨hlo, hhi⟩ := hx
  rcases lt_or_ge x 1 with h | h
  · -- oscillating regime e^(-e) ≤ x < 1
    exact tower_converges_lower hlo h
  · -- increasing regime 1 ≤ x ≤ e^(1/e)
    obtain ⟨L, hL, hfix, _, _⟩ := tower_converges_engine h hhi
    exact ⟨L, hL, hfix⟩

/-- **Euler's power-tower theorem, SHARP (headline, MANDATORY).** For every `x > 0`
the infinite power tower `ⁿx` converges **iff** `x ∈ [e^(-e), e^(1/e)]`
(numerically `[0.0660, 1.4447]`). Both endpoints are sharp:
- `x > e^(1/e)` diverges to `+∞` (`tower_diverges`);
- `0 < x < e^(-e)` diverges by *oscillation* — the even/odd subsequences are trapped
  on opposite sides of a genuine attracting 2-cycle `β₀ < γ₀`, so their limits differ
  (`EngineLower.tower_diverges_lower`, the sharp converse of `two_cycle_collapse`);
- `x ∈ [e^(-e), e^(1/e)]` converges (`tower_converges_of_mem`).

This is the full "interval of convergence" statement, axiom-clean
(`[propext, Classical.choice, Quot.sound]`). -/
theorem tower_converges_iff_full {x : ℝ} (hx : 0 < x) :
    (∃ L : ℝ, Tendsto (tower x) atTop (𝓝 L)) ↔ x ∈ Set.Icc eNegE eInvE := by
  constructor
  · rintro ⟨L, hL⟩
    rw [Set.mem_Icc]
    by_contra hmem
    push Not at hmem
    rcases lt_or_ge x eNegE with hlo | hlo
    · exact tower_diverges_lower hx hlo ⟨L, hL⟩
    · exact not_tendsto_atTop_of_tendsto_nhds hL (tower_diverges (hmem hlo))
  · intro hmem
    obtain ⟨L, hL, _⟩ := tower_converges_of_mem hmem
    exact ⟨L, hL⟩

end LeanFormalizations.RealAnalysis.PowerTower

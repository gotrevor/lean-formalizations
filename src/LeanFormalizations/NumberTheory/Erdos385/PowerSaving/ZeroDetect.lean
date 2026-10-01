/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Deviation

/-!
# Erdős #385 power saving: local zero detection (phase E9b, the crux)

**Why not `NearOneLargeValues`.**  The frozen `NearOneLargeValues` (PowerSaving.lean) asks, for
*every* smooth compactly supported weight `f`, that large values `‖vkDev f P t‖ ≥ P^{1−η}` number
`≪ T^{Bη^{3/2}} (log T)^C`.  The only known mechanism is the local explicit formula: a large value
at `t` forces a zero `ρ` with `β ≥ 1 − O(η)` and `|γ − t| ≤ L`, where `L` is the height at which
the Mellin tail `∫_{|u|>L} |mellin f(1+iu)| du` drops below `P^{−η}`.  A single zero at
`β = 1 − η/2` then produces `≍ L` large values around `γ`.  For a Gevrey weight
(`|mellin f(1+iu)| ≤ e^{−c|u|^α}`) `L` is polylogarithmic and the count is fine; but a general
`C_c^∞` weight can have Mellin decay as slow as `exp(−(log u)²)` (`SlowMellinWeight`), giving
`L = exp(√(η log P))`, which exceeds `T^{Bη^{3/2}}` once `η ≪ (log P)^{−1/2}`, a range VK does
not empty.  So `nearOneLargeValues_of_density` would need zero-free information beyond VK.  It
stays a disclosed hole, off the headline path (Maze row "NearOneLargeValues for every weight").

**What the headline needs** (`LargeValueCount`, LargeValueSum.lean) is only a count
`≪ (log Z)^C u^{−1/2} = (log P)^C P^{η/2}` at `P = √Z`, `u/2 = P^{−η}`.  A polynomial loss
`L ≍ P^{η/3}` is affordable.  That is `LocalZeroDetect` below; with `NearOneZeroDensity` it gives
`#large ≤ (2L+1)·2N(1 − 2η − o(1), 2T) ≪ P^{η/3 + O(η^{3/2})} (log P)^C ≤ P^{η/2}` for `η ≤ η₀`.

## Route for `localZeroDetect_of_richert` (contrapositive; 75%)

Suppose no zero has `Re ρ ≥ 1 − 3η₂/2` and `|Im ρ − t| ≤ L + 1`, where
`η₂ = η + 3 log log P / log P`, `L = (A/2) P^{η/3} log P`.  Write `G(s) = F(s) P^s H(s + it)`,
`F = mellin f`, `H = ζ'/ζ + 1/(w − 1)` (`zetaH`).  By V4 (`smoothTwist_sub_main_eq`),
`vkDev = −(1/2π) ∫_ℝ G(2 + iy) dy`.
1. **Tails on `Re s = 2`**, `|y| > P`: `≤ P² B · K/P³`.
2. **Shift `[c, 2] × [−P, P]`**, `c = 1 + 1/log P`: `|H| ≤ 3 log P` on `Re w ≥ c`
   (`logDeriv_zeta_dirichlet_bound`); horizontals `≤ 3K log P / P²`.
3. **Middle tails on `Re s = c`**, `L < |y| ≤ P`: `≤ 3e K P log P / L³` (`F ≪ y^{−4}`).
4. **Shift `[1 − η₂, c] × [−L, L]`**: by Landau's local lemma (`Landau.local_landau` on
   `closedBall (1 + η₂ + iy₀) (4η₂)`; growth from Richert for `σ ≤ 1` and PNT+ `ZetaUpperBnd` for
   `σ ≥ 1`, centre from PNT+ `ZetaLowerBound3`), `|H| ≤ K (log P)²` on the box.  Left side
   `≤ Kπ P^{1−η₂} (log P)² = Kπ P^{1−η} / log P`; horizontals `≤ K e P (log P)² / L⁴`.
Each piece is `≤ P^{1−η}/8` for `P ≥ P₀`, contradiction.
-/

namespace LeanFormalizations.Erdos385

open Real Complex LeanFormalizations.Literature

/-- **Local zero detection.**  A large deviation `‖vkDev f P t‖ ≥ P^{1−η}` of the smoothed prime
sum at a height `t` with `A P^{η/3} log P ≤ |t| ≤ P⁴` forces a zero of `ζ` with real part
`≥ 1 − 2η − A log log P / log P` within `A P^{η/3} log P / 2` of `t`.  The polynomial window
`P^{η/3}` is the price of a general `C^∞` weight (Mellin decay `≪ |u|^{−4}`); see the header. -/
def LocalZeroDetect : Prop :=
  ∀ f : ℝ → ℂ, (∀ k : ℕ, ContDiff ℝ k f) → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
    ∃ A P₀ : ℝ, 0 ≤ A ∧ ∀ P η t : ℝ, P₀ ≤ P → 0 < η → η ≤ 1 / 16 → |t| ≤ P ^ 4 →
      A * P ^ (η / 3) * Real.log P ≤ |t| →
      P ^ (1 - η) ≤ ‖vkDev f P t‖ →
      ∃ ρ : ℂ, riemannZeta ρ = 0 ∧
        1 - 2 * η - A * Real.log (Real.log P) / Real.log P ≤ ρ.re ∧
        |ρ.im - t| ≤ A * P ^ (η / 3) * Real.log P / 2

/-- **The crux of phase E9b**: local zero detection from Richert's growth bound (route in the
header: V4 + two rectangle shifts + Landau's local lemma at scale `η₂`).  75%. -/
theorem localZeroDetect_of_richert (h : RichertZetaGrowth) : LocalZeroDetect := by
  sorry

/-- **The obstruction to `NearOneLargeValues` for every weight** (Maze anchor): a smooth weight
supported in `(0, ∞)` whose Mellin transform on `Re s = 1` beats every `C e^{−|u|^α}`
infinitely often.  Believed true (95%: sum of bumps at scales `2^{−k}` with weights `e^{−k²}`
gives decay `≍ exp(−(log u)²)`); not proved here.  With such a weight, one zero at
`β = 1 − η/2` makes `≍ exp(√(η log P))` large values, more than `T^{Bη^{3/2}}` for
`(log P)^{−2/3} ≪ η ≪ (log P)^{−1/2}`. -/
def SlowMellinWeight : Prop :=
  ∃ f : ℝ → ℂ, (∀ k : ℕ, ContDiff ℝ k f) ∧ HasCompactSupport f ∧ tsupport f ⊆ Set.Ioi 0 ∧
    ∀ α C : ℝ, 0 < α → ∃ u : ℝ, C * Real.exp (-|u| ^ α) < ‖mellin f (1 + u * I)‖

end LeanFormalizations.Erdos385

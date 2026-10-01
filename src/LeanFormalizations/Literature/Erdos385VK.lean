/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Literature inputs below Vinogradov–Korobov (phases E2e, E3d)

Statements only, never `axiom`s; each faithful-or-weaker to its source.

* `RichertZetaGrowth`: Richert's bound for `ζ` near `σ = 1`, the analytic output of Vinogradov's
  mean value theorem.  `|ζ(σ + it)| ≤ A |t|^{B(1−σ)^{3/2}} (log |t|)^{2/3}` for `1/2 ≤ σ ≤ 1`,
  `|t| ≥ 3`.  Source: H.-E. Richert, Math. Ann. 169 (1967); explicit constants `A = 76.2`,
  `B = 4.45` in K. Ford, Proc. LMS 85 (2002), "Vinogradov's integral and bounds for the Riemann
  zeta function", Theorem 1.  Weaker than the source: unspecified `A, B`.  ⚠️ Constants and theorem
  number recalled, not re-opened (85%); the shape is textbook (Titchmarsh 2nd ed. §6.12 remarks).
  Phase E2e derives `Literature.VKZeroFreeLogDeriv` from it (Landau's method), which moves Theorem A's
  last hypothesis down to the exponential-sum layer.
* `DLVPStatement`: the de la Vallée Poussin prime number theorem,
  `ψ(x) = x + O(x exp(−c √(log x)))`.  Source: de la Vallée Poussin 1899; PNT+ names it `StrongPNT`
  (blueprint statement in `PrimeNumberTheoremAnd/StrongPNT.lean`, not yet proved there at this pin).
  Phase E3d uses it for the long-range average at the `exp((log Z)^{1/3})` scale.

No known-false controls yet: the natural mistranscriptions (dropping `σ ≤ 1`, weakening the
exponent) are either still true or open problems, so they cannot serve as provable controls.
-/

open Complex Filter Asymptotics
open scoped Chebyshev

namespace LeanFormalizations.Literature

/-- **Richert's growth bound** (Ford 2002 Thm 1 with unspecified constants). -/
def RichertZetaGrowth : Prop :=
  ∃ A B : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 3 ≤ |t| →
    ‖riemannZeta (σ + t * I)‖ ≤
      A * |t| ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log |t| ^ ((2 : ℝ) / 3)

/-- **PNT with the de la Vallée Poussin error term** (PNT+ `StrongPNT`, blueprint). -/
def DLVPStatement : Prop :=
  ∃ c > 0, (ψ - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x))

end LeanFormalizations.Literature

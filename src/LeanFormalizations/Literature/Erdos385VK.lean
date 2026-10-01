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

* `NearOneZeroDensity` (phase E9): zero density near `σ = 1`,
  `N(σ, T) ≪ T^{B(1−σ)^{3/2}} (log T)^C` for `1/2 ≤ σ ≤ 1`.  Source: H. L. Montgomery, *Topics in
  Multiplicative Number Theory*, LNM 227 (1971), Ch. 12 (Halász–Turán method fed by Richert's bound;
  constant `B = 1000`, `C = 14` as recalled); A. Ivić, *The Riemann Zeta-Function* (1985), Ch. 11
  (`B ≈ 58`).  Weaker than the sources: unspecified `B, C`, and zeros counted without multiplicity
  (`Set.ncard`).  ⚠️ Theorem numbers and constants recalled, not re-opened (75%); the shape
  `T^{B(1−σ)^{3/2}}` is the textbook near-1 density.
* `ShortIntervalPrimesLower` (phase E9): primes in `[y, y + y^θ]` for some fixed `θ < 1`, with the
  expected count up to a factor `2`.  Source: A. E. Ingham, Q. J. Math. 8 (1937) (`θ > 5/8`);
  M. N. Huxley, Invent. Math. 15 (1972) (`θ > 7/12`).  Weaker: unspecified `θ < 1`, a lower bound
  with factor `1/2`.

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

/-- **Zero density near `σ = 1`** (Montgomery 1971 Ch. 12; Ivić 1985 Ch. 11), unspecified
constants, zeros counted without multiplicity. -/
def NearOneZeroDensity : Prop :=
  ∃ B C : ℝ, ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 3 ≤ T →
    ({ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T}.ncard : ℝ) ≤
      C * T ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log T ^ C

/-- **Primes in short intervals** (Ingham 1937, Huxley 1972), as a lower bound with an unspecified
exponent `θ < 1`. -/
def ShortIntervalPrimesLower : Prop :=
  ∃ e : ℝ, e < 1 ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    y ^ e / (2 * Real.log y) ≤
      ((Nat.primeCounting ⌊y + y ^ e⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊)

end LeanFormalizations.Literature

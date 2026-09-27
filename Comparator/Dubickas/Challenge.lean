/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Comparator.Dubickas.Support.Pisot

/-!
# Dubickas (2022), Theorem 1 - comparator CHALLENGE (the trusted audit surface)

A. Dubickas, *Transcendency of some constants related to integer sequences of polynomial
iterations*, Ramanujan J. **57** (2022), 569–581, doi:10.1007/s11139-021-00428-5.

This file imports *only* Mathlib (via `Support/Pisot.lean`, which states the two hypotheses
and the Pisot notion - read it too).  `Solution.lean` must prove *these exact statements*;
`comparator` checks every declaration below is identical in the solution, replays the proofs
through the Lean kernel and `nanoda`, and allows only `propext`, `Quot.sound`, `Classical.choice`.

**Read the hypotheses.**  The theorems are *conditional* on two results Dubickas proves in the
same paper and that are not formalized here:
* `Dubickas2022` - his Lemma 6 (from Corvaja–Zannier 2004, the `p`-adic subspace theorem).
* `Dubickas2022PisotGap` - his Lemma 8 (from Smyth, Mignotte and Baker's linear forms in logs).
Both are stated below as `Prop` definitions and taken as hypotheses, never as axioms.

The project definitions on this surface are the Pisot notion, the two hypotheses, the five
integer sequences (each a two-line recursion), and the two "limit exists and is transcendental"
predicates.  `Transcendental ℚ x` is Mathlib's `¬ IsAlgebraic ℚ x`.
-/

set_option warningAsError false


namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature

/-- **Dubickas (2022), Theorem 2 for monic quadratics.** -/
theorem transcendental_growth_of_monic_quadratic (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) (a₁ a₂ : ℤ) (x : ℕ → ℤ)
    (hx : ∀ n, x (n + 1) = x n ^ 2 + a₁ * x n + a₂) (hinf : Tendsto x atTop atTop)
    (h17 : a₁ ^ 2 - 2 * a₁ - 4 * a₂ ≠ 0) (h18 : a₁ ^ 2 - 2 * a₁ - 4 * a₂ ≠ 8) :
    ∃ α : ℝ, Tendsto (fun n ↦ (x n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) atTop (𝓝 α) ∧
      Transcendental ℚ α := sorry

/-- `1, 2, 5, 26, 677, …` - A003095 without its leading `0`. -/
def kappaSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 => kappaSeq n ^ 2 + 1

/-- `2, 3, 8, 63, 3968, …` - A003096. -/
def zetaSeq : ℕ → ℤ
  | 0 => 2
  | n + 1 => zetaSeq n ^ 2 - 1

/-- `2, 3, 7, 43, 1807, …` - Sylvester's sequence, A000058. -/
def sylvester : ℕ → ℤ
  | 0 => 2
  | n + 1 => sylvester n ^ 2 - sylvester n + 1

/-- `1, 3, 13, 183, …` - A002065 without its leading `0`. -/
def etaSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 => etaSeq n ^ 2 + etaSeq n + 1

/-- `1, 4, 25, 676, …` - A004019 without its leading `0`. -/
def tauSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 => tauSeq n ^ 2 + 2 * tauSeq n + 1

/-- `lim x_n^(1/2ⁿ)` exists and is transcendental. -/
def HasTranscendentalGrowth (x : ℕ → ℤ) : Prop :=
  ∃ α : ℝ, Tendsto (fun n ↦ (x n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) atTop (𝓝 α) ∧ Transcendental ℚ α

/-- **Dubickas (2022), Theorem 1: κ, ζ, γ, η, τ are all transcendental.** -/
theorem theorem1 (hD : Dubickas2022) (hG : Dubickas2022PisotGap) :
    HasTranscendentalGrowth kappaSeq ∧ HasTranscendentalGrowth zetaSeq ∧
      HasTranscendentalGrowth sylvester ∧ HasTranscendentalGrowth etaSeq ∧
      HasTranscendentalGrowth tauSeq := sorry

/-- `lim x_n^(1/2^(n+1))` (the OEIS normalisation, `= √α`) exists and is transcendental. -/
def HasTranscendentalHalfGrowth (x : ℕ → ℤ) : Prop :=
  ∃ c : ℝ, Tendsto (fun n ↦ (x n : ℝ) ^ ((1 : ℝ) / 2 ^ (n + 1))) atTop (𝓝 c) ∧
    Transcendental ℚ c

/-- **OEIS A076949, A077124, A076393 (Vardi's constant) are transcendental.** -/
theorem oeis_constants (hD : Dubickas2022) (hG : Dubickas2022PisotGap) :
    HasTranscendentalHalfGrowth kappaSeq ∧ HasTranscendentalHalfGrowth zetaSeq ∧
      HasTranscendentalHalfGrowth sylvester := sorry

/-- The sequences are the advertised ones (checked by the kernel here, not by the solution). -/
example : (List.range 5).map kappaSeq = [1, 2, 5, 26, 677] ∧
    (List.range 5).map zetaSeq = [2, 3, 8, 63, 3968] ∧
    (List.range 5).map sylvester = [2, 3, 7, 43, 1807] ∧
    (List.range 4).map etaSeq = [1, 3, 13, 183] ∧
    (List.range 4).map tauSeq = [1, 4, 25, 676] := by decide

end LeanFormalizations.Transcendence.Dubickas

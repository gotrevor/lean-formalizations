/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Assembly

/-!
# Erdős #385 power saving: MR16 Lemma 14 with a frequency mask (phase E9b)

`mr16_masked`: `mr16_core` for `Φ − 𝓕⁻(1_E F)`, where `E = {ξ : 2πξ ∈ Eₜ}` and `Eₜ` is a finite
union of closed intervals inside `T₀ ≤ |t|` (the near-1 large-value frequencies).  The right side
loses the frequencies of `Eₜ`: the middle integral and the dyadic block integrals run over
`t ∉ Eₜ` only.

Proof plan (85%): rerun `mr16_core` with `Pmid' = 𝓕⁻(1_{mid∖E} F)` and
`Phh' = Φ − 𝓕⁻(1_{all ∪ E} F)` in place of `Pmid`, `Phh`; `Plo` is unchanged because `Eₜ` avoids
`|t| < T₀`.  The inputs carry over: `integral_winDif_mid_le` needs only `‖G‖ ≤ 4` and a.e.
continuity of the masked indicator (the frontier of `mid ∖ E` is finite), and
`integral_norm_sub_proj` needs only a measurable set with integrable masked transform; the tail
bound `integral_tail_le` is applied to `|Â|² 1_{Eₜᶜ}`.
-/

open MeasureTheory Complex Set Filter
open scoped FourierTransform

noncomputable section

namespace Erdos385.Parseval

open LeanFormalizations.Literature

/-- The `ξ`-set of a `t`-set (`t = 2πξ`). -/
def tSet (Et : Set ℝ) : Set ℝ := {ξ | 2 * Real.pi * ξ ∈ Et}

/-- **Masked MR16 Lemma 14.** -/
theorem mr16_masked {a : ℕ → ℂ} {X T₀ h₁ h₂ : ℝ} (hX : 2 ≤ X) (hT₀ : 1 ≤ T₀) (hh₁ : 2 ≤ h₁)
    (h12 : h₁ ≤ h₂) (h2X : h₂ ≤ X / T₀ ^ 3) (ha1 : ∀ m, ‖a m‖ ≤ 1)
    (hsupp : ∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0)
    (S : Finset ℝ) (r : ℝ) (hr : 0 ≤ r) (hS : ∀ s ∈ S, T₀ + r ≤ |s|) {B : ℝ}
    (hB : ∀ T : ℝ, X / (2 * h₁) ≤ T →
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ ⋃ s ∈ S, Icc (s - r) (s + r),
          ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B) :
    (1 / X) * ∫ x in Ioc X (2 * X),
        ‖winDif (fun u ↦ Phi a ⌊4 * X⌋₊ u - 𝓕⁻ ((tSet (⋃ s ∈ S, Icc (s - r) (s + r))).indicator
          fun ξ ↦ LSeries a (sArg ξ) / sArg ξ) u) h₁ h₂ x‖ ^ 2 ≤
      500 * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁} \ ⋃ s ∈ S, Icc (s - r) (s + r),
        ‖LSeries a (1 + t * I)‖ ^ 2) + B) := by
  sorry

end Erdos385.Parseval

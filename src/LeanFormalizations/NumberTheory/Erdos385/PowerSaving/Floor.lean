/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Landau
import LeanFormalizations.NumberTheory.Erdos385.RateVK.General

/-!
# Erdős #385 power saving: the VK floor for the short prime sum (phase E9b)

`primePFloor_of_richert`: `|P(1+it)| ≤ K / exp((log Z)^{1/4})` for
`exp((log Z)^{1/4}) ≤ |t| ≤ 8X`, from Richert's bound via `vkZeroFreeLogDeriv_of_richert`,
`smoothPrimeSumVK_of_VKZ` and `Gen.primeP_small` at `a = 1/4`, `κ = 1`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter Complex LeanFormalizations.Literature

/-- The VK floor for `P` at height `≥ exp((log Z)^{1/4})`. -/
def PrimePFloor (δ : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Admissible δ g → ∃ K : ℝ, ∀ᶠ Z : ℝ in atTop, ∀ t : ℝ,
    Real.exp (Real.log Z ^ (1 / 4 : ℝ)) ≤ |t| → |t| ≤ 8 * paramX δ Z →
      ‖primeP g Z (1 + t * I)‖ ≤ K / Real.exp (Real.log Z ^ (1 / 4 : ℝ))

theorem primePFloor_of_richert (h : RichertZetaGrowth) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    PrimePFloor δ := by
  intro g hg
  haveI : Fact ((0 : ℝ) < 1 / 4) := ⟨by norm_num⟩
  haveI : Fact ((1 / 4 : ℝ) < 1 / 3) := ⟨by norm_num⟩
  obtain ⟨K, hK⟩ := Gen.primeP_small (a := 1 / 4)
    (smoothPrimeSumVK_of_VKZ (vkZeroFreeLogDeriv_of_richert h)) hδ hδ' one_pos le_rfl hg
  refine ⟨K, ?_⟩
  filter_upwards [hK] with Z hZ t h1 h2
  have e : Gen.paramT0 (1 / 4) 1 Z = Real.exp (Real.log Z ^ (1 / 4 : ℝ)) := by
    simp [Gen.paramT0]
  have := hZ t (by rw [e]; exact h1) h2
  rwa [e] at this

end LeanFormalizations.Erdos385

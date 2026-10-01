/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Landau
import LeanFormalizations.NumberTheory.Erdos385.PNTFromVK

/-!
# Erdős #385: Theorem A with the sharp rate, from Richert's growth bound alone

Chain: `RichertZetaGrowth` (Vinogradov's mean value theorem, analytic form)
→ `VKZeroFreeLogDeriv` (`Landau.lean`, Landau's method)
→ `DLVPStatement` (`PNTFromVK.lean`)
→ `almost_all_F385_rate_of_VK` (`RateVK.lean`, with `MR16Lemma14`, `MontgomeryVaughanMVT`,
`MediumPNTStatement` proved in `ShortSumParseval.lean` and `Discharge.lean`).
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **Theorem A with the sharp rate**: for `δ ∈ (0, 1/4)` and `ε > 0`,
`#{n ≤ X : F(n) < n + (1 − δ)√n} ≪ X exp(−(log X)^{1/3−ε})`, assuming only Richert's bound. -/
theorem almost_all_F385_rate_of_richert (h : RichertZetaGrowth) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 / 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * X * Real.exp (-(Real.log X ^ ((1 : ℝ) / 3 - ε))) :=
  almost_all_F385_rate_of_VK (vkZeroFreeLogDeriv_of_richert h) hδ hδ' ε hε

end LeanFormalizations.Erdos385

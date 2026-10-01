/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll

/-!
# Erdős #385: a rate for the almost-all theorem (phase E3c)

One frozen statement, `almost_all_F385_rate`: under the same four literature inputs as
`almost_all_F385`, for each `δ ∈ (0, 1/4)`,
`#{n ≤ X : F(n) < n + (1 − δ)√n} ≤ C X exp(−c (log X)^{1/10})`.

The exponent `1/10` is what the E3 pieces give as they stand: `variance_small` saves
`exp(−(κ/2)(log Z)^{1/10})`, inherited from `MediumPNTStatement`.  The source argument
(`DOOR-ALMOSTALL-ERDOS-385.md`, check (3)) gives `1/3 − ε` once the long-range average uses
Vinogradov–Korobov strength; that is a later phase, not this one.

## Route (85%; every ingredient is already proved in `AlmostAll.lean`)

1. Fix `g` from `exists_admissible`, then `κ := min κ₀ 1` and `c₁` from `longAverage_lower`,
   and `C` from `variance_small h1 h2 (smoothPrimeSumVK_of_VKZ h3) h4` (copy the opening of
   `almost_all_F385`).
2. Per window: `card_badWindow_le` with `μ = c₁ δ / log² Z` gives, eventually in `Z`,
   `#badWindow δ Z ≤ 2 paramX δ Z · C exp(−(κ/2) L^{1/10}) · L⁴ / (c₁δ)²` with `L = log Z`,
   hence `≤ C' Z exp(−(κ/4) L^{1/10})` for `Z ≥ Z₀` (absorb `L⁴`, and `paramX δ Z ≤ 2Z`).
3. Cover: the windows `[Z + paramH δ Z, (1 + δ/2) Z]` at `Z_k = Z₀ (1 + δ/4)^k` overlap
   (because `paramH δ Z = o(Z)`) and cover every `n ≥ N₀`.  Reuse the covering lemma inside
   `tendsto_density_zero_of_windows` if it is exposed; otherwise prove the covering directly.
4. Sum: windows with `Z_k ≤ √X` contribute at most `√X + O(1)` in total (crude count).  Windows
   with `√X < Z_k ≤ X` have `log Z_k ≥ (log X)/2`, so each is
   `≤ C' Z_k exp(−(κ/4) 2^{−1/10} (log X)^{1/10})`, and `Σ_{Z_k ≤ X} Z_k ≤ (4/δ + 1) X`
   (geometric).  Take `c = (κ/4) 2^{−1/10}/2` so that `√X ≤ X exp(−c (log X)^{1/10})` for
   large `X`.
5. Small `X` (below the eventual thresholds): the count is `≤ X + 1`, and
   `exp(−c (log X)^{1/10})` is bounded below on a bounded range; enlarge `C`.

If step 3 stalls, state the covering as a NAMED sub-lemma with a disclosed hole plus an English
paragraph and a confidence; that is an acceptable finish.

Frozen: this statement, every statement in `AlmostAll.lean`, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter LeanFormalizations.Literature

/-- **Theorem A with a rate** (exponent `1/10`, from `MediumPNT`). -/
theorem almost_all_F385_rate (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT)
    (h3 : VKZeroFreeLogDeriv) (h4 : MediumPNTStatement) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * X * Real.exp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by
  sorry

end LeanFormalizations.Erdos385

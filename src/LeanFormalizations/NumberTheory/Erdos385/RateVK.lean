/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.Rate
import LeanFormalizations.NumberTheory.Erdos385.Headline

/-!
# Erdős #385: the sharp rate `exp(−(log X)^{1/3−ε})` (phase E3d)

One frozen statement, `almost_all_F385_rate_VK`: from Vinogradov–Korobov and the de la Vallée
Poussin PNT, for each `δ ∈ (0, 1/4)` and `ε > 0`,
`#{n ≤ X : F(n) < n + (1 − δ)√n} ≤ C X exp(−(log X)^{1/3 − ε})`.
This is the rate the source argument gives (`DOOR-ALMOSTALL-ERDOS-385.md`, check (3), 80%), and it is
the limit of the method: the only saving is the VK pointwise bound for a prime sum of length `√X`.

## Route (75%)

E3's pieces are tuned to `MediumPNTStatement` (saving `exp(−(κ/2)(log Z)^{1/10})`).  Re-run them
with the scale `T₀ = exp((log Z)^{1/3})`, `h₂ = X/T₀³`, and the three discharged inputs
(`Erdos385.mr16Lemma14_holds`, `montgomeryVaughanMVT_holds`, `mediumPNTStatement_holds` are proved;
use them directly):

1. **Long average** (replaces `longAverage_lower`'s use of MediumPNT).  The `h₂`-averages of the
   witness coefficients are `≥ c₁ δ / log² Z`: it needs primes `q` in intervals of length
   `≍ √Z exp(−3(log Z)^{1/3})` at height `√Z`, and `DLVPStatement` gives error
   `√Z exp(−c √(log √Z))`, which is `o` of that length because `√(log Z) ≫ (log Z)^{1/3}`.
   State a `longAverage_lower_DLVP` mirroring `longAverage_lower` with the new `paramH2`.
2. **Variance** (replaces `variance_small`'s parameter choice).  The three terms of MR16 Lemma 14:
   `1/T₀ = exp(−(log Z)^{1/3})`; the middle range `≤ sup_{T₀ ≤ |t| ≤ 2Z} |P(1+it)|² · ∫|Q|²` with
   `SmoothPrimeSumVK` (from `smoothPrimeSumVK_of_VKZ`) at `P = √Z`, `T = max(√Z, 2|t|)`, giving
   `|P(1+it)| ≪ T₀^{−B} + exp(−(log Z)^{1/3−ε/2}/3)` (Mellin decay for small `|t|`, VK otherwise),
   and MVT for `Q`; the tail as in E3.  So the variance is `≪ exp(−(log Z)^{1/3−ε/2}/4)`.
3. **Per window**: `card_badWindow_le` with `μ = c₁δ/log² Z` gives
   `#badWindow ≤ C Z (log Z)⁴ exp(−(log Z)^{1/3−ε/2}/4)`.
4. **Sum over windows**: `card_le_of_windows` (`Rate.lean`) and the split at `√X`, exactly as in
   `almost_all_F385_rate`; absorb `(log)^4` and the constant `1/4` into the `ε/2` slack.

If E3's lemmas hard-wire `MediumPNTStatement` or the `1/10` scale, add parametrised copies rather
than editing frozen statements.  If a step stalls, state it as a NAMED sub-lemma with a disclosed
hole plus an English paragraph and a confidence; that is an acceptable finish.

Frozen: this statement, every statement in `AlmostAll.lean`/`Rate.lean`, and everything in
`Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Real LeanFormalizations.Literature

/-- **Theorem A with the sharp rate** `exp(−(log X)^{1/3−ε})`. -/
theorem almost_all_F385_rate_VK (h3 : VKZeroFreeLogDeriv) (h5 : DLVPStatement) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * X * Real.exp (-(Real.log X ^ ((1 : ℝ) / 3 - ε))) := by
  sorry

end LeanFormalizations.Erdos385

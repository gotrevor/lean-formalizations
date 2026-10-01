/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.RateVK

/-!
# Erdős #385: the de la Vallée Poussin PNT from Vinogradov–Korobov (phase E3e)

Two frozen statements:
* `dlvpStatement_of_VK : VKZeroFreeLogDeriv → DLVPStatement`;
* `almost_all_F385_rate_of_VK`: the sharp rate of `almost_all_F385_rate_VK` with `VKZeroFreeLogDeriv`
  as the only hypothesis (one line from the first).

The VK region is much wider than de la Vallée Poussin's, so this is a weakening of the standard VK
prime number theorem `ψ(x) − x ≪ x exp(−c (log x)^{3/5} (log log x)^{−1/5})`.

## Route (70%): smooth explicit formula at a height `T < P`, then sandwich

`SmoothPrimeSumVK` (E3) requires `P ≤ T`, which caps its saving at `exp(−(log P)^{1/3−ε})`, too weak
here.  Re-run its proof with a free height `T`:
1. **Smooth weights.**  For `η ∈ (0, 1/4)`, take `f_η^±` smooth, `0 ≤ f ≤ 1`, with
   `1_{[1/2+η, 1−η]} ≤ f^- ≤ 1_{[1/2,1]} ≤ f^+ ≤ 1_{[1/2−η, 1+η]}`, so
   `Σ Λ(n) f^-(n/x) ≤ ψ(x) − ψ(x/2) ≤ Σ Λ(n) f^+(n/x)`, and `mellin f^± (1) = 1/2 + O(η)`.
   Mellin decay uniform in `η`: `|f̃(σ+it)| ≪_B (η |t|)^{−B}` for `|t| ≥ 1` (integrate by parts `B`
   times; `mellin_strip_decay` tracks the constants, check its uniformity in `f`).
2. **Contour shift at height `T`.**  `smoothTwist_eq_vertical`, `smoothTwist_sub_main_eq`,
   `vertical_integral_bound` with `t = 0`: shift from `Re s = 2` to the VK line
   `σ_T = 1 − c₀/((log T)^{2/3}(log log T)^{1/3})` for `|Im s| ≤ T`, using `zetaH_extends` and the
   `C₀ log T` bound; the parts `|Im s| > T` cost `x · Σ (ηT)^{−B}`-type tails.  Error:
   `x^{σ_T} · log T · ∫_{|t|≤T} |f̃| + x (ηT)^{−B} ≪ x exp(−c₀ log x/((log T)^{2/3}(log log T)^{1/3})) (log T)² + x (ηT)^{−B}`.
3. **Choose** `η = exp(−2c√(log x))`, `T = exp(4c√(log x))/η`, so `log T ≍ √(log x)` and
   `log x/(log T)^{2/3+} ≫ (log x)^{2/3−} ≫ √(log x)`; every error term is `≪ x exp(−c√(log x))`
   for a small `c`.
4. **Dyadic sum.**  `ψ(x) − x = Σ_k [ψ(x/2^k) − ψ(x/2^{k+1}) − x/2^{k+1}] + O(√x)`, each block
   bounded by step 3 (blocks below `√x` trivially).  Repackage as `(ψ − id) =O[atTop] …`.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Real LeanFormalizations.Literature

/-- **de la Vallée Poussin's PNT from the Vinogradov–Korobov region.** -/
theorem dlvpStatement_of_VK (h : VKZeroFreeLogDeriv) : DLVPStatement := by
  sorry

/-- **Theorem A with the sharp rate, modulo Vinogradov–Korobov only.** -/
theorem almost_all_F385_rate_of_VK (h3 : VKZeroFreeLogDeriv) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 / 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * X * Real.exp (-(Real.log X ^ ((1 : ℝ) / 3 - ε))) := by
  sorry

end LeanFormalizations.Erdos385

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.Endpoint
import LeanFormalizations.NumberTheory.Erdos385.BadCount
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Assembly

/-!
# Erdős #385: Theorem A with a power saving (phase E9b, new mathematics)

`RateVK.lean` proves `#{n ≤ X : F(n) < n + (1 − δ)√n} ≪ X exp(−(log X)^{1/3−ε})` and calls that
"the limit of the method: the only saving is the VK pointwise bound for a prime sum of length
`√X`".  It is the limit of a *pure mean-square* method.  Splitting the frequencies `t` by the
size of the short prime sum `P(1+it)` (`p ≍ √Z`), and treating the two parts differently, gives a
power saving:

* `almost_all_F385_powerSaving`: `#{n ≤ X : F(n) < n + (1 − δ)√n} ≪ X^{1−c}`, `c = c(δ) > 0`;
* `badCount_powerSaving`: `#{bad n ≤ X} ≪ X^{1−c}`, beating `BadCount.badCountExpBound_holds`
  (`X exp(−(log X)^{1/2−ε})`) and the `X^{1−o(1)}` ceiling of the conditioning framework
  (`DOOR-EXCEPTIONAL-ERDOS-385.md` §A2).

Inputs: `RichertZetaGrowth` (as in `Endpoint.lean`), `NearOneZeroDensity` (Montgomery 1971), and
`ShortIntervalPrimesLower` (Ingham/Huxley), all cited `Literature` Props.  This is the
multiplicative analogue of Montgomery–Vaughan's power-saving exceptional set for binary Goldbach:
the zeros near `σ = 1` are handled pointwise, everything else in mean square.  Unpublished for
#385 as far as we know (60%); the method is classical in spirit.  70% that the outline closes.

## Route

Keep E3's pipeline (`AlmostAll.lean`, `RateVK/General.lean`): witness coefficients `coeffA`,
`F(s) = P(s) Q(s)` with `P` the smooth prime sum at `√Z`, MR16 Lemma 14 (`mr16Lemma14_holds`),
the per-window count `card_badWindow_le`, the window sum `card_le_of_windows`.  Change three things.

1. **Scales.**  `T₀ = Z^{c₀}`, `h₂ = Z/T₀³`.  The long `h₂`-average still has size `≍ δ/log² Z`
   (`longAverage_lower`'s argument), now with primes `q` in intervals of relative length
   `Z^{−3c₀}` at height `≍ √Z`: that is `ShortIntervalPrimesLower` once `6c₀ ≤ 1 − θ`.
2. **Split the frequencies.**  Fix `η₀ > 0` small (from `NearOneLargeValues`).  Let
   `S_near = {t : T₀ ≤ |t| ≤ 2Z, |P(1+it) − main| > (√Z)^{1−η₀}}` (Λ-normalisation of
   `SmoothPrimeSumVK`) and `S_far` the rest of `T₀ ≤ |t| ≤ 2Z`.  Write the short-minus-long
   difference `D(x) = shortSum(x, h₁)/h₁ − shortSum(x, h₂)/h₂` as `D_near + D_far`, where
   `D_S` is the inverse Mellin–Plancherel transform of `F(1+it) K_x(t) 1_S(t)` (the identity behind
   `mr16Lemma14_holds`, restricted to a frequency set; state it as a named lemma).
   * **Far, mean square**: `(1/X)∫|D_far|² ≪ 1/T₀ + sup_{S_far}|P|² ∫|Q|² + tail
     ≪ Z^{−c₀} + Z^{−η₀}` by the definition of `S_far` and MVT for `Q` (`montgomeryVaughanMVT_holds`).
   * **Near, pointwise**: `|D_near(x)| ≤ ∫_{S_near} |P| |Q| |K| dt`, `S_near` bounded so the integral
     converges absolutely.  Cut `S_near` into levels `|P − main| ≈ (√Z)^{1−η}`, `η ∈ [η_min, η₀]`
     dyadic.  Each level is covered by `≤ 2 C T^{Bη^{3/2}} log^C T` unit intervals
     (`NearOneLargeValues`, `T = 2Z`), and `η_min ≥ (log Z)^{−2/3−ε}` by `SmoothPrimeSumVK`.  So
     `|D_near(x)| ≪ Σ_η Z^{Bη^{3/2} − η/2} log^C Z ≪ exp(−(log Z)^{1/3−ε}) log^{C+1} Z`, which is
     `o(δ/log² Z)` once `η₀ ≤ 1/(16B²)`, for **every** `x`.
3. **Count.**  A bad window has `|D(x)| ≥ μ = c₁δ/log² Z`, hence `|D_far(x)| ≥ μ/2`; Chebyshev on
   the far mean square gives `#badWindow ≪ Z (log Z)^4 Z^{−min(c₀, η₀)}`; sum windows as before.

`badCount_powerSaving` follows from the headline at `δ = 1/8` (a bad `n` has
`F n ≤ n < n + (7/8)√n`).

`NearOneLargeValues` is the one place zeros enter.  It follows from `NearOneZeroDensity` by the
local explicit formula: a large value of the smooth prime sum at `t` forces a zero
`ρ = β + iγ` with `|γ − t| ≤ (log T)²` and `β ≥ 1 − η − O(log log T/log P)` (Landau's local lemma
`Landau.local_landau` for `ζ'/ζ` in the disc, plus a contour shift as in `PNTFromVK/`).  It is
planted as `nearOneLargeValues_of_density` (80%).

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Complex LeanFormalizations.Literature

/-- **Large values of a smooth prime sum near `σ = 1` are rare**: `1`-separated heights
`t ∈ [3, T]` where `Σ Λ(n) n^{−it} f(n/P)` deviates from its main term by `≥ P^{1−η}` number
`≪ T^{Bη^{3/2}} (log T)^C`, for `η ≤ η₀` and `P ≤ T ≤ P⁴`.  The Dirichlet-polynomial form of
`NearOneZeroDensity`. -/
def NearOneLargeValues : Prop :=
  ∀ f : ℝ → ℂ, (∀ k : ℕ, ContDiff ℝ k f) → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
    ∃ B C η₀ : ℝ, 0 < η₀ ∧ ∀ P T η : ℝ, 2 ≤ P → 3 ≤ T → P ≤ T → T ≤ P ^ 4 → 0 < η → η ≤ η₀ →
      ∀ S : Finset ℝ, (∀ t ∈ S, 3 ≤ |t| ∧ |t| ≤ T) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ S, P ^ (1 - η) ≤
          ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) *
              f (n / P)) - mellin f (1 - t * I) * (P : ℂ) ^ (1 - t * I)‖) →
        (S.card : ℝ) ≤ C * T ^ (B * η ^ ((3 : ℝ) / 2)) * Real.log T ^ C

/-- Zeros to large values (local explicit formula; 80%, see the header). -/
theorem nearOneLargeValues_of_density (h1 : RichertZetaGrowth) (h2 : NearOneZeroDensity) :
    NearOneLargeValues := by
  sorry

/-- **The per-window power saving** (the analytic crux: steps 1–3 of the header, the near/far
frequency split).  Global count from it: `almost_all_of_badWindowPowerSaving`.  70%. -/
theorem badWindowPowerSaving_of_lit (h1 : RichertZetaGrowth) (h2 : NearOneZeroDensity)
    (h3 : ShortIntervalPrimesLower) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    BadWindowPowerSaving δ := by
  sorry

/-- **Theorem A with a power saving.** -/
theorem almost_all_F385_powerSaving (h1 : RichertZetaGrowth) (h2 : NearOneZeroDensity)
    (h3 : ShortIntervalPrimesLower) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c C : ℝ, 0 < c ∧ ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * (X : ℝ) ^ (1 - c) :=
  almost_all_of_badWindowPowerSaving hδ hδ' (badWindowPowerSaving_of_lit h1 h2 h3 hδ hδ')

/-- **The bad set has a power saving.** -/
theorem badCount_powerSaving (h1 : RichertZetaGrowth) (h2 : NearOneZeroDensity)
    (h3 : ShortIntervalPrimesLower) :
    ∃ c C : ℝ, 0 < c ∧ ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ) ≤ C * (X : ℝ) ^ (1 - c) := by
  obtain ⟨c, C, hc, hC⟩ := almost_all_F385_powerSaving h1 h2 h3 (δ := 1 / 8) (by norm_num)
    (by norm_num)
  refine ⟨c, C, hc, fun X hX => le_trans ?_ (hC X hX)⟩
  have hsub : {n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n} ⊆
      {n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - 1 / 8) * Real.sqrt n} := by
    rintro n ⟨hnX, hn5, hb⟩
    refine ⟨hnX, ?_⟩
    unfold Bad at hb
    have : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
    have : (F n : ℝ) ≤ n := by exact_mod_cast hb
    nlinarith
  exact_mod_cast Set.ncard_le_ncard hsub
    ((Set.finite_Iic X).subset fun n hn => hn.1)

end LeanFormalizations.Erdos385

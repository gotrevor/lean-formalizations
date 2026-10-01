/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385AlmostAll
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.Headline
import LeanFormalizations.NumberTheory.Erdos385.Landau.ZeroFree

/-!
# Erdős #385: Vinogradov–Korobov from Richert's growth bound (phase E2e)

Two frozen statements:
* `vkZeroFreeLogDeriv_of_richert : RichertZetaGrowth → VKZeroFreeLogDeriv`;
* `almost_all_F385_of_richert : RichertZetaGrowth → AlmostAllF385` (one line from the first and
  `almost_all_F385_of_VK`).

## Route: Landau's method (Titchmarsh 2nd ed. Thms 3.10 and 3.11; 70% it closes in budget)

Write `L = log |t|`, `θ(t) = (log log |t| / log |t|)^{2/3}`, `φ(t) = log log |t|` (for `|t|` large).

1. **Growth on a disc.**  From `RichertZetaGrowth`: for `1 − θ ≤ σ ≤ 1` and `|t| ≥ t₁`,
   `log |ζ(σ+it)| ≤ B θ^{3/2} L + (2/3) log L + log A ≤ C φ(t)`.  For `σ ≥ 1` use
   `|ζ(σ+it)| ≤ ζ`-bound on `σ ≥ 1` (e.g. from `σ = 1` by Phragmén–Lindelöf, or the elementary
   `|ζ(s)| ≪ log |t|` on `σ ≥ 1`, `|t| ≥ 2`, which is in mathlib or PNT+ `ZetaBounds`).
2. **Borel–Carathéodory → log-derivative.**  Centre `s₀ = 1 + θ + it₀`, radius `r ≍ θ`.  `ζ` has no
   zeros on `σ > 1` and `|ζ(s₀)| ≥ ζ(2(1+θ))/ζ(1+θ) ≫ θ`, so `log |ζ(s)/ζ(s₀)| ≤ C φ` on the disc.
   Mathlib `Mathlib/Analysis/Complex/BorelCaratheodory.lean`; PNT+ `StrongPNT.lean` has the
   derivative and Blaschke/zero-counting forms (`BorelCaratheodoryDeriv`, `ZerosBound`,
   `FinalBound`, `LogOfAnalyticFunction`; a grep suggests these are sorry-free at this pin, so confirm with `#print axioms` before relying on one; ⚠️ `ZeroInequality`,
   `DeltaRange`, `LogDerivZetaUniformLogSquaredBoundStrip`, `LogDerivZetaLogSquaredBoundSmallt`,
   `I2NewBound`, `I3NewBound` carry `sorry` there, so do not use those).  Output: for `s` within
   `r/2` of `s₀`, `ζ'/ζ(s) = Σ_{|ρ − s₀| ≤ r/2} 1/(s − ρ) + O(φ/θ)`.
3. **Zero-free region.**  The 3-4-1 inequality `3 Re(−ζ'/ζ)(σ) + 4 Re(−ζ'/ζ)(σ+it) +
   Re(−ζ'/ζ)(σ+2it) ≥ 0` with step 2 at heights `t` and `2t` and a zero `ρ = β + it` gives
   `β ≤ 1 − c θ/φ`, i.e. the region `σ ≥ 1 − c₀ / (L^{2/3} (log L)^{1/3})`.
4. **Log-derivative bound in the region.**  With no zeros within `r/2`, step 2 gives
   `|ζ'/ζ(s)| ≤ C φ/θ ≪ L^{2/3} (log L)^{1/3} ≤ C₀ log T` for `|t| ≤ T`.
5. **Small `|y|`** (`|y| < t₁`): compactness.  `ζ'/ζ(s) + 1/(s−1)` is analytic on a neighbourhood
   of `{σ ≥ 1 − c₀', |y| ≤ t₁}` once `c₀'` is below the distance to the nearest zero (no zeros with
   `|Im ρ| < 14`, `ζ ≠ 0` on `[1/2, 1)` real: `riemannZeta_ne_zero_of_one_le_re` (name from memory, check) and the real-axis
   facts in mathlib / PNT+), so it is bounded there; shrink `c₀` to fit both ranges, using that the
   VK region at height `T ≥ 3` shrinks as `T` grows.
6. **Large `σ`**: for `σ ≥ 2`, `|ζ'/ζ| ≤ Σ Λ(n)/n²` and `|1/(s−1)| ≤ 1`.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: these statements and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature Complex

/-! ## Decomposition (lap 1)

`vkZeroFreeLogDeriv_of_richert` is reduced to two named halves:
* `vk_large_height` — Landau's method proper (steps 1–4, 6 of the route): for `|y| ≥ t₁`, the VK
  region at height `|y|` is zero-free and `|ζ'/ζ| ≪ log |y|` there.  THE CRUX.
* `vk_small_height` — step 5, compactness: below any fixed height `t₁`, a strip `σ ≥ 1 − c₂` is
  zero-free with `ζ'/ζ + 1/(s−1)` bounded.  Unconditional (no Richert).
The gluing (`vkW` antitone, constants) is proved below. -/

/-- **Large height (the crux; Landau's method).**  Steps 1–4 and 6 of the route: from Richert's
growth bound, Borel–Carathéodory (PNT+ `FinalBound`, sorry-free) gives the local zero-sum formula
for `ζ'/ζ` on discs of radius `≍ θ(t) = (log log t / log t)^{2/3}`, the 3-4-1 inequality gives the
zero-free region of width `≍ θ/log log t ≍ vkW t`, and the local formula with no zeros gives
`|ζ'/ζ| ≪ log log t / θ ≤ C log t`. -/
theorem vk_large_height (h : RichertZetaGrowth) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C₁ t₁ : ℝ, 3 ≤ t₁ ∧ ∀ σ y : ℝ, t₁ ≤ |y| → InVKRegion c₁ |y| σ →
      riemannZeta (σ + y * I) ≠ 0 ∧
        ‖deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I)‖ ≤ C₁ * Real.log |y| := by
  exact vk_large_height_of h

/-- **Small height (compactness).**  `ζ ≠ 0` on `Re s ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`),
`(s−1)ζ(s) → 1` at the pole, and continuity on the compact box `[1−c, 2] × [−t₁, t₁]`; for `σ ≥ 2`
the Dirichlet series bound. -/
theorem vk_small_height (t₁ : ℝ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ C₂ : ℝ, ∀ σ y : ℝ, |y| ≤ t₁ → 1 - c₂ ≤ σ →
      ((σ : ℂ) + y * I) ≠ 1 →
      riemannZeta (σ + y * I) ≠ 0 ∧
        ‖deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I) + 1 / (σ + y * I - 1)‖ ≤ C₂ := by
  obtain ⟨σ₀, hσ₀, hZ⟩ := ZetaNoZerosInBox t₁
  obtain ⟨U, hU, hB⟩ := riemannZetaLogDerivResidue
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  rw [bddAbove_def] at hB
  obtain ⟨B, hB⟩ := hB
  obtain ⟨C₃, hD3⟩ := logDeriv_zeta_dirichlet_bound
  set c₂ := (1 - σ₀) / 2 with hc₂
  have hc₂0 : 0 < c₂ := by rw [hc₂]; linarith
  set g : ℂ → ℂ := fun s => zLD s + 1 / (s - 1) with hg
  set K := (Set.Icc (1 - c₂) 2 ×ℂ Set.Icc (-t₁) t₁) ∩ {s | r ≤ ‖s - 1‖} with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hzK : ∀ s ∈ K, s ≠ 1 ∧ riemannZeta s ≠ 0 := by
    intro s hs
    have h1 : s ≠ 1 := by
      intro h; have := hs.2; simp [h] at this; linarith
    refine ⟨h1, ?_⟩
    have := hZ s.im (abs_le.mpr ⟨hs.1.2.1, hs.1.2.2⟩) s.re (by have := hs.1.1.1; linarith)
    rwa [Complex.re_add_im] at this
  have hgc : ContinuousOn g K := by
    intro s hs
    obtain ⟨h1, h0⟩ := hzK s hs
    have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    have ha : AnalyticAt ℂ riemannZeta s := hd.analyticAt (isOpen_compl_singleton.mem_nhds h1)
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    apply ContinuousAt.continuousWithinAt
    exact (ha.deriv.continuousAt.div ha.continuousAt h0).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hsub)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hgc
  refine ⟨c₂, hc₂0, max (max M B) (2 + C₃), fun σ y hy hσ hs1 => ?_⟩
  refine ⟨hZ y (abs_le.mpr ⟨by linarith [neg_abs_le y, le_abs_self y], hy.trans' (le_abs_self y)⟩)
    σ (by linarith), ?_⟩
  set s : ℂ := σ + y * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  change ‖g s‖ ≤ _
  by_cases h2 : 2 < σ
  · have hb := hD3 σ y (by linarith)
    have hp : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have := Complex.abs_re_le_norm (s - 1)
      simp only [Complex.sub_re, hsre, Complex.one_re] at this
      rw [abs_of_pos (by linarith)] at this
      rw [div_le_one (by linarith)]; linarith
    have h1 : 1 / (σ - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    calc ‖g s‖ ≤ ‖zLD s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ 2 + C₃ := by linarith
      _ ≤ _ := le_max_right _ _
  · push Not at h2
    by_cases hr' : ‖s - 1‖ < r
    · have hmem : s ∈ U \ {1} := ⟨hball (by rwa [Metric.mem_ball, dist_eq_norm]), hs1⟩
      have hb := hB _ ⟨s, hmem, rfl⟩
      simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply] at hb
      have e : g s = -(-(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹) := by
        simp only [hg, zLD, one_div]; ring
      rw [e, norm_neg]
      exact hb.trans ((le_max_right M B).trans (le_max_left _ _))
    · push Not at hr'
      have hK' : s ∈ K := ⟨⟨⟨by rw [hsre]; linarith, by rw [hsre]; exact h2⟩,
        ⟨by rw [hsim]; linarith [neg_abs_le y], by rw [hsim]; linarith [le_abs_self y]⟩⟩, hr'⟩
      exact (hM s hK').trans ((le_max_left M B).trans (le_max_left _ _))

/-- **Vinogradov–Korobov with a log-derivative bound, from Richert's growth bound** (Landau). -/
theorem vkZeroFreeLogDeriv_of_richert (h : RichertZetaGrowth) : VKZeroFreeLogDeriv := by
  obtain ⟨c₁, hc₁, C₁, t₁, ht₁, hL⟩ := vk_large_height h
  obtain ⟨c₂, hc₂, C₂, hS⟩ := vk_small_height t₁
  have hw3 := vkW_pos (le_refl (3 : ℝ))
  refine ⟨min c₁ (c₂ / vkW 3), lt_min hc₁ (div_pos hc₂ hw3), max C₁ 0 + 1 + max C₂ 0,
    fun T σ y hT hσ hy hs1 => ?_⟩
  rw [inVKRegion_iff] at hσ
  have hlogT : 1 ≤ Real.log T :=
    (one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hT)).le
  have hwT := vkW_pos hT
  by_cases hyt : t₁ ≤ |y|
  · have hy3 : 3 ≤ |y| := ht₁.trans hyt
    have hreg : InVKRegion c₁ |y| σ := by
      rw [inVKRegion_iff]
      have := vkW_anti hy3 hy
      have : min c₁ (c₂ / vkW 3) * vkW T ≤ c₁ * vkW |y| :=
        mul_le_mul (min_le_left _ _) this hwT.le hc₁.le
      linarith
    obtain ⟨hne, hb⟩ := hL σ y hyt hreg
    refine ⟨hne, ?_⟩
    have hlogy : Real.log |y| ≤ Real.log T := Real.log_le_log (by linarith) hy
    have hlogy0 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
    have hpole : ‖1 / ((σ : ℂ) + y * I - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have : |y| ≤ ‖(σ : ℂ) + y * I - 1‖ := by
        have := Complex.abs_im_le_norm ((σ : ℂ) + y * I - 1)
        simpa using this
      exact (div_le_one (by linarith)).mpr (by linarith)
    calc _ ≤ ‖deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I)‖
          + ‖1 / ((σ : ℂ) + y * I - 1)‖ := norm_add_le _ _
      _ ≤ max C₁ 0 * Real.log T + 1 := by
          have : C₁ * Real.log |y| ≤ max C₁ 0 * Real.log T :=
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogy0).trans
              (mul_le_mul_of_nonneg_left hlogy (le_max_right _ _))
          linarith
      _ ≤ (max C₁ 0 + 1 + max C₂ 0) * Real.log T := by
          have := le_max_right C₂ 0
          nlinarith
  · push Not at hyt
    have hσ2 : 1 - c₂ ≤ σ := by
      have h1 : vkW T ≤ vkW 3 := vkW_anti (le_refl _) hT
      have h2 : min c₁ (c₂ / vkW 3) * vkW T ≤ c₂ / vkW 3 * vkW 3 :=
        mul_le_mul (min_le_right _ _) h1 hwT.le (div_pos hc₂ hw3).le
      rw [div_mul_cancel₀ _ hw3.ne'] at h2
      linarith
    obtain ⟨hne, hb⟩ := hS σ y hyt.le hσ2 hs1
    refine ⟨hne, hb.trans ?_⟩
    have := le_max_left C₂ 0
    have := le_max_right C₁ 0
    have := le_max_right C₂ 0
    nlinarith

/-- **Theorem A from Richert's bound.** -/
theorem almost_all_F385_of_richert (h : RichertZetaGrowth) : AlmostAllF385 :=
  almost_all_F385_of_VK (vkZeroFreeLogDeriv_of_richert h)

end LeanFormalizations.Erdos385

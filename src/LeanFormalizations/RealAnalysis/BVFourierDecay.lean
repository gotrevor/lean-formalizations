/-
# Route (b) toward `prelim_decay_2`: half-period shift + L¹-translation-by-TV

`prelim_decay_2` (`‖𝓕 ψ u‖ ≤ V(ψ)/(2π|u|)` for ψ integrable + bounded variation) is **still `sorry`
upstream** in `PrimeNumberTheoremAnd` (now our dependency, `Wiener.lean:323`) and **absent from mathlib**.
The blueprint route is Lebesgue–Stieltjes integration-by-parts (sharp `2π|u|`), which mathlib lacks.

This file develops — and now fully PROVES — the **self-contained route (b)** (weaker constant `4|u|`,
no BV-IBP):

  ‖𝓕 f u‖ ≤ ½ ∫ ‖f t − f(t + 1/(2u))‖ dt        -- (b1) Fourier half-period shift     [PROVEN]
            ≤ ½ · |1/(2u)| · V(f)  =  V(f)/(4|u|) -- (b2) L¹-translation-by-total-variation [PROVEN]

**COMPLETE & axiom-clean** (`#print axioms prelim_decay_2_route_b = [propext, Classical.choice,
Quot.sound]`). Both analytic cruxes are machine-checked:
  • (b1) write `𝓕` in the `exp(↑r·I)` phase form (norm 1), shift by `1/(2u)`, pick up `𝐞(−½) = −1`
    so the shifted integral is `−𝓕 f u`, add the two reps, take norms.
  • (b2) via the **monotone variation function** `W(t) = V(f on (−∞,t])`: pointwise
    `‖f t − f(t+h)‖ ≤ W(t+h) − W(t)` (superadditivity + `edist_le`), then the finite-window telescoping
    `∫_{−N}^{N}(W(·+k) − W) = ∫_N^{N+k}W − ∫_{−N}^{−N+k}W ≤ k·V` with a monotone-convergence limit —
    **no variation/Stieltjes measure needed** (mathlib-absent for signed BV).

A complete, mathlib-only, axiom-clean BV-Fourier decay bound (non-sharp constant `4|u|` vs the sharp
`2π|u|`). NOT a headline; dead code on the WeakPNT path (`weakPNT` is axiom-clean with the upstream
`prelim_decay` sorries present). Lives in `wip/` (outside the build); `src/` stays sorry-free.
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Real Filter
open scoped FourierTransform

namespace LeanFormalizations.RealAnalysis.BVFourierDecay

/-- **Pointwise variation bound (PROVEN).** For `f` of bounded variation on `univ`, any two values differ
by at most the total variation: `‖f a − f b‖ ≤ V(f)`. Direct from `eVariationOn.edist_le`. -/
theorem norm_sub_le_eVariationOn_toReal {f : ℝ → ℂ} (hf : BoundedVariationOn f Set.univ) (a b : ℝ) :
    ‖f a - f b‖ ≤ (eVariationOn f Set.univ).toReal := by
  have h : edist (f a) (f b) ≤ eVariationOn f Set.univ :=
    eVariationOn.edist_le f (Set.mem_univ a) (Set.mem_univ b)
  rw [edist_dist, dist_eq_norm] at h
  have h2 := ENNReal.toReal_mono hf h
  rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h2

/-- **Helper toward (b1) — PROVEN.** The Fourier character at `−½` is `−1` (`𝐞(−½) = e^{−πi} = −1`).
This is the algebraic heart of the half-period shift: it turns the shifted Fourier integral into `−𝓕 f u`. -/
theorem fourierChar_neg_half : ((Real.fourierChar (-(1 / 2 : ℝ))) : ℂ) = -1 := by
  rw [Real.fourierChar_apply, show ((2 : ℝ) * π * (-(1 / 2))) = -π from by ring,
    Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **(b1) Fourier half-period shift (PROVEN).**
`‖𝓕 f u‖ ≤ ½ ∫ ‖f t − f(t + 1/(2u))‖ dt`.

Proof sketch: substitute `t ↦ t + 1/(2u)` in `𝓕 f u = ∫ 𝐞(−tu) f t dt`; since `𝐞(−½) = e^{−πi} = −1`,
the shifted integral equals `−𝓕 f u`, so `2·𝓕 f u = ∫ 𝐞(−tu)(f t − f(t+1/(2u))) dt`. Take norms
(`‖𝐞(·)‖ = 1`, `norm_integral_le_integral_norm`). Needs `MeasureTheory.integral_add_right_eq_self` for the
translation invariance of `volume` and the `Real.fourierChar` value at `−½`. -/
theorem norm_fourierIntegral_le_half_integral_norm_sub_shift
    (f : ℝ → ℂ) (hf : Integrable f) (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 f u‖ ≤ (1 / 2) * ∫ t, ‖f t - f (t + 1 / (2 * u))‖ := by
  set h : ℝ := 1 / (2 * u) with hh
  -- the Fourier phase, written in the `Complex.exp (↑r * I)` form (so it lives in ℂ, norm 1)
  set c : ℝ → ℂ := fun v => Complex.exp ((↑(-2 * π * (v * u)) : ℝ) * Complex.I) with hc
  have hcnorm : ∀ v, ‖c v‖ = 1 := fun v => Complex.norm_exp_ofReal_mul_I _
  have hcm : AEStronglyMeasurable c volume := by
    apply Continuous.aestronglyMeasurable; fun_prop
  have hcbd : ∀ᵐ v, ‖c v‖ ≤ 1 := Filter.Eventually.of_forall fun v => le_of_eq (hcnorm v)
  have hfsh : Integrable (fun v => f (v + h)) := hf.comp_add_right h
  have hI1 : Integrable (fun v => c v * f v) := hf.bdd_mul hcm hcbd
  have hI2 : Integrable (fun v => c v * f (v + h)) := hfsh.bdd_mul hcm hcbd
  -- (i) `𝓕 f u = ∫ c v · f v`  (unfold `fourier_eq'`, real inner `⟪v,u⟫ = v*u`)
  have hFT : 𝓕 f u = ∫ v, c v * f v := by
    rw [fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, hc, inner_apply]
  -- the phase satisfies `c (v + h) = - c v`  (since `𝐞(-½) = e^{-πi} = -1`)
  have hcs : ∀ v, c (v + h) = - c v := by
    intro v
    simp only [hc]
    have hreal : (-2 * π * ((v + h) * u) : ℝ) = (-2 * π * (v * u)) + (-π) := by
      rw [hh]; field_simp; ring
    rw [hreal, Complex.ofReal_add, add_mul, Complex.exp_add,
      show ((↑(-π : ℝ)) : ℂ) * Complex.I = -(↑π * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg, mul_one]
  -- (ii) translation invariance ⇒ `𝓕 f u = - ∫ c v · f (v + h)`
  have hshift : 𝓕 f u = - ∫ v, c v * f (v + h) := by
    rw [hFT, ← MeasureTheory.integral_add_right_eq_self (fun v => c v * f v) h, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hcs v, neg_mul]
  -- (iii) add the two reps ⇒ `2 · 𝓕 f u = ∫ c v · (f v − f (v+h))`
  have hrep : (2 : ℂ) * 𝓕 f u = ∫ v, c v * (f v - f (v + h)) := by
    have hsum : (2 : ℂ) * 𝓕 f u = (∫ v, c v * f v) - (∫ v, c v * f (v + h)) := by
      rw [two_mul]; nth_rewrite 1 [hFT]; nth_rewrite 1 [hshift]; ring
    rw [hsum, ← integral_sub hI1 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [mul_sub]
  -- (iv) take norms: `‖c v‖ = 1` ⇒ `2‖𝓕 f u‖ ≤ ∫ ‖f v − f(v+h)‖`
  have hnb : ‖(2 : ℂ) * 𝓕 f u‖ ≤ ∫ v, ‖f v - f (v + h)‖ := by
    rw [hrep]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [norm_mul, hcnorm, one_mul]
  have h2norm : ‖(2 : ℂ) * 𝓕 f u‖ = 2 * ‖𝓕 f u‖ := by rw [norm_mul]; norm_num
  rw [h2norm] at hnb
  linarith [hnb]

/-! ### (b2) L¹-translation by total variation, via the monotone variation function

The key to making this mathlib-reachable (avoiding the mathlib-absent *signed* variation measure)
is the **monotone variation function** `W(t) = V(f on (-∞,t])`, whose Stieltjes measure mathlib
*does* have. Below: `W` is monotone, and the pointwise bound `‖f t − f(t+h)‖ ≤ W(t+h) − W(t)`
(for `h ≥ 0`) is PROVEN from `eVariationOn.add_le_union` + `eVariationOn.edist_le`. (b2) then reduces
to the single monotone Stieltjes–Fubini fact `∫(W(·+h) − W) ≤ h·V`. -/

/-- The **monotone variation function** `W(t) = V(f on (-∞, t])`. -/
noncomputable def varFn (f : ℝ → ℂ) (t : ℝ) : ℝ := (eVariationOn f (Set.Iic t)).toReal

/-- `eVariationOn` on any subset is finite when `f` has bounded variation on `univ`. -/
theorem evar_ne_top {f : ℝ → ℂ} (hbv : BoundedVariationOn f Set.univ) (s : Set ℝ) :
    eVariationOn f s ≠ ⊤ :=
  ne_top_of_le_ne_top hbv (eVariationOn.mono f (Set.subset_univ s))

/-- The variation function is monotone. -/
theorem varFn_mono {f : ℝ → ℂ} (hbv : BoundedVariationOn f Set.univ) : Monotone (varFn f) := by
  intro s t hst
  exact ENNReal.toReal_mono (evar_ne_top hbv _) (eVariationOn.mono f (Set.Iic_subset_Iic.mpr hst))

/-- The variation function is nonnegative. -/
theorem varFn_nonneg (f : ℝ → ℂ) (t : ℝ) : 0 ≤ varFn f t := ENNReal.toReal_nonneg

/-- The variation function is bounded by the total variation `V`. -/
theorem varFn_le_V {f : ℝ → ℂ} (hbv : BoundedVariationOn f Set.univ) (t : ℝ) :
    varFn f t ≤ (eVariationOn f Set.univ).toReal :=
  ENNReal.toReal_mono (evar_ne_top hbv _) (eVariationOn.mono f (Set.subset_univ _))

/-- **Pointwise bound (PROVEN).** `‖f t − f(t+h)‖ ≤ W(t+h) − W(t)` for `h ≥ 0`. Superadditivity of
the variation over `Iic t ⊎ Icc t (t+h) = Iic (t+h)` (`eVariationOn.add_le_union`) plus the two-point
lower bound `‖f t − f(t+h)‖ ≤ V(Icc t (t+h))` (`eVariationOn.edist_le`). -/
theorem norm_sub_le_varFn_sub {f : ℝ → ℂ} (hbv : BoundedVariationOn f Set.univ)
    (t h : ℝ) (hh : 0 ≤ h) :
    ‖f t - f (t + h)‖ ≤ varFn f (t + h) - varFn f t := by
  have hunion : Set.Iic t ∪ Set.Icc t (t + h) = Set.Iic (t + h) := by
    ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]; constructor
    · rintro (hx | ⟨_, hx⟩) <;> linarith
    · intro hx; rcases le_total x t with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, hx⟩
  have hsuper : eVariationOn f (Set.Iic t) + eVariationOn f (Set.Icc t (t+h))
      ≤ eVariationOn f (Set.Iic (t+h)) := by
    calc eVariationOn f (Set.Iic t) + eVariationOn f (Set.Icc t (t+h))
        ≤ eVariationOn f (Set.Iic t ∪ Set.Icc t (t+h)) :=
          eVariationOn.add_le_union f (fun x hx y hy => le_trans hx hy.1)
      _ = eVariationOn f (Set.Iic (t+h)) := by rw [hunion]
  have hedist : edist (f t) (f (t + h)) ≤ eVariationOn f (Set.Icc t (t+h)) :=
    eVariationOn.edist_le f (by simp [hh]) (by simp [hh])
  have hfin1 := evar_ne_top hbv (Set.Iic t)
  have hfin2 := evar_ne_top hbv (Set.Icc t (t+h))
  have hfin3 := evar_ne_top hbv (Set.Iic (t+h))
  have key : (eVariationOn f (Set.Iic t)).toReal + (eVariationOn f (Set.Icc t (t+h))).toReal
      ≤ (eVariationOn f (Set.Iic (t+h))).toReal := by
    rw [← ENNReal.toReal_add hfin1 hfin2]; exact ENNReal.toReal_mono hfin3 hsuper
  have hnorm : ‖f t - f (t + h)‖ ≤ (eVariationOn f (Set.Icc t (t+h))).toReal := by
    rw [← dist_eq_norm]
    have := ENNReal.toReal_mono hfin2 hedist
    rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at this
  simp only [varFn]; linarith

/-- **Analytic core of (b2) (PROVEN).** For `k ≥ 0` the monotone variation function's
translate-difference `t ↦ W(t+k) − W(t)` is integrable, with `∫(W(·+k) − W) ≤ k·V`.

Proved by an **elementary route that needs no variation/Stieltjes measure** (mathlib-absent for
signed BV): the finite-window integral telescopes,
`∫_{−N}^{N}(W(t+k) − W(t)) dt = ∫_{N}^{N+k} W − ∫_{−N}^{−N+k} W ≤ k·V − 0`
(substitution `intervalIntegral.integral_comp_add_right`, oriented interval additivity, then
`W ≤ V` and `W ≥ 0`); the bound is uniform in `N`, so the nonneg integrand is integrable
(`integrable_of_intervalIntegral_norm_bounded`) and `∫_ℝ = lim_N ∫_{−N}^{N} ≤ k·V`
(`intervalIntegral_tendsto_integral` + `le_of_tendsto`). -/
theorem integrable_and_integral_varFn_diff_le
    (f : ℝ → ℂ) (hbv : BoundedVariationOn f Set.univ) (k : ℝ) (hk : 0 ≤ k) :
    Integrable (fun t => varFn f (t + k) - varFn f t) ∧
      (∫ t, (varFn f (t + k) - varFn f t)) ≤ k * (eVariationOn f Set.univ).toReal := by
  set V := (eVariationOn f Set.univ).toReal with hV
  have hmono := varFn_mono hbv
  have hmonosh : Monotone (fun t => varFn f (t + k)) := hmono.comp (monotone_id.add_const k)
  have hii : ∀ a b : ℝ, IntervalIntegrable (varFn f) volume a b := fun a b => hmono.intervalIntegrable
  have hiish : ∀ a b : ℝ, IntervalIntegrable (fun t => varFn f (t + k)) volume a b :=
    fun a b => hmonosh.intervalIntegrable
  have hgnn : ∀ t, 0 ≤ varFn f (t + k) - varFn f t := by
    intro t; have := hmono (le_add_of_nonneg_right hk : t ≤ t + k); linarith
  -- finite-window bound, uniform in N (oriented interval additivity ⇒ no size constraint on N)
  have hfin : ∀ N : ℝ, (∫ t in (-N)..N, (varFn f (t + k) - varFn f t)) ≤ k * V := by
    intro N
    rw [intervalIntegral.integral_sub (hiish _ _) (hii _ _),
      intervalIntegral.integral_comp_add_right (varFn f) k]
    have e1 : (∫ t in (-N)..N, varFn f t)
        = (∫ t in (-N)..(-N+k), varFn f t) + (∫ t in (-N+k)..N, varFn f t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
    have e2 : (∫ t in (-N+k)..(N+k), varFn f t)
        = (∫ t in (-N+k)..N, varFn f t) + (∫ t in N..(N+k), varFn f t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
    rw [e1, e2]
    have hhi : (∫ t in N..(N+k), varFn f t) ≤ k * V := by
      calc (∫ t in N..(N+k), varFn f t) ≤ ∫ _t in N..(N+k), V :=
            intervalIntegral.integral_mono_on (by linarith) (hii _ _)
              intervalIntegrable_const (fun x _ => varFn_le_V hbv x)
        _ = k * V := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hlo : 0 ≤ (∫ t in (-N)..(-N+k), varFn f t) :=
      intervalIntegral.integral_nonneg (by linarith) (fun x _ => varFn_nonneg f x)
    linarith
  have hint : Integrable (fun t => varFn f (t + k) - varFn f t) := by
    apply integrable_of_intervalIntegral_norm_bounded (k * V)
      (a := fun x : ℝ => -x) (b := fun x : ℝ => x) (l := atTop)
    · intro x; exact ((hiish (-x) x).sub (hii (-x) x)).1
    · exact tendsto_neg_atTop_atBot
    · exact tendsto_id
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N _
      rw [intervalIntegral.integral_congr (g := fun t => varFn f (t + k) - varFn f t)
        (fun x _ => Real.norm_of_nonneg (hgnn x))]
      exact hfin N
  refine ⟨hint, ?_⟩
  have htend := intervalIntegral_tendsto_integral hint
    (a := fun x : ℝ => -x) (b := fun x : ℝ => x) tendsto_neg_atTop_atBot tendsto_id
  exact le_of_tendsto htend (Eventually.of_forall fun N => hfin N)

/-- **(b2) L¹-translation by total variation.** `∫ ‖f t − f(t+h)‖ dt ≤ |h| · V(f)`, for ALL `h`.
Reduces to the nonneg case via the proven pointwise bound + `integral_mono_of_nonneg`, with the
analytic core isolated in `integrable_and_integral_varFn_diff_le`; the `h < 0` case folds back to
`h ≥ 0` by translation invariance (`integral_add_right_eq_self`) and `norm_sub_rev`. -/
theorem integral_norm_sub_translate_le
    (f : ℝ → ℂ) (hf : Integrable f) (hbv : BoundedVariationOn f Set.univ) (h : ℝ) :
    (∫ t, ‖f t - f (t + h)‖) ≤ |h| * (eVariationOn f Set.univ).toReal := by
  -- the nonneg-shift bound, valid for any `k ≥ 0`
  have hpos : ∀ k : ℝ, 0 ≤ k →
      (∫ t, ‖f t - f (t + k)‖) ≤ k * (eVariationOn f Set.univ).toReal := by
    intro k hk
    obtain ⟨hRint, hRle⟩ := integrable_and_integral_varFn_diff_le f hbv k hk
    exact le_trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg _) hRint
      (Filter.Eventually.of_forall fun t => norm_sub_le_varFn_sub hbv t k hk)) hRle
  rcases le_total 0 h with hh | hh
  · rw [abs_of_nonneg hh]; exact hpos h hh
  · -- h ≤ 0 : substitute `t ↦ t − h` and use `norm_sub_rev`
    have hh' : 0 ≤ -h := by linarith
    have heq : (∫ t, ‖f t - f (t + h)‖) = ∫ t, ‖f t - f (t + -h)‖ := by
      rw [← MeasureTheory.integral_add_right_eq_self (fun t => ‖f t - f (t + h)‖) (-h)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [show u + -h + h = u by ring, norm_sub_rev]
    rw [heq, abs_of_nonpos hh]
    exact hpos (-h) hh'

/-- **Assembly (PROVEN — fully, axiom-clean).** Route-(b) decay bound `‖𝓕 f u‖ ≤ V(f)/(4|u|)` — the
weaker (non-sharp) form of `prelim_decay_2`. Both analytic cruxes (b1)+(b2) above are now machine-checked,
so this is a complete mathlib-only proof (`#print axioms = [propext, Classical.choice, Quot.sound]`). -/
theorem prelim_decay_2_route_b
    (f : ℝ → ℂ) (hf : Integrable f) (hbv : BoundedVariationOn f Set.univ) (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 f u‖ ≤ (eVariationOn f Set.univ).toReal / (4 * |u|) := by
  set V := (eVariationOn f Set.univ).toReal with hV
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
  have hb1 := norm_fourierIntegral_le_half_integral_norm_sub_shift f hf u hu
  have hb2 := integral_norm_sub_translate_le f hf hbv (1 / (2 * u))
  have habs : |1 / (2 * u)| = 1 / (2 * |u|) := by
    rw [abs_div, abs_one, abs_mul]; norm_num
  -- chain: ‖𝓕 f u‖ ≤ ½·(∫‖f t − f(t+1/(2u))‖) ≤ ½·(|1/(2u)|·V) = V/(4|u|)
  have hstep : (1 / 2) * (∫ t, ‖f t - f (t + 1 / (2 * u))‖) ≤ V / (4 * |u|) := by
    have hu' : 0 < |u| := abs_pos.mpr hu
    calc (1 / 2) * (∫ t, ‖f t - f (t + 1 / (2 * u))‖)
        ≤ (1 / 2) * (|1 / (2 * u)| * V) := by
          exact mul_le_mul_of_nonneg_left hb2 (by norm_num)
      _ = V / (4 * |u|) := by
          rw [habs]; field_simp <;> ring
  exact hb1.trans hstep

end LeanFormalizations.RealAnalysis.BVFourierDecay

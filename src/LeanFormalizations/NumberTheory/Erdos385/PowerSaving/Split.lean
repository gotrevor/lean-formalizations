/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Assembly
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Window

/-!
# Erdős #385 power saving: the per-window bound from two analytic leaves (phase E9b)

`badWindowPowerSaving_of_leaves` proves `BadWindowPowerSaving δ` from

* `LongAveragePower δ`: the long average `S(x, H)/H`, `H = X/Z^{3c₀}`, is `≥ c₁δ/log² Z` on the
  window (header step 1; from `ShortIntervalPrimesLower`);
* `DifferenceSplit δ`: `D(x) = S(x,h₁)/h₁ − S(x,H)/H` is within `1/log³ Z` of a function `D_far`
  whose mean square over `(X, 2X]` is `≤ C Z^{−c}` (header step 2: `D − D_far = D_near` is the
  near-1 frequency part, bounded pointwise; `D_far` is controlled by MVT).

Both are quantified over every small `c₀`, so they can be used at a common `c₀`.
The count is `card_badWindow_le_of_split` with `G = D_far²`, `ν = μ²/4`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory LeanFormalizations.Literature

/-- The long length `H = X / Z^{3c₀}` (power-scale `h₂`). -/
noncomputable def powerH (c₀ δ Z : ℝ) : ℝ := paramX δ Z / Z ^ (3 * c₀)

/-- The difference `D(x) = S(x, h₁)/h₁ − S(x, H)/H`. -/
noncomputable def diffD (c₀ δ : ℝ) (g : ℝ → ℝ) (Z x : ℝ) : ℝ :=
  shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
    shortSum (coeffA δ g Z) x (powerH c₀ δ Z) / powerH c₀ δ Z

/-- Step 1 (long average at power scale). -/
def LongAveragePower (δ : ℝ) : Prop :=
  ∃ cmax : ℝ, 0 < cmax ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cmax → ∀ g : ℝ → ℝ, Admissible δ g →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ Z : ℝ in atTop, ∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z →
      c₁ * δ / Real.log Z ^ 2 ≤ shortSum (coeffA δ g Z) x (powerH c₀ δ Z) / powerH c₀ δ Z

/-- Step 2 (near/far split of the difference). -/
def DifferenceSplit (δ : ℝ) : Prop :=
  ∃ cmax : ℝ, 0 < cmax ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cmax → ∀ g : ℝ → ℝ, Admissible δ g →
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ Z : ℝ in atTop, ∃ Dfar : ℝ → ℝ,
      IntegrableOn (fun x => Dfar x ^ 2) (Set.Ioc (paramX δ Z) (2 * paramX δ Z)) ∧
      (∀ x, paramX δ Z < x → x ≤ 2 * paramX δ Z →
        |diffD c₀ δ g Z x - Dfar x| ≤ 1 / Real.log Z ^ 3) ∧
      ∫ x in (paramX δ Z)..(2 * paramX δ Z), Dfar x ^ 2 ≤ C * paramX δ Z * Z ^ (-c)

/-- `log⁴ Z ≤ Z^{c/2}` eventually. -/
theorem eventually_log_pow_le_rpow {c : ℝ} (hc : 0 < c) :
    ∀ᶠ Z : ℝ in atTop, Real.log Z ^ 4 ≤ Z ^ (c / 2) := by
  have := (isLittleO_log_rpow_atTop (show 0 < c / 8 by positivity))
  have h := this.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_ge_atTop 1] with Z hZ hZ1
  have hl : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg (by positivity), one_mul] at hZ
  calc Real.log Z ^ 4 ≤ (Z ^ (c / 8)) ^ 4 := pow_le_pow_left₀ hl hZ 4
    _ = Z ^ (c / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num; ring_nf

theorem badWindowPowerSaving_of_leaves {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hL : LongAveragePower δ) (hS : DifferenceSplit δ) : BadWindowPowerSaving δ := by
  obtain ⟨g, hg⟩ := exists_admissible hδ hδ'
  obtain ⟨m1, hm1, hL⟩ := hL
  obtain ⟨m2, hm2, hS⟩ := hS
  set c₀ := min m1 m2
  have hc₀ : 0 < c₀ := lt_min hm1 hm2
  obtain ⟨c₁, hc₁, hlong⟩ := hL c₀ hc₀ (min_le_left _ _) g hg
  obtain ⟨c, C, hc, hsplit⟩ := hS c₀ hc₀ (min_le_right _ _) g hg
  have hlogt : Tendsto (fun Z : ℝ => Real.log Z) atTop atTop := Real.tendsto_log_atTop
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.1 ((card_badWindow_le_of_split hδ hδ' hg).and
    (hlong.and (hsplit.and ((eventually_log_pow_le_rpow hc).and
      ((hlogt.eventually_ge_atTop (2 / (c₁ * δ))).and (eventually_gt_atTop 1))))))
  refine ⟨c / 2, by positivity, 4 * (|C| + 1) / (c₁ * δ) ^ 2, by positivity, max Z₁ 1,
    le_max_right _ _, fun Z hZ => ?_⟩
  obtain ⟨hcount, hl, ⟨Dfar, hint, hnear, hfar⟩, hlog4, hlogbig, hZ1⟩ :=
    hZ₁ Z ((le_max_left _ _).trans hZ)
  have hlZ : 0 < Real.log Z := Real.log_pos hZ1
  set μ := c₁ * δ / Real.log Z ^ 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hX0 : 0 < paramX δ Z := by unfold paramX; nlinarith
  have hXZ : paramX δ Z ≤ Z := by unfold paramX; nlinarith
  -- `1/log³ Z ≤ μ/2`
  have hsmall : 1 / Real.log Z ^ 3 ≤ μ / 2 := by
    rw [hμ, div_le_iff₀ (by positivity)]
    have : 2 / (c₁ * δ) * (c₁ * δ) = 2 := by field_simp
    have h2 : 2 ≤ Real.log Z * (c₁ * δ) := by
      have := mul_le_mul_of_nonneg_right hlogbig (show 0 ≤ c₁ * δ by positivity); linarith
    have e : c₁ * δ / Real.log Z ^ 2 / 2 * Real.log Z ^ 3 = Real.log Z * (c₁ * δ) / 2 := by
      field_simp
    rw [e]; linarith
  have hb := hcount (powerH c₀ δ Z) μ (μ ^ 2 / 4) (fun x => Dfar x ^ 2) hμ0
    (fun x => sq_nonneg _) hint hl (by
      intro x hx1 hx2 hD
      have hn := hnear x hx1 hx2
      unfold diffD at hn
      have h1 : μ / 2 ≤ |Dfar x| := by
        have := abs_sub_abs_le_abs_sub
          (shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
            shortSum (coeffA δ g Z) x (powerH c₀ δ Z) / powerH c₀ δ Z) (Dfar x)
        linarith
      have := pow_le_pow_left₀ (by positivity) h1 2
      rw [sq_abs] at this
      nlinarith)
  -- assemble
  have hZc : 0 < Z ^ (-c) := by positivity
  have hcard0 : (0 : ℝ) ≤ (badWindow δ Z).ncard := by positivity
  have hfar' : ∫ x in (paramX δ Z)..(2 * paramX δ Z), Dfar x ^ 2 ≤ (|C| + 1) * Z * Z ^ (-c) := by
    refine hfar.trans ?_
    have : C * paramX δ Z ≤ (|C| + 1) * Z := by
      have := le_abs_self C
      nlinarith [abs_nonneg C]
    exact mul_le_mul_of_nonneg_right this hZc.le
  have hkey : ((badWindow δ Z).ncard : ℝ) * (μ ^ 2 / 4) ≤ (|C| + 1) * Z * Z ^ (-c) :=
    hb.trans hfar'
  have hpow : Z * Z ^ (-c) * Real.log Z ^ 4 ≤ Z ^ (1 - c / 2) := by
    have e : Z ^ (1 - c / 2) = Z * Z ^ (-c) * Z ^ (c / 2) := by
      have hZ0 : 0 < Z := by linarith
      rw [show 1 - c / 2 = 1 + -c + c / 2 by ring, Real.rpow_add hZ0, Real.rpow_add hZ0,
        Real.rpow_one]
    rw [e]; exact mul_le_mul_of_nonneg_left hlog4 (by positivity)
  have hμ2 : μ ^ 2 / 4 = (c₁ * δ) ^ 2 / (4 * Real.log Z ^ 4) := by rw [hμ]; field_simp
  rw [hμ2] at hkey
  have hcd : 0 < (c₁ * δ) ^ 2 := by positivity
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hkey
  rw [show 4 * (|C| + 1) / (c₁ * δ) ^ 2 * Z ^ (1 - c / 2) =
    4 * (|C| + 1) * Z ^ (1 - c / 2) / (c₁ * δ) ^ 2 by ring, le_div_iff₀ hcd]
  have : (|C| + 1) * Z * Z ^ (-c) * (4 * Real.log Z ^ 4) ≤ 4 * (|C| + 1) * Z ^ (1 - c / 2) := by
    have := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4 * (|C| + 1) by positivity)
    linarith
  linarith

end LeanFormalizations.Erdos385

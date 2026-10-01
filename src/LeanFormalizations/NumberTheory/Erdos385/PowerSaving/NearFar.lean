/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Split
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Bridge

/-!
# Erdős #385 power saving: step 2 from a frequency-side input (phase E9b)

`differenceSplit_of_nearFar` proves `DifferenceSplit δ` from `NearFarInput δ`, a statement purely
about the Dirichlet series `A(s) = Σ coeffA(m) m^{−s}` on the line `σ = 1`: a finite set `S` of
heights `|s| ≥ T₀ + 1` (`T₀ = Z^{c₀}`) such that
* the near part is small in `L¹`: `∫_{nearSet S 1} |A(1+it)| dt ≤ 1/log³ Z`;
* off the near set, `A` has a power saving in mean square on the mid band
  `T₀ ≤ |t| ≤ X/h₁` and on every dyadic tail band (weighted as in `mr16_masked`).
The wiring is `Parseval.far_split` at `h₁ = paramH1`, `h₂ = powerH = X/T₀³`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex LeanFormalizations.Literature Erdos385.Parseval

/-- **Frequency-side input for step 2.**  Believed (65%): take `S` a maximal `1`-separated set of
heights `T₀ + 1 ≤ |t| ≤ 8X` where the short prime factor `P(1+it)` of `A = P Q` is
`≥ Z^{−η₀/2}`.  Near part: `NearOneLargeValues` levels plus the VK lower bound on `η`
(`SmoothPrimeSumVK`), `|Q| ≪ 1`.  Off the near set `|P| ≤ Z^{−η₀/2}` up to a derivative bound for
`P` on unit intervals, then the MVT for `Q` (`primeQ_meanSquare`) gives the mid and tail bands for
`T ≤ 8X`; for `T > 8X` the MVT for `A` itself gives `X/(h₁T)·(T/X)/log Z ≪ 1/h₁ ≪ Z^{−1/2}`. -/
def NearFarInput (δ : ℝ) : Prop :=
  ∃ cmax : ℝ, 0 < cmax ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cmax → ∀ g : ℝ → ℝ, Admissible δ g →
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ Z : ℝ in atTop, ∃ T₀ : ℝ, Z ^ c₀ / 2 ≤ T₀ ∧ T₀ ≤ Z ^ c₀ ∧
      ∃ S : Finset ℝ, (∀ s ∈ S, T₀ + 1 ≤ |s|) ∧
      (∫ t in nearSet S 1, ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖) ≤
        1 / Real.log Z ^ 3 ∧
      (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ paramX δ Z / paramH1 δ Z} \ nearSet S 1,
          ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2) ≤ C * Z ^ (-c) ∧
      ∀ T : ℝ, paramX δ Z / (2 * paramH1 δ Z) ≤ T →
        paramX δ Z / (paramH1 δ Z * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T} \ nearSet S 1,
          ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2 ≤ C * Z ^ (-c)

/-- Eventual parameter facts at power scale: `2 ≤ h₁ ≤ powerH = X/(Z^{c₀})³`. -/
theorem powerH_params {δ c₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hc₀ : 0 < c₀)
    (hc₀' : c₀ ≤ 1 / 12) :
    ∀ᶠ Z : ℝ in atTop, 2 ≤ paramX δ Z ∧ 2 ≤ paramH1 δ Z ∧ paramH1 δ Z ≤ powerH c₀ δ Z ∧
      powerH c₀ δ Z = paramX δ Z / (Z ^ c₀) ^ 3 ∧ 2 ≤ Z ^ c₀ ∧ 1 < Z := by
  filter_upwards [variance_params (κ := 1) hδ hδ' one_pos, eventually_ge_atTop (2 ^ 12),
    (tendsto_rpow_atTop hc₀).eventually_ge_atTop 2] with Z hv hZ hZc
  obtain ⟨hZ16, -, hX2, hH2, -, hH1hi, -⟩ := hv
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hpow : (Z ^ c₀) ^ 3 = Z ^ (3 * c₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]; ring_nf
  refine ⟨hX2, hH2, ?_, by rw [powerH, hpow], hZc, by linarith⟩
  -- `h₁ ≤ √Z ≤ X/Z^{1/4} ≤ X/Z^{3c₀}`
  have hR : Z ^ (3 * c₀) ≤ Z ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hR0 : 0 < Z ^ (3 * c₀) := by positivity
  set R := Z ^ ((1 : ℝ) / 4) with hRdef
  have hR4 : R ^ 4 = Z := by
    rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]; norm_num
  have hsq : √Z = R ^ 2 := by
    rw [← hR4, show R ^ 4 = (R ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hR8 : 8 ≤ R := by
    have : (2 : ℝ) ^ 12 = 8 ^ 4 := by norm_num
    rw [this] at hZ
    rw [← hR4] at hZ
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hZ
  have hsZ : δ * √Z / 8 ≤ √Z := by
    have : 0 ≤ √Z := Real.sqrt_nonneg _; nlinarith
  have hkey : √Z * R ≤ paramX δ Z := by
    unfold paramX
    rw [hsq, ← hR4]
    have h3 : 0 < R ^ 3 := by positivity
    have h4 := mul_le_mul_of_nonneg_left hR8 h3.le
    nlinarith
  unfold powerH
  rw [le_div_iff₀ hR0]
  calc paramH1 δ Z * Z ^ (3 * c₀) ≤ √Z * R :=
        mul_le_mul (hH1hi.trans hsZ) hR hR0.le (Real.sqrt_nonneg _)
    _ ≤ paramX δ Z := hkey

/-- **Step 2 from the frequency-side input** (pure wiring through `far_split`). -/
theorem differenceSplit_of_nearFar {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hN : NearFarInput δ) : DifferenceSplit δ := by
  obtain ⟨m, hm, hN⟩ := hN
  refine ⟨min m (1 / 12), lt_min hm (by norm_num), fun c₀ hc₀ hc₀m g hg => ?_⟩
  obtain ⟨c, C, hc, hev⟩ := hN c₀ hc₀ (hc₀m.trans (min_le_left _ _)) g hg
  set c' := min c c₀
  refine ⟨c', 500 * (2 + 2 * |C|), lt_min hc hc₀, ?_⟩
  filter_upwards [hev, powerH_params hδ hδ' hc₀ (hc₀m.trans (min_le_right _ _))] with Z hS hp
  obtain ⟨T₀, hT₀lo, hT₀hi, S, hSs, hnear, hmid, htail⟩ := hS
  obtain ⟨hX2, hH2, h12, hHeq, hT2, hZ1⟩ := hp
  have hT1 : 1 ≤ T₀ := by linarith
  have h2X : powerH c₀ δ Z ≤ paramX δ Z / T₀ ^ 3 := by
    rw [hHeq]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity)
      (pow_le_pow_left₀ (by linarith) hT₀hi 3)
  have hfacts := coeffA_facts hδ hδ' hZ1 hg
  obtain ⟨Dfar, hint, hD, hfar⟩ := far_split (a := coeffA δ g Z) (X := paramX δ Z)
    (T₀ := T₀) (h₁ := paramH1 δ Z) (h₂ := powerH c₀ δ Z) hX2 hT1 hH2 h12 h2X
    (fun m => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfacts m).1]
      linarith [(hfacts m).2.1])
    (fun m hm' => by
      by_contra hne
      have := (hfacts m).2.2 (by exact_mod_cast hne)
      have hX0 : 0 < paramX δ Z := by linarith
      rcases hm' with h | h <;> linarith [this.1, this.2])
    S 1 zero_le_one hSs htail
  refine ⟨Dfar, hint, fun x hx _ => (hD x (by linarith)).trans hnear, hfar.trans ?_⟩
  have hX0 : 0 < paramX δ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hZc : Z ^ (-c) ≤ Z ^ (-c') :=
    Real.rpow_le_rpow_of_exponent_le hZ1.le (by simp [c'])
  have hZc₀ : 1 / Z ^ c₀ ≤ Z ^ (-c') := by
    rw [one_div, ← Real.rpow_neg hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by simp [c'])
  have hT₀inv : 1 / T₀ ≤ 2 * (1 / Z ^ c₀) := by
    rw [one_div_le (by linarith) (by positivity)]
    have : 0 < Z ^ c₀ := by positivity
    field_simp; linarith
  have hpos : 0 ≤ Z ^ (-c) := by positivity
  have hCc : C * Z ^ (-c) ≤ |C| * Z ^ (-c') :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hpos).trans
      (mul_le_mul_of_nonneg_left hZc (abs_nonneg C))
  have : 1 / T₀ + C * Z ^ (-c) + C * Z ^ (-c) ≤ (2 + 2 * |C|) * Z ^ (-c') := by
    linarith
  calc paramX δ Z * (500 * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧
          |t| ≤ paramX δ Z / paramH1 δ Z} \ nearSet S 1,
          ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ^ 2) + C * Z ^ (-c)))
      ≤ paramX δ Z * (500 * ((2 + 2 * |C|) * Z ^ (-c'))) := by gcongr; linarith
    _ = 500 * (2 + 2 * |C|) * paramX δ Z * Z ^ (-c') := by ring

end LeanFormalizations.Erdos385

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Split
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.LongAverage
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Primes

/-!
# Erdős #385 power saving, step 1: the long average at power scale (phase E9b)

`longAveragePower_of_shortIntervalPrimes`: `ShortIntervalPrimesLower` (exponent `e < 1`) gives
`LongAveragePower δ` with `cmax = (1 − e⁺)/20`, via `primeCount_tile` (`K = 4`) and
`longAverage_core`.  With `s = √Z`: `h₂/(2√Z) ≍ s^{1−6c₀}` beats the tile length `(4s)^{e⁺}`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter LeanFormalizations.Literature

theorem primeCountAt_power {e y₀ δ c₀ : ℝ} (he : e < 1)
    (hS : ∀ y : ℝ, y₀ ≤ y → y ^ e / (2 * Real.log y) ≤
      ((Nat.primeCounting ⌊y + y ^ e⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊))
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ (1 - max e 0) / 20) :
    ∀ᶠ Z : ℝ in atTop, PrimeCountAt 4 Z (powerH c₀ δ Z) := by
  set E := max e 0 with hE
  have hE0 : 0 ≤ E := le_max_right _ _
  have hE1 : E < 1 := max_lt he one_pos
  set r := 1 - 6 * c₀ - E with hr
  have hr0 : 0 < r := by rw [hr]; nlinarith
  have hs : Tendsto (fun Z : ℝ => √Z) atTop atTop := Real.tendsto_sqrt_atTop
  have hsr : Tendsto (fun Z : ℝ => √Z ^ r) atTop atTop := (tendsto_rpow_atTop hr0).comp hs
  filter_upwards [hs.eventually_ge_atTop (2 * max y₀ 2), hs.eventually_ge_atTop 4,
    hsr.eventually_ge_atTop 64] with Z hZs hZ4 hZr
  intro y H hy1 hy2 hH1 hHy
  set s := √Z with hsdef
  have hs0 : 0 < s := by linarith
  have hZ : Z = s ^ 2 := by rw [hsdef, Real.sq_sqrt]; nlinarith [Real.sqrt_nonneg Z,
    Real.sqrt_eq_zero'.not.1 (by linarith : ¬ √Z = 0)]
  have hy₀ : y₀ ≤ y := by linarith [le_max_left y₀ 2]
  have hy2' : 2 ≤ y := by linarith [le_max_right y₀ 2]
  have hy1' : 1 ≤ y := by linarith
  -- tile bounds
  set L := (4 * s) ^ E with hL
  set m := (4 * s) ^ (min e 0) with hm
  have hm0 : 0 < m := by positivity
  have hmL : ∀ t, y ≤ t → t ≤ 2 * y → m ≤ t ^ e ∧ t ^ e ≤ L := by
    intro t ht1 ht2
    have ht1' : 1 ≤ t := by linarith
    have ht4 : t ≤ 4 * s := by linarith
    constructor
    · calc m ≤ t ^ (min e 0) := Real.rpow_le_rpow_of_nonpos (by linarith) ht4 (min_le_right _ _)
        _ ≤ t ^ e := Real.rpow_le_rpow_of_exponent_le ht1' (min_le_left _ _)
    · calc t ^ e ≤ t ^ E := Real.rpow_le_rpow_of_exponent_le ht1' (le_max_left _ _)
        _ ≤ L := Real.rpow_le_rpow (by linarith) ht4 hE0
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hH0 : 0 ≤ H := by
    refine le_trans (div_nonneg ?_ (by linarith)) hH1
    unfold powerH paramX
    exact div_nonneg (mul_nonneg (by linarith) hZ0) (by positivity)
  have htile := primeCount_tile hS hy₀ hy2' hH0 hHy hm0 hmL
  -- `2L ≤ h₂/(2√Z) ≤ H`
  have hpow : powerH c₀ δ Z / (2 * s) = (1 - δ / 2) / 2 * s ^ (1 - 6 * c₀) := by
    unfold powerH paramX
    rw [hZ, show (s ^ 2) ^ (3 * c₀) = s ^ (6 * c₀) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]; norm_num; ring_nf,
      show s ^ (1 - 6 * c₀) = s * s ^ (-(6 * c₀)) by
        rw [sub_eq_add_neg, Real.rpow_add hs0, Real.rpow_one],
      Real.rpow_neg hs0.le]
    field_simp
  have hL4 : L ≤ 4 * s ^ E := by
    rw [hL, Real.mul_rpow (by norm_num) hs0.le]
    gcongr
    calc (4 : ℝ) ^ E ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hE1.le
      _ = 4 := Real.rpow_one 4
  have hsplit : s ^ (1 - 6 * c₀) = s ^ r * s ^ E := by
    rw [← Real.rpow_add hs0, hr]; ring_nf
  have h2L : 2 * L ≤ H := by
    refine le_trans ?_ hH1
    rw [hpow, hsplit]
    have hsE : 0 < s ^ E := by positivity
    have : 64 * s ^ E ≤ s ^ r * s ^ E := mul_le_mul_of_nonneg_right hZr hsE.le
    nlinarith
  have hD : 0 < 2 * Real.log (2 * y) := by
    have := Real.log_pos (show (1 : ℝ) < 2 * y by linarith); linarith
  rw [card_primesIn (by linarith)]
  refine le_trans ?_ htile
  rw [div_le_div_iff₀ (by linarith) hD]
  nlinarith

theorem longAveragePower_of_shortIntervalPrimes (h3 : ShortIntervalPrimesLower) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) : LongAveragePower δ := by
  obtain ⟨e, he, y₀, hS⟩ := h3
  have hE1 : max e 0 < 1 := max_lt he one_pos
  refine ⟨(1 - max e 0) / 20, by linarith, fun c₀ hc₀ hc₀' g hg =>
    ⟨1 / (32 * 4 ^ 2), by norm_num, ?_⟩⟩
  have hT : Tendsto (fun Z : ℝ => Z ^ (3 * c₀)) atTop atTop := tendsto_rpow_atTop (by positivity)
  filter_upwards [primeCountAt_power he hS hδ hδ' hc₀ hc₀', eventually_ge_atTop 16,
    hT.eventually_ge_atTop (4 / δ)] with Z hP hZ hZT x hx1 hx2
  have hZ0 : 0 < Z := by linarith
  have hZT0 : 0 < Z ^ (3 * c₀) := by positivity
  have hh20 : 0 < powerH c₀ δ Z := by unfold powerH paramX; apply div_pos (by nlinarith) hZT0
  have hh2δ : powerH c₀ δ Z ≤ δ / 4 * Z := by
    unfold powerH paramX
    rw [div_le_iff₀ hZT0]
    have : 4 / δ * δ = 4 := by field_simp
    have := mul_le_mul_of_nonneg_left hZT (show 0 ≤ δ / 4 * Z by positivity)
    nlinarith
  exact longAverage_core hg hP (by norm_num) hδ hδ' hZ hh20 hh2δ hx1 hx2

end LeanFormalizations.Erdos385

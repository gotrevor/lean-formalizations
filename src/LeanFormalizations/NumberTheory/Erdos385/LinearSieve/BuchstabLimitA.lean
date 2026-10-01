/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.BuchstabBin

/-!
# The lower Buchstab inequality in the limit (phase E5, step 2) — PROVED

`buchstab_limit_a'`: `a(s') − ∫_s^{s'} b(t−1)/(t−1) ≤ a(s)` for `2 ≤ s ≤ s'`.
From `aLow_ge_bins` (finite Buchstab over a uniform partition, mesh `h`) and
`riemann_delay_le` (shifted upper Riemann sums of the monotone `b(u−1)/(u−1)` are
`≤ (1 + 3h/(s−1))(∫_s^{s'} + 2h·b(s'+1))`), then `h → 0`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve
open Filter Topology Finset Set

section Riemann
variable {f : ℝ → ℝ} (hf : MonotoneOn f (Ioi 0)) (hf0 : ∀ x, 0 < x → 0 ≤ f x)
include hf

lemma intervalIntegrable_delay {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => f (u - 1) / (u - 1)) MeasureTheory.volume a b := by
  have hm : MonotoneOn (fun u => f (u - 1)) (uIcc a b) := by
    intro x hx y hy hxy
    rw [uIcc_of_le hab] at hx hy
    exact hf (show (0:ℝ) < x - 1 by linarith [hx.1]) (show (0:ℝ) < y - 1 by linarith [hy.1])
      (by linarith)
  have hc : ContinuousOn (fun u : ℝ => (u - 1)⁻¹) (uIcc a b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le hab] at hx; linarith [hx.1]
  simpa [div_eq_mul_inv] using hm.intervalIntegrable.mul_continuousOn hc

include hf0 in
lemma integral_delay_ge {a h : ℝ} (ha : 1 < a) (hh : 0 ≤ h) :
    h * (f (a - 1) / (a + h - 1)) ≤ ∫ u in a..a + h, f (u - 1) / (u - 1) := by
  have hc : ∫ _ in a..a + h, f (a - 1) / (a + h - 1) = h * (f (a - 1) / (a + h - 1)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [← hc]
  refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    (intervalIntegrable_delay hf ha (by linarith)) fun u hu => ?_
  have h1 : 0 < a - 1 := by linarith
  have hu1 : 0 < u - 1 := by linarith [hu.1]
  have hfa := hf0 _ h1
  have hmono : f (a - 1) ≤ f (u - 1) := hf h1 hu1 (by linarith [hu.1])
  calc f (a - 1) / (a + h - 1) ≤ f (a - 1) / (u - 1) :=
        div_le_div_of_nonneg_left hfa hu1 (by linarith [hu.2])
    _ ≤ f (u - 1) / (u - 1) := div_le_div_of_nonneg_right hmono hu1.le

include hf0 in
/-- **Shifted upper Riemann sum** for the delay integrand `g(u) = f(u−1)/(u−1)`. -/
theorem riemann_delay_le {s s' : ℝ} (hs : 2 ≤ s) (hss' : s < s') {k : ℕ} (hk : 0 < k)
    (hh1 : (s' - s) / k ≤ 1) :
    ∑ i ∈ Finset.range k, f (s + (i + 2) * ((s' - s) / k) - 1) * ((s' - s) / k) /
      (s + i * ((s' - s) / k) - 1) ≤
    (1 + 3 * ((s' - s) / k) / (s - 1)) *
      ((∫ u in s..s', f (u - 1) / (u - 1)) + 2 * ((s' - s) / k) * f (s' + 1)) := by
  set h := (s' - s) / k with hhdef
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < h := div_pos (by linarith) hkr
  set t : ℕ → ℝ := fun i => s + i * h with ht
  have htk : t k = s' := by simp only [ht, hhdef]; field_simp; ring
  have htge : ∀ i : ℕ, s ≤ t i := fun i => by
    simp only [ht]; have : (0 : ℝ) ≤ i * h := by positivity
    linarith
  set c := 1 + 3 * h / (s - 1) with hc
  have hc0 : 0 ≤ c := by have : 0 < s - 1 := by linarith
                         positivity
  set g := fun u : ℝ => f (u - 1) / (u - 1) with hg
  have hg0 : ∀ u, 1 < u → 0 ≤ g u := fun u hu =>
    div_nonneg (hf0 _ (by linarith)) (by linarith)
  -- per-term
  have hterm : ∀ i ∈ Finset.range k, f (s + (i + 2) * h - 1) * h / (s + i * h - 1) ≤
      c * ∫ u in t (i + 2)..t (i + 3), g u := by
    intro i _
    have ht2 : t (i + 3) = t (i + 2) + h := by simp only [ht]; push_cast; ring
    have ht2' : t (i + 2) = s + (i + 2) * h := by simp only [ht]; push_cast; ring
    have hti := htge i
    have hti2 := htge (i + 2)
    rw [ht2]
    have hint := integral_delay_ge hf hf0 (a := t (i + 2)) (h := h) (by linarith) hpos.le
    rw [ht2'] at hint ⊢
    have hd : 0 < s + i * h - 1 := by simp only [ht] at hti; linarith
    have hd' : 0 < s + (i + 2) * h + h - 1 := by nlinarith
    have hF : 0 ≤ f (s + (i + 2) * h - 1) := hf0 _ (by nlinarith)
    have hratio : (s + (i + 2) * h + h - 1) ≤ c * (s + i * h - 1) := by
      have hsi : s - 1 ≤ s + i * h - 1 := by simp only [ht] at hti; linarith
      have h3 : 3 * h ≤ 3 * h * (s + i * h - 1) / (s - 1) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      have e : (1 + 3 * h / (s - 1)) * (s + i * h - 1) =
          (s + i * h - 1) + 3 * h * (s + i * h - 1) / (s - 1) := by ring
      rw [hc, e]; linarith
    calc f (s + (i + 2) * h - 1) * h / (s + i * h - 1)
        = c * (h * (f (s + (i + 2) * h - 1) / (c * (s + i * h - 1)))) := by
          have : 0 < c := by
            have : 0 < s - 1 := by linarith
            rw [hc]; positivity
          field_simp
      _ ≤ c * (h * (f (s + (i + 2) * h - 1) / (s + (i + 2) * h + h - 1))) := by
          gcongr
      _ ≤ c * ∫ u in s + (i + 2) * h..s + (i + 2) * h + h, g u :=
          mul_le_mul_of_nonneg_left hint hc0
  -- sum the integrals
  have hsum : ∑ i ∈ Finset.range k, ∫ u in t (i + 2)..t (i + 3), g u =
      ∫ u in t 2..t (k + 2), g u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := MeasureTheory.volume)
      (a := fun i => t (i + 2)) (n := k) fun i _ =>
        intervalIntegrable_delay hf (by linarith [htge (i + 2)])
          (by simp only [ht]; push_cast; nlinarith)
    simpa using this
  -- compare with [s, s'] plus the tail
  have hint_all : IntervalIntegrable g MeasureTheory.volume s (s' + 2 * h) :=
    intervalIntegrable_delay hf (by linarith) (by linarith)
  have hk2 : t (k + 2) = s' + 2 * h := by
    simp only [ht]; push_cast; rw [show s + (k + 2) * h = t k + 2 * h by simp only [ht]; ring, htk]
  have hmono_int : ∫ u in t 2..t (k + 2), g u ≤ ∫ u in s..s' + 2 * h, g u := by
    rw [hk2]
    refine intervalIntegral.integral_mono_interval (htge 2) (by simp only [ht]; push_cast; linarith)
      le_rfl ?_ hint_all
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact hg0 u (by linarith [hu.1])
  have hsplit : ∫ u in s..s' + 2 * h, g u = (∫ u in s..s', g u) + ∫ u in s'..s' + 2 * h, g u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_delay hf (by linarith) hss'.le)
      (intervalIntegrable_delay hf (by linarith) (by linarith))).symm
  have htail : ∫ u in s'..s' + 2 * h, g u ≤ 2 * h * f (s' + 1) := by
    have : ∫ _ in s'..s' + 2 * h, f (s' + 1) = 2 * h * f (s' + 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← this]
    refine intervalIntegral.integral_mono_on (by linarith)
      (intervalIntegrable_delay hf (by linarith) (by linarith)) intervalIntegrable_const
      fun u hu => ?_
    have hu1 : 1 ≤ u - 1 := by linarith [hu.1]
    have hfu : f (u - 1) ≤ f (s' + 1) := hf (show (0:ℝ) < u - 1 by linarith) (show (0:ℝ) < s' + 1 by linarith) (by linarith [hu.2])
    have hfu0 := hf0 (u - 1) (by linarith)
    calc g u = f (u - 1) / (u - 1) := rfl
      _ ≤ f (u - 1) / 1 := div_le_div_of_nonneg_left hfu0 one_pos hu1
      _ ≤ f (s' + 1) := by rw [div_one]; exact hfu
  calc _ ≤ ∑ i ∈ Finset.range k, c * ∫ u in t (i + 2)..t (i + 3), g u := sum_le_sum hterm
    _ = c * ∫ u in t 2..t (k + 2), g u := by rw [← mul_sum, hsum]
    _ ≤ c * ((∫ u in s..s', g u) + 2 * h * f (s' + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        linarith

end Riemann

/-- **The lower Buchstab inequality in the limit** (step 2):
`a(s') − ∫_s^{s'} b(t−1)/(t−1) dt ≤ a(s)` for `2 ≤ s ≤ s'`. -/
theorem buchstab_limit_a' {s s' : ℝ} (hs : 2 ≤ s) (hss' : s ≤ s') :
    aLow s' - ∫ t in s..s', bUp (t - 1) / (t - 1) ≤ aLow s := by
  rcases eq_or_lt_of_le hss' with rfl | hlt
  · simp
  set I := ∫ t in s..s', bUp (t - 1) / (t - 1)
  have hB0 : ∀ x : ℝ, 0 < x → 0 ≤ bUp x := fun x hx => bUp_nonneg hx
  -- h_k → 0
  have hh : Tendsto (fun k : ℕ => (s' - s) / k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun k : ℕ => (1 + 3 * ((s' - s) / k) / (s - 1)) *
      (I + 2 * ((s' - s) / k) * bUp (s' + 1))) atTop (𝓝 ((1 + 3 * 0 / (s - 1)) *
      (I + 2 * 0 * bUp (s' + 1)))) :=
    ((tendsto_const_nhds.add ((tendsto_const_nhds.mul hh).div_const _)).mul
      (tendsto_const_nhds.add ((tendsto_const_nhds.mul hh).mul tendsto_const_nhds)))
  simp only [mul_zero, zero_div, add_zero, zero_mul, one_mul] at hR
  have hev : ∀ᶠ k : ℕ in atTop, aLow s' - aLow s ≤ (1 + 3 * ((s' - s) / k) / (s - 1)) *
      (I + 2 * ((s' - s) / k) * bUp (s' + 1)) := by
    filter_upwards [hh.eventually (ge_mem_nhds one_pos), eventually_ge_atTop 1] with k hk1 hk
    have h1 := aLow_ge_bins hs hlt (k := k) hk
    have h2 := riemann_delay_le bUp_mono' hB0 hs hlt (k := k) hk hk1
    linarith
  have := ge_of_tendsto hR hev
  linarith
end LeanFormalizations.Erdos385.LinearSieve

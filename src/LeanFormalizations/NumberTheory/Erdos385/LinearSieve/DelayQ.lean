/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.DelayConstruct

/-!
# Convergence of `u = Q/s` for the growing solution `Q = sol 1`

`s'u(s') − s u(s) = ∫_s^{s'} u(t−1) dt` (`s ≥ 2`).  Hence (i) for `t ≥ 3`, `u(t)` is a convex
combination of `u(t−1)` and the mean of `u` on `[t−2, t−1]`, so a band `[m, m+L]` containing `u` on
`[x−2, x]` contains `u` on `[x−2, ∞)`; (ii) on `[x, x+1]`, `u` oscillates by `≤ L/x`; so the band on
`[x, x+2]` has width `≤ 4L/x`.  Iterating from `x₀ = 220` gives `|u − ℓ| ≤ K e^{−2s}`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve.Delay

open MeasureTheory Set Filter

local notation "Q" => sol 1

/-- `u = Q/s`. -/
noncomputable def u (s : ℝ) : ℝ := Q s / s

lemma u_cont_on {a b : ℝ} (ha : 0 < a) : ContinuousOn u (Icc a b) :=
  (sol_continuous 1).continuousOn.div continuousOn_id fun t ht =>
    (show (0 : ℝ) < t by linarith [ht.1]).ne'

lemma u_pos {s : ℝ} (hs : 0 < s) : 0 < u s := div_pos (by linarith [solQ_ge_two s]) hs

/-- `s' u(s') − s u(s) = ∫_s^{s'} u(t−1)`. -/
lemma u_two_point {s s' : ℝ} (hs : 2 ≤ s) (hss : s ≤ s') :
    s' * u s' - s * u s = ∫ t in s..s', u (t - 1) := by
  have h := sol_two_point 1 hs hss
  unfold u
  rw [mul_div_cancel₀ _ (by linarith), mul_div_cancel₀ _ (by linarith), h, one_mul]
  ring

lemma u_ii {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => u (t - 1)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  have : ContinuousOn u (Icc (a - 1) (b - 1)) := u_cont_on (by linarith)
  exact this.comp (by fun_prop) fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The band predicate. -/
def Band (a b m L : ℝ) : Prop := ∀ t, a ≤ t → t ≤ b → m ≤ u t ∧ u t ≤ m + L

/-- **Propagation**: a band on `[x−2, x]` persists forever (`x ≥ 3`). -/
lemma band_forever {x m L : ℝ} (hx : 3 ≤ x) (hB : Band (x - 2) x m L) :
    ∀ t, x - 2 ≤ t → m ≤ u t ∧ u t ≤ m + L := by
  have key : ∀ n : ℕ, Band (x - 2) (x + n) m L := by
    intro n
    induction n with
    | zero => simpa using hB
    | succ n ih =>
      intro t ht1 ht2
      push_cast at ht2
      rcases le_total t (x + n) with h | h
      · exact ih t ht1 h
      have ht3 : 3 ≤ t := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h2p := u_two_point (s := t - 1) (s' := t) (by linarith) (by linarith)
      rw [intervalIntegral.integral_comp_sub_right (fun r => u r) 1] at h2p
      have hprev := ih (t - 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by linarith)
      have hcont : ContinuousOn u (Icc (t - 1 - 1) (t - 1)) := u_cont_on (by linarith)
      have hii : IntervalIntegrable u volume (t - 1 - 1) (t - 1) :=
        hcont.intervalIntegrable_of_Icc (by linarith)
      have hlo : ∫ r in (t - 1 - 1)..(t - 1), m ≤ ∫ r in (t - 1 - 1)..(t - 1), u r :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hii
          fun r hr => (ih r (by linarith [hr.1]) (by linarith [hr.2])).1
      have hhi : ∫ r in (t - 1 - 1)..(t - 1), u r ≤ ∫ r in (t - 1 - 1)..(t - 1), (m + L) :=
        intervalIntegral.integral_mono_on (by linarith) hii intervalIntegrable_const
          fun r hr => (ih r (by linarith [hr.1]) (by linarith [hr.2])).2
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
      have htpos : 0 < t := by linarith
      constructor
      · by_contra hc; push Not at hc
        nlinarith [hprev.1]
      · by_contra hc; push Not at hc
        nlinarith [hprev.2]
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (t - x)
  exact key n t ht (by linarith)

/-- **Oscillation** on `[x, x+1]`. -/
lemma band_osc {x m L : ℝ} (hx : 3 ≤ x) (hB : Band (x - 2) x m L) {s s' : ℝ}
    (hs : x ≤ s) (hss : s ≤ s') (hs' : s' ≤ x + 1) : |u s' - u s| ≤ L / x := by
  have hF := band_forever hx hB
  have h2p := u_two_point (by linarith : 2 ≤ s) hss
  have hrw : s' * (u s' - u s) = ∫ t in s..s', (u (t - 1) - u s) := by
    rw [intervalIntegral.integral_sub (u_ii (by linarith) hss) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, ← h2p]; ring
  have hbound : ‖∫ t in s..s', (u (t - 1) - u s)‖ ≤ L * |s' - s| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le hss] at ht
    have h1 := hF (t - 1) (by linarith [ht.1])
    have h2 := hF s (by linarith)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [← hrw, Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s'),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ s' - s)] at hbound
  have hL : 0 ≤ L := by have := hB x (by linarith) le_rfl; linarith [this.1, this.2]
  rw [le_div_iff₀ (by linarith)]
  have : |u s' - u s| * s' ≤ L := by nlinarith [abs_nonneg (u s' - u s)]
  nlinarith [abs_nonneg (u s' - u s)]

/-- **Contraction**: a width-`L` band on `[x−2, x]` gives a width-`4L/x` band on `[x, x+2]`. -/
lemma band_step {x m L : ℝ} (hx : 3 ≤ x) (hB : Band (x - 2) x m L) :
    Band x (x + 2) (u x - 2 * L / x) (4 * L / x) := by
  have hF := band_forever hx hB
  have hB1 : Band (x + 1 - 2) (x + 1) m L := fun t h1 _ => hF t (by linarith)
  have hxpos : 0 < x := by linarith
  intro t ht1 ht2
  have hdiff : |u t - u x| ≤ 2 * L / x := by
    rcases le_total t (x + 1) with h | h
    · have := band_osc hx hB le_rfl ht1 h
      have hL : 0 ≤ L / x := (abs_nonneg _).trans this
      calc _ ≤ L / x := this
        _ ≤ 2 * L / x := by rw [mul_div_assoc]; linarith
    · have h1 := band_osc hx hB le_rfl (by linarith) (le_refl (x + 1))
      have h2 := band_osc (by linarith) hB1 le_rfl h (by linarith)
      have hLx : L / (x + 1) ≤ L / x := by
        have hL : 0 ≤ L / x := (abs_nonneg _).trans h1
        have hL0 : 0 ≤ L := by
          by_contra hc; push Not at hc; have := div_neg_of_neg_of_pos hc hxpos; linarith
        exact div_le_div_of_nonneg_left hL0 hxpos (by linarith)
      calc |u t - u x| ≤ |u t - u (x + 1)| + |u (x + 1) - u x| := abs_sub_le _ _ _
        _ ≤ L / x + L / x := add_le_add (h2.trans hLx) h1
        _ = 2 * L / x := by ring
  rw [abs_le] at hdiff
  constructor
  · linarith
  · have : u x - 2 * L / x + 4 * L / x = u x + 2 * L / x := by ring
    linarith

end LeanFormalizations.Erdos385.LinearSieve.Delay

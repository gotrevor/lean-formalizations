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

lemma band_widen {a b m L L' : ℝ} (hB : Band a b m L) (hL : L ≤ L') : Band a b m L' :=
  fun t h1 h2 => ⟨(hB t h1 h2).1, (hB t h1 h2).2.trans (by linarith)⟩

/-- **Convergence of `u`** with rate `e^{−2s}`, and the resulting estimate for `Q`. -/
theorem Q_conv : ∃ ω M : ℝ, 0 < ω ∧ 0 ≤ M ∧ ∀ s, 2 ≤ s →
    |Q s - 2 * ω * s| ≤ M * Real.exp (-s) := by
  set x0 : ℝ := 300
  set r : ℝ := Real.exp (-4)
  have hr0 : 0 < r := Real.exp_pos _
  have he4 : Real.exp 4 ≤ 75 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    nlinarith [pow_le_pow_left₀ h0 h1.le 4]
  have hr1 : r ≤ 1 / 2 := by
    have : r * Real.exp 4 = 1 := by rw [← Real.exp_add]; norm_num
    have : 1 ≤ Real.exp 4 * (1 / 2) := by
      have := Real.add_one_le_exp 4; linarith
    nlinarith
  have hr4 : ∀ x : ℝ, x0 ≤ x → 4 / x ≤ r := by
    intro x hx
    have : r * Real.exp 4 = 1 := by rw [← Real.exp_add]; norm_num
    rw [div_le_iff₀ (by norm_num [x0] at hx ⊢; linarith)]
    nlinarith
  -- initial band on [x0 - 2, x0]
  obtain ⟨tmin, htmin, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num))
    (u_cont_on (a := x0 - 2) (b := x0) (by norm_num [x0]))
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num))
    (u_cont_on (a := x0 - 2) (b := x0) (by norm_num [x0]))
  set m0 := u tmin
  set L0 := u tmax - u tmin
  have hm0 : 0 < m0 := u_pos (by linarith [htmin.1])
  have hL0 : 0 ≤ L0 := by have := hmax htmin; simp only [mem_setOf_eq] at this; linarith
  have hB0 : Band (x0 - 2) x0 m0 L0 := fun t h1 h2 =>
    ⟨hmin ⟨h1, h2⟩, by have := hmax ⟨h1, h2⟩; simp only [mem_setOf_eq] at this; linarith⟩
  have hx03 : (3 : ℝ) ≤ x0 := by norm_num
  have bands : ∀ k : ℕ, ∃ m, Band (x0 + 2 * k - 2) (x0 + 2 * k) m (L0 * r ^ k) := by
    intro k
    induction k with
    | zero => exact ⟨m0, by simpa using hB0⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      have hxk : x0 ≤ x0 + 2 * k := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hstep := band_step (by linarith) hm
      refine ⟨u (x0 + 2 * k) - 2 * (L0 * r ^ k) / (x0 + 2 * k), ?_⟩
      have e1 : x0 + 2 * ((k + 1 : ℕ) : ℝ) - 2 = x0 + 2 * k := by push_cast; ring
      have e2 : x0 + 2 * ((k + 1 : ℕ) : ℝ) = x0 + 2 * k + 2 := by push_cast; ring
      rw [e1, e2]
      refine band_widen hstep ?_
      have hpos : 0 < x0 + 2 * k := by linarith
      have := hr4 _ hxk
      have hLk : 0 ≤ L0 * r ^ k := by positivity
      calc 4 * (L0 * r ^ k) / (x0 + 2 * k) = 4 / (x0 + 2 * k) * (L0 * r ^ k) := by ring
        _ ≤ r * (L0 * r ^ k) := mul_le_mul_of_nonneg_right this hLk
        _ = L0 * r ^ (k + 1) := by ring
  have forever : ∀ k : ℕ, ∀ t, x0 + 2 * k - 2 ≤ t → ∀ t', x0 + 2 * k - 2 ≤ t' →
      |u t - u t'| ≤ L0 * r ^ k := by
    intro k t ht t' ht'
    obtain ⟨m, hm⟩ := bands k
    have hF := band_forever (x := x0 + 2 * (k : ℝ))
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hm
    have h1 := hF t (by linarith)
    have h2 := hF t' (by linarith)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  set a : ℕ → ℝ := fun k => u (x0 + 2 * k)
  have hgeom : ∀ k, dist (a k) (a (k + 1)) ≤ L0 * r ^ k := by
    intro k
    rw [Real.dist_eq]
    refine forever k _ (by linarith) _ (by push_cast; linarith)
  have hr1' : r < 1 := by linarith
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r L0 hr1' hgeom)
  have hdl : ∀ k, |a k - l| ≤ L0 * r ^ k / (1 - r) := fun k => by
    rw [← Real.dist_eq]; exact dist_le_of_le_geometric_of_tendsto r L0 hr1' hgeom hl k
  have hlpos : m0 ≤ l := by
    refine ge_of_tendsto hl (Eventually.of_forall fun k => ?_)
    have := band_forever hx03 hB0 (x0 + 2 * k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    exact this.1
  -- tail estimate
  have htail : ∀ s, x0 ≤ s → |u s - l| ≤ 3 * L0 * Real.exp (2 * x0 + 4) * Real.exp (-2 * s) := by
    intro s hs
    set k := ⌊(s - x0) / 2⌋₊
    have hk1 : (k : ℝ) ≤ (s - x0) / 2 := Nat.floor_le (by linarith)
    have hk2 : (s - x0) / 2 < k + 1 := Nat.lt_floor_add_one _
    have h1 := forever k s (by linarith) (x0 + 2 * k) (by linarith)
    have h2 := hdl k
    have hrk : r ^ k = Real.exp (-4 * k) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hexp : Real.exp (-4 * k) ≤ Real.exp (2 * x0 + 4) * Real.exp (-2 * s) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h1r : 1 / (1 - r) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hLr : 0 ≤ L0 * r ^ k := by positivity
    calc |u s - l| ≤ |u s - a k| + |a k - l| := abs_sub_le _ _ _
      _ ≤ L0 * r ^ k + L0 * r ^ k / (1 - r) := add_le_add h1 h2
      _ = L0 * r ^ k * (1 + 1 / (1 - r)) := by ring
      _ ≤ L0 * r ^ k * 3 := mul_le_mul_of_nonneg_left (by linarith) hLr
      _ = 3 * L0 * Real.exp (-4 * k) := by rw [hrk]; ring
      _ ≤ 3 * L0 * (Real.exp (2 * x0 + 4) * Real.exp (-2 * s)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  -- compact part
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((sol_continuous 1).sub (continuous_const.mul continuous_id)).continuousOn
      (s := Icc (2 : ℝ) x0) (f := fun s => Q s - l * s))
  refine ⟨l / 2, 3 * L0 * Real.exp (2 * x0 + 4) + |B| * Real.exp x0, by linarith, by positivity,
    fun s hs => ?_⟩
  have hl2 : 2 * (l / 2) * s = l * s := by ring
  rw [hl2]
  have hes : 0 < Real.exp (-s) := Real.exp_pos _
  rcases le_total s x0 with h | h
  · have := hB s ⟨hs, h⟩
    rw [Real.norm_eq_abs] at this
    have h1 : 1 ≤ Real.exp x0 * Real.exp (-s) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have h2 : 0 ≤ 3 * L0 * Real.exp (2 * x0 + 4) * Real.exp (-s) := by positivity
    nlinarith [le_abs_self B, abs_nonneg B]
  · have ht := htail s h
    have hspos : 0 < s := by linarith
    have hQ : Q s - l * s = s * (u s - l) := by
      unfold u; field_simp
    rw [hQ, abs_mul, abs_of_pos hspos]
    have hse : s * Real.exp (-2 * s) ≤ Real.exp (-s) := by
      have h1 : s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
      have : Real.exp (-2 * s) = Real.exp (-s) * Real.exp (-s) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have hC : 0 ≤ 3 * L0 * Real.exp (2 * x0 + 4) := by positivity
    calc s * |u s - l| ≤ s * (3 * L0 * Real.exp (2 * x0 + 4) * Real.exp (-2 * s)) :=
          mul_le_mul_of_nonneg_left ht hspos.le
      _ = 3 * L0 * Real.exp (2 * x0 + 4) * (s * Real.exp (-2 * s)) := by ring
      _ ≤ 3 * L0 * Real.exp (2 * x0 + 4) * Real.exp (-s) := mul_le_mul_of_nonneg_left hse hC
      _ ≤ _ := by
          have h0 : 0 ≤ |B| * Real.exp x0 * Real.exp (-s) := by positivity
          linarith [show (3 * L0 * Real.exp (2 * x0 + 4) + |B| * Real.exp x0) * Real.exp (-s) =
            3 * L0 * Real.exp (2 * x0 + 4) * Real.exp (-s) + |B| * Real.exp x0 * Real.exp (-s) by ring]

end LeanFormalizations.Erdos385.LinearSieve.Delay

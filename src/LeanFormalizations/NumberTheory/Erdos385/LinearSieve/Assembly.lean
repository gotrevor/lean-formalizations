/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Comparison

/-!
# Assembly of the delay-system comparison (phase E5, step 5 applied)

`pos_of_delay_system`: if `(a, b)` satisfy the Jurkat–Richert delay inequalities, `(α, β)` the
equalities, they agree on `(1, 2]` in the right direction and both pairs approach each other
exponentially, then `α ≤ a` on `[2, ∞)`.  Proof: `comparison_principle` on
`K = max(α − a, b − β, 0)`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open MeasureTheory Set Filter

/-- The positive part of the discrepancy. -/
noncomputable def discK (a b α β : ℝ → ℝ) (s : ℝ) : ℝ := max (max (α s - a s) (b s - β s)) 0

lemma discK_nonneg (a b α β : ℝ → ℝ) (s : ℝ) : 0 ≤ discK a b α β s := le_max_right _ _

lemma ii_shift_div {f : ℝ → ℝ} {s s' : ℝ} (hs : 2 ≤ s) (hss : s ≤ s')
    (hf : IntervalIntegrable (fun t => f (t - 1)) volume s s') :
    IntervalIntegrable (fun t => f (t - 1) / (t - 1)) volume s s' := by
  simp_rw [div_eq_mul_inv]
  refine hf.mul_continuousOn ?_
  refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun t ht => ?_
  rw [uIcc_of_le hss] at ht
  linarith [ht.1]

lemma ii_mono_shift {f : ℝ → ℝ} (hf : Monotone f) (s s' : ℝ) :
    IntervalIntegrable (fun t => f (t - 1)) volume s s' :=
  Monotone.intervalIntegrable fun x y h => hf (by linarith)

lemma ii_cont_shift {f : ℝ → ℝ} (hf : Continuous f) (s s' : ℝ) :
    IntervalIntegrable (fun t => f (t - 1)) volume s s' :=
  (hf.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _

lemma ii_sup {f g : ℝ → ℝ} {s s' : ℝ} (hf : IntervalIntegrable f volume s s')
    (hg : IntervalIntegrable g volume s s') :
    IntervalIntegrable (fun t => max (f t) (g t)) volume s s' :=
  ⟨hf.1.sup hg.1, hf.2.sup hg.2⟩

theorem pos_of_delay_system (a b α β : ℝ → ℝ) (M : ℝ)
    (ha : Monotone a) (hb : Monotone b) (hα : Continuous α) (hβ : Continuous β)
    (h12 : ∀ u, 1 < u → u ≤ 2 → α u ≤ a u ∧ b u ≤ β u)
    (hA : ∀ s s', 2 ≤ s → s ≤ s' → a s' - ∫ t in s..s', b (t - 1) / (t - 1) ≤ a s)
    (hB : ∀ s s', 2 ≤ s → s ≤ s' → b s ≤ b s' - ∫ t in s..s', a (t - 1) / (t - 1))
    (hαβ : ∀ s s', 2 ≤ s → s ≤ s' →
      α s = α s' - ∫ t in s..s', β (t - 1) / (t - 1) ∧
      β s = β s' - ∫ t in s..s', α (t - 1) / (t - 1))
    (hdec : ∀ s, 2 ≤ s → discK a b α β s ≤ M * Real.exp (-s)) :
    ∀ s, 2 ≤ s → α s ≤ a s := by
  set k := discK a b α β with hk
  -- interval integrability of the shifted k
  have hkii : ∀ s s', IntervalIntegrable (fun t => k (t - 1)) volume s s' := by
    intro s s'
    have h1 := (ii_cont_shift hα s s').sub (ii_mono_shift ha s s')
    have h2 := (ii_mono_shift hb s s').sub (ii_cont_shift hβ s s')
    exact ii_sup (ii_sup h1 h2) intervalIntegrable_const
  have hkmeas : Measurable k := by
    have h1 : Measurable fun s => α s - a s := hα.measurable.sub ha.measurable
    have h2 : Measurable fun s => b s - β s := hb.measurable.sub hβ.measurable
    exact (h1.max h2).max measurable_const
  -- the real recursion: for 2 ≤ s ≤ s', k s ≤ M e^{-s'} + ∫_s^{s'} k(t-1)/(t-1)
  have hrecR : ∀ s s', 2 ≤ s → s ≤ s' →
      k s ≤ M * Real.exp (-s') + ∫ t in s..s', k (t - 1) / (t - 1) := by
    intro s s' hs hss
    have hkI := ii_shift_div hs hss (hkii s s')
    have hdec' := hdec s' (by linarith)
    have hk1 : α s' - a s' ≤ k s' := (le_max_left _ _).trans (le_max_left _ _)
    have hk2 : b s' - β s' ≤ k s' := (le_max_right _ _).trans (le_max_left _ _)
    have hkpos : 0 ≤ ∫ t in s..s', k (t - 1) / (t - 1) := by
      refine intervalIntegral.integral_nonneg hss fun t ht => ?_
      exact div_nonneg (discK_nonneg _ _ _ _ _) (by linarith [ht.1])
    obtain ⟨eα, eβ⟩ := hαβ s s' hs hss
    have iβ := ii_shift_div hs hss (ii_cont_shift hβ s s')
    have iα := ii_shift_div hs hss (ii_cont_shift hα s s')
    have ib := ii_shift_div hs hss (ii_mono_shift hb s s')
    have ia := ii_shift_div hs hss (ii_mono_shift ha s s')
    have m1 : ∫ t in s..s', (b (t - 1) / (t - 1) - β (t - 1) / (t - 1)) ≤
        ∫ t in s..s', k (t - 1) / (t - 1) := by
      refine intervalIntegral.integral_mono_on hss (ib.sub iβ) hkI fun t ht => ?_
      have ht1 : 0 < t - 1 := by linarith [ht.1]
      rw [← sub_div]
      exact div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) ht1.le
    have m2 : ∫ t in s..s', (α (t - 1) / (t - 1) - a (t - 1) / (t - 1)) ≤
        ∫ t in s..s', k (t - 1) / (t - 1) := by
      refine intervalIntegral.integral_mono_on hss (iα.sub ia) hkI fun t ht => ?_
      have ht1 : 0 < t - 1 := by linarith [ht.1]
      rw [← sub_div]
      exact div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) ht1.le
    rw [intervalIntegral.integral_sub ib iβ] at m1
    rw [intervalIntegral.integral_sub iα ia] at m2
    have hAs := hA s s' hs hss
    have hBs := hB s s' hs hss
    have hMe : 0 ≤ M * Real.exp (-s') := (discK_nonneg _ _ _ _ _).trans hdec'
    refine max_le (max_le ?_ ?_) (by linarith)
    · linarith
    · linarith
  sorry

end LeanFormalizations.Erdos385.LinearSieve

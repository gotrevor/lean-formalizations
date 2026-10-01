/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Existence for the delay equation `X(s) = 2 + σ ∫_2^s X(t−1)/(t−1) dt` (phase E5, step 4)

Method of steps as a Picard iteration: the `n`-th iterate is already exact on `(−∞, n+2]`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve.Delay

open MeasureTheory Set Filter

/-- The (globally continuous) integrand: `F(t−1)/(t−1)`, frozen at `t ≤ 2`. -/
noncomputable def g (F : ℝ → ℝ) (t : ℝ) : ℝ := F (max (t - 1) 1) / max (t - 1) 1

/-- One Picard step. -/
noncomputable def T (σ : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ := 2 + σ * ∫ t in (2 : ℝ)..max s 2, g F t

/-- The iterates. -/
noncomputable def iter (σ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 2
  | n + 1 => T σ (iter σ n)

lemma g_continuous {F : ℝ → ℝ} (hF : Continuous F) : Continuous (g F) := by
  unfold g
  refine (hF.comp (by fun_prop)).div (by fun_prop) fun t => ?_
  have : (1 : ℝ) ≤ max (t - 1) 1 := le_max_right _ _
  linarith

lemma T_continuous (σ : ℝ) {F : ℝ → ℝ} (hF : Continuous F) : Continuous (T σ F) := by
  unfold T
  have h := intervalIntegral.continuous_primitive
    (fun a b => (g_continuous hF).intervalIntegrable (μ := volume) a b) 2
  exact continuous_const.add (continuous_const.mul (h.comp (continuous_id.max continuous_const)))

lemma iter_continuous (σ : ℝ) : ∀ n, Continuous (iter σ n)
  | 0 => continuous_const
  | n + 1 => T_continuous σ (iter_continuous σ n)

lemma iter_succ_eq (σ : ℝ) : ∀ n : ℕ, ∀ s : ℝ, s ≤ n + 2 → iter σ (n + 1) s = iter σ n s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    simp only [iter, T, CharP.cast_eq_zero, zero_add] at hs ⊢
    rw [max_eq_right hs, intervalIntegral.integral_same, mul_zero, add_zero]
  | succ n ih =>
    intro s hs
    show T σ (iter σ (n + 1)) s = T σ (iter σ n) s
    unfold T
    congr 2
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ≤ max s 2 := by
      rcases le_total 2 (max s 2) with h | h
      · rw [uIcc_of_le h] at ht; exact ht.2
      · rw [uIcc_of_ge h] at ht; exact ht.2.trans (le_max_right _ _)
    have hm : max (t - 1) 1 ≤ (n : ℝ) + 2 := by
      push_cast at hs
      refine max_le ?_ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      rcases le_total s 2 with h2 | h2
      · rw [max_eq_right h2] at ht'; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      · rw [max_eq_left h2] at ht'; linarith
    unfold g
    rw [ih _ hm]

lemma iter_eq_of_le (σ : ℝ) {n m : ℕ} (hnm : n ≤ m) {s : ℝ} (hs : s ≤ n + 2) :
    iter σ m s = iter σ n s := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [iter_succ_eq σ m s (hs.trans (by exact_mod_cast (by omega : n + 2 ≤ m + 2))), ih]

/-- The solution. -/
noncomputable def sol (σ : ℝ) (s : ℝ) : ℝ := iter σ ⌈s⌉₊ s

lemma sol_eq_iter (σ : ℝ) {n : ℕ} {s : ℝ} (hs : s ≤ n + 2) : sol σ s = iter σ n s := by
  unfold sol
  rcases le_total n ⌈s⌉₊ with h | h
  · exact iter_eq_of_le σ h hs
  · exact (iter_eq_of_le σ h (by linarith [Nat.le_ceil s])).symm

lemma sol_continuous (σ : ℝ) : Continuous (sol σ) := by
  rw [continuous_iff_continuousAt]
  intro s
  obtain ⟨n, hn⟩ := exists_nat_gt s
  have hev : iter σ n =ᶠ[nhds s] sol σ := by
    filter_upwards [Iio_mem_nhds (show s < (n : ℝ) + 2 by linarith)] with x hx
    exact (sol_eq_iter σ (le_of_lt hx)).symm
  exact ((iter_continuous σ n).continuousAt).congr hev

lemma sol_init (σ : ℝ) {s : ℝ} (hs : s ≤ 2) : sol σ s = 2 := by
  rw [sol_eq_iter σ (n := 0) (by simpa using hs)]; rfl

/-- The integral equation. -/
lemma sol_eq (σ : ℝ) {s : ℝ} (hs : 2 ≤ s) :
    sol σ s = 2 + σ * ∫ t in (2 : ℝ)..s, sol σ (t - 1) / (t - 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt s
  rw [sol_eq_iter σ (n := n + 1) (by push_cast; linarith)]
  show T σ (iter σ n) s = _
  unfold T
  rw [max_eq_left hs]
  congr 2
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hs] at ht
  unfold g
  rw [max_eq_left (by linarith [ht.1]), sol_eq_iter σ (n := n) (by linarith [ht.2])]

lemma shift_ii (σ : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => sol σ (t - 1) / (t - 1)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div ((sol_continuous σ).comp (by fun_prop)).continuousOn
    (by fun_prop) fun t ht => ?_
  have : min a b ≤ t := ht.1
  have : 2 ≤ min a b := le_min ha hb
  linarith

/-- Two-point form. -/
lemma sol_two_point (σ : ℝ) {s s' : ℝ} (hs : 2 ≤ s) (hss : s ≤ s') :
    sol σ s' = sol σ s + σ * ∫ t in s..s', sol σ (t - 1) / (t - 1) := by
  rw [sol_eq σ hs, sol_eq σ (hs.trans hss)]
  rw [← intervalIntegral.integral_interval_sub_left (shift_ii σ le_rfl (hs.trans hss))
    (shift_ii σ le_rfl hs)]
  ring

end LeanFormalizations.Erdos385.LinearSieve.Delay

namespace LeanFormalizations.Erdos385.LinearSieve.Delay

open MeasureTheory Set

lemma iter_one_ge_two : ∀ n : ℕ, ∀ s : ℝ, 2 ≤ iter 1 n s
  | 0, _ => le_rfl
  | n + 1, s => by
    show 2 ≤ T 1 (iter 1 n) s
    unfold T
    have : 0 ≤ ∫ t in (2 : ℝ)..max s 2, g (iter 1 n) t := by
      refine intervalIntegral.integral_nonneg (le_max_right _ _) fun t _ => ?_
      unfold g
      have h1 : (1 : ℝ) ≤ max (t - 1) 1 := le_max_right _ _
      have h2 := iter_one_ge_two n (max (t - 1) 1)
      positivity
    linarith

lemma solQ_ge_two (s : ℝ) : 2 ≤ sol 1 s := iter_one_ge_two _ _

end LeanFormalizations.Erdos385.LinearSieve.Delay

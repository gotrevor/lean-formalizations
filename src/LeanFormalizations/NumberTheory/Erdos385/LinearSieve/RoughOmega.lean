/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.RoughPNT
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Bounded
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.DelaySolution

/-!
# `ω∞ ≤ e^{−γ}` from rough numbers (phase E5, `omega_le`)

`φ(s) = liminf Φ(N, N^{1/s}) log N / N` satisfies `φ ≥ 1` on `(1, 2]` (PNT), the forward
Buchstab inequality `φ(s') ≥ φ(s) + ∫_s^{s'} φ(t−1)/(t−1)` (leaf `phi_buchstab`), and `φ ≤ b`.
Comparison with the delay solution gives `Q/2 ≤ φ ≤ b ≤ Cs + Me^{−s}`, hence `ω ≤ C`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Filter MeasureTheory Set

/-- The normalised rough sequence. -/
noncomputable def phiSeq (s : ℝ) (N : ℕ) : ℝ :=
  (rough N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N

/-- `φ(s)`. -/
noncomputable def phiLow (s : ℝ) : ℝ := liminf (phiSeq s) atTop

lemma phiSeq_nonneg (s : ℝ) (N : ℕ) : 0 ≤ phiSeq s N := by
  unfold phiSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg this
    positivity

lemma phiSeq_le_bSeq (s : ℝ) (N : ℕ) : phiSeq s N ≤ bSeq s N := by
  unfold phiSeq bSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg this
    have h : (rough N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
      exact_mod_cast rough_le_siftMax _ _
    gcongr

lemma phiSeq_bdd {s : ℝ} (hs : 0 < s) : IsBoundedUnder (· ≤ ·) atTop (phiSeq s) :=
  (bSeq_bdd hs).mono_le (Eventually.of_forall fun N => phiSeq_le_bSeq s N)

lemma phiSeq_bdd_below (s : ℝ) : IsBoundedUnder (· ≥ ·) atTop (phiSeq s) :=
  isBoundedUnder_of ⟨0, phiSeq_nonneg s⟩

/-- `φ ≥ 1` on `(1, ∞)`… used on `(1, 2]`. -/
theorem phi_ge_one {s : ℝ} (hs : 1 < s) : 1 ≤ phiLow s := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have : 1 - δ ≤ phiLow s :=
    le_liminf_of_le (phiSeq_bdd (by linarith)).isCoboundedUnder_ge (rough_norm_ge hs hδ)
  linarith

theorem phi_le_bUp {s : ℝ} (hs : 0 < s) : phiLow s ≤ bUp s := by
  unfold phiLow bUp
  calc liminf (phiSeq s) atTop ≤ liminf (bSeq s) atTop :=
        liminf_le_liminf (Eventually.of_forall fun N => phiSeq_le_bSeq s N)
          (phiSeq_bdd_below s) (bSeq_bdd hs).isCoboundedUnder_ge
    _ ≤ limsup (bSeq s) atTop :=
        liminf_le_limsup (bSeq_bdd hs) (isBoundedUnder_of ⟨0, bSeq_nonneg s⟩)
    _ = _ := rfl

theorem phi_mono : MonotoneOn phiLow (Ioi 0) := by
  intro s hs s' hs' hss
  simp only [mem_Ioi] at hs hs'
  refine liminf_le_liminf (Eventually.of_forall fun N => ?_) (phiSeq_bdd_below s)
    (phiSeq_bdd hs').isCoboundedUnder_ge
  unfold phiSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have := Real.log_nonneg h1
  have hz : ⌊(N : ℝ) ^ (1 / s')⌋₊ ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le h1
      (one_div_le_one_div_of_le hs hss))
  have : (rough N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ rough N ⌊(N : ℝ) ^ (1 / s')⌋₊ := by
    exact_mod_cast sift_anti_z 1 N _ hz
  gcongr

/-- Leaf: the forward Buchstab inequality in the limit (same mechanism as `buchstab_limit_b`,
with `Φ` in place of `S⁻`; all terms nonnegative). -/
theorem phi_buchstab : ∀ s s' : ℝ, 2 ≤ s → s ≤ s' →
    phiLow s + ∫ t in s..s', phiLow (t - 1) / (t - 1) ≤ phiLow s' := by
  sorry

/-- `ω∞ ≤ C` as a proposition about every delay pair. -/
def OmegaLe : Prop := ∀ Q P : ℝ → ℝ, IsDelayPair Q P → ∀ ω M : ℝ, 0 < ω →
    (∀ s, 2 ≤ s → |Q s - 2 * ω * s| ≤ M * Real.exp (-s)) → ω ≤ mertC

/-- `Q/2 ≤ φ` on `[2, ∞)`. -/
theorem half_Q_le_phi {Q P : ℝ → ℝ} (hQP : IsDelayPair Q P) : ∀ s, 2 ≤ s → Q s / 2 ≤ phiLow s := by
  obtain ⟨hQc, -, hinit, heq⟩ := hQP
  have key : ∀ n : ℕ, ∀ s : ℝ, 2 ≤ s → s ≤ 2 + n → Q s / 2 ≤ phiLow s := by
    intro n
    induction n with
    | zero =>
      intro s h1 h2
      have : s = 2 := by push_cast at h2; linarith
      subst this
      rw [(hinit 2 le_rfl).1]; have := phi_ge_one (s := 2) (by norm_num); linarith
    | succ n ih =>
      intro s h1 h2
      push_cast at h2
      have hphi := phi_buchstab 2 s le_rfl h1
      have hQ := (heq 2 s le_rfl h1).1
      rw [(hinit 2 le_rfl).1] at hQ
      have hphi2 := phi_ge_one (s := 2) (by norm_num)
      -- integrability
      have hiQ : IntervalIntegrable (fun t => Q (t - 1) / (t - 1)) volume 2 s := by
        refine ContinuousOn.intervalIntegrable ?_
        refine ContinuousOn.div (hQc.comp (continuous_id.sub continuous_const)).continuousOn
          (continuous_id.sub continuous_const).continuousOn fun t ht => ?_
        rw [uIcc_of_le h1] at ht
        show t - 1 ≠ 0; linarith [ht.1]
      have hiphi : IntervalIntegrable (fun t => phiLow (t - 1) / (t - 1)) volume 2 s := by
        simp_rw [div_eq_mul_inv]
        refine IntervalIntegrable.mul_continuousOn ?_ ?_
        · refine MonotoneOn.intervalIntegrable ?_
          rw [uIcc_of_le h1]
          intro x hx y hy hxy
          exact phi_mono (show x - 1 ∈ Ioi 0 by simp; linarith [hx.1])
            (show y - 1 ∈ Ioi 0 by simp; linarith [hy.1]) (by linarith)
        · refine ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
            fun t ht => ?_
          rw [uIcc_of_le h1] at ht
          show t - 1 ≠ 0; linarith [ht.1]
      have hdiff : 0 ≤ ∫ t in (2 : ℝ)..s, (phiLow (t - 1) / (t - 1) - Q (t - 1) / (t - 1) / 2) := by
        rw [intervalIntegral.integral_of_le h1]
        refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
        have ht1 : 0 < t - 1 := by linarith [ht.1]
        rw [show phiLow (t - 1) / (t - 1) - Q (t - 1) / (t - 1) / 2 =
          (phiLow (t - 1) - Q (t - 1) / 2) / (t - 1) by ring]
        refine div_nonneg ?_ ht1.le
        rcases le_total (t - 1) 2 with h | h
        · rw [(hinit _ h).1]; have := phi_ge_one (s := t - 1) (by linarith [ht.1]); linarith
        · have := ih (t - 1) h (by linarith [ht.2]); linarith
      rw [intervalIntegral.integral_sub hiphi (hiQ.div_const 2)] at hdiff
      have hhalf : ∫ t in (2 : ℝ)..s, Q (t - 1) / (t - 1) / 2 =
          (∫ t in (2 : ℝ)..s, Q (t - 1) / (t - 1)) / 2 := intervalIntegral.integral_div _ _
      rw [hhalf] at hdiff
      linarith
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_ge s
  exact key n s hs (by linarith)

/-- **`ω ≤ C`** from an upper bound `b(s) ≤ Cs + Me^{−s}`. -/
theorem omegaLe_of_bUp (hb : ∃ M : ℝ, ∀ s, 2 ≤ s → bUp s ≤ mertC * s + M * Real.exp (-s)) :
    OmegaLe := by
  intro Q P hQP ω M' hω hdec
  obtain ⟨M, hM⟩ := hb
  by_contra hlt
  push Not at hlt
  set K := |M| + |M'|
  set s := max 2 (K / (ω - mertC) + 1)
  have hs : 2 ≤ s := le_max_left _ _
  have hs2 : K / (ω - mertC) + 1 ≤ s := le_max_right _ _
  have h1 := half_Q_le_phi hQP s hs
  have h2 := phi_le_bUp (s := s) (by linarith)
  have h3 := hM s hs
  have h4 := (abs_le.mp (hdec s hs)).1
  have he : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hK1 : M * Real.exp (-s) ≤ |M| := by
    calc M * Real.exp (-s) ≤ |M| * Real.exp (-s) := mul_le_mul_of_nonneg_right (le_abs_self M) he0.le
      _ ≤ |M| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = |M| := mul_one _
  have hK2 : M' * Real.exp (-s) ≤ |M'| := by
    calc M' * Real.exp (-s) ≤ |M'| * Real.exp (-s) := mul_le_mul_of_nonneg_right (le_abs_self M') he0.le
      _ ≤ |M'| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = |M'| := mul_one _
  -- (ω − C) s ≤ M e^{-s} + M' e^{-s}/2 ≤ K
  have hgap : 0 < ω - mertC := by linarith
  have hmain : (ω - mertC) * s ≤ K := by
    nlinarith [abs_nonneg M, abs_nonneg M']
  have : K < (ω - mertC) * s := by
    have := mul_le_mul_of_nonneg_left hs2 hgap.le
    rw [mul_add, mul_div_cancel₀ _ hgap.ne'] at this
    linarith
  linarith

end LeanFormalizations.Erdos385.LinearSieve

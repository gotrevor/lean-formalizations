/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.DelayConstruct

/-!
# The decaying solution `P = sol (−1)`: averaging identity, positivity, decay

`(s−1) P(s) = ∫_{s−1}^s P` for `s ≥ 2` (both sides have derivative `P(s) − P(s−1)`), whence
`P > 0` (first-zero contradiction) and `P(s) ≤ P(s−1)/(s−1)` (P antitone), so `P ≤ 2e⁵ e^{−s}`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve.Delay

open MeasureTheory Set Filter

local notation "P" => sol (-1)

lemma P_cont : Continuous P := sol_continuous _

/-- `R(s) = 2 − ∫_2^s g P`, equal to `P` on `[2, ∞)`. -/
lemma P_eq_R {s : ℝ} (hs : 2 ≤ s) : P s = 2 - ∫ t in (2 : ℝ)..s, g P t := by
  rw [sol_eq _ hs]
  have : ∫ t in (2 : ℝ)..s, sol (-1) (t - 1) / (t - 1) = ∫ t in (2 : ℝ)..s, g P t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hs] at ht
    unfold g; rw [max_eq_left (by linarith [ht.1])]
  rw [this]; ring

/-- **The averaging identity.** -/
lemma P_avg {s : ℝ} (hs : 2 ≤ s) : (s - 1) * P s = ∫ t in (s - 1)..s, P t := by
  set I : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, P t
  set R : ℝ → ℝ := fun u => 2 - ∫ t in (2 : ℝ)..u, g P t
  set f : ℝ → ℝ := fun u => (u - 1) * R u - (I u - I (u - 1))
  have hG := g_continuous P_cont
  have hderiv : ∀ x, 2 ≤ x → HasDerivAt f 0 x := by
    intro x hx
    have hR : HasDerivAt R (-g P x) x := (hG.integral_hasStrictDerivAt 2 x).hasDerivAt.const_sub 2
    have hI : HasDerivAt I (P x) x := (P_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
    have hI1 : HasDerivAt (fun u => I (u - 1)) (P (x - 1)) x := by
      have h := (P_cont.integral_hasStrictDerivAt 0 (x - 1)).hasDerivAt
      have := h.comp x ((hasDerivAt_id x).sub_const 1)
      rw [mul_one] at this
      exact this
    have hf := (((hasDerivAt_id x).sub_const 1).mul hR).sub (hI.sub hI1)
    have hRx : R x = P x := (P_eq_R hx).symm
    have hgx : g P x = P (x - 1) / (x - 1) := by unfold g; rw [max_eq_left (by linarith)]
    have h0 : (0 : ℝ) = 1 * R x + (id x - 1) * -g P x - (P x - P (x - 1)) := by
      have hx1 : x - 1 ≠ 0 := by linarith
      rw [hgx, hRx]; simp only [id]; field_simp; ring
    rw [h0]; exact hf
  have hf2 : f 2 = 0 := by
    simp only [f, R, I, intervalIntegral.integral_same, sub_zero]
    rw [intervalIntegral.integral_interval_sub_left (P_cont.intervalIntegrable _ _)
      (P_cont.intervalIntegrable _ _)]
    have : ∫ t in (2 - 1 : ℝ)..2, P t = ∫ t in (2 - 1 : ℝ)..2, (2 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (by norm_num)] at ht
      exact sol_init _ ht.2
    rw [this]; simp; norm_num
  have hcont : Continuous f := by
    have hRc : Continuous R := continuous_const.sub
      (intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable (μ := volume) a b) 2)
    have hIc : Continuous I :=
      intervalIntegral.continuous_primitive (fun a b => P_cont.intervalIntegrable (μ := volume) a b) 0
    exact ((continuous_id.sub continuous_const).mul hRc).sub (hIc.sub (hIc.comp (by fun_prop)))
  have hconst := constant_of_has_deriv_right_zero hcont.continuousOn
    (fun x hx => (hderiv x hx.1).hasDerivWithinAt) s ⟨hs, le_rfl⟩
  rw [hf2] at hconst
  simp only [f, R, I] at hconst
  rw [intervalIntegral.integral_interval_sub_left (P_cont.intervalIntegrable _ _)
      (P_cont.intervalIntegrable _ _)] at hconst
  rw [P_eq_R hs]; linarith

/-- **Positivity of `P`.** -/
theorem P_pos (s : ℝ) : 0 < P s := by
  by_contra hneg
  push Not at hneg
  set S := {x : ℝ | 2 ≤ x ∧ P x ≤ 0}
  have hS : S.Nonempty := by
    rcases le_total s 2 with h | h
    · rw [sol_init _ h] at hneg; norm_num at hneg
    · exact ⟨s, h, hneg⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le P_cont continuous_const)
  have hbdd : BddBelow S := ⟨2, fun x hx => hx.1⟩
  set s0 := sInf S
  have hs0 : s0 ∈ S := hclosed.csInf_mem hS hbdd
  have hbelow : ∀ t, t < s0 → 0 < P t := by
    intro t ht
    by_contra h; push Not at h
    rcases le_total t 2 with h2 | h2
    · rw [sol_init _ h2] at h; norm_num at h
    · exact absurd (csInf_le hbdd ⟨h2, h⟩) (not_le.mpr ht)
  have hs02 : 2 < s0 := by
    rcases lt_or_eq_of_le hs0.1 with h | h
    · exact h
    · have := hs0.2; rw [← h, sol_init _ le_rfl] at this; norm_num at this
  have hint : 0 < ∫ t in (s0 - 1)..s0, P t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (P_cont.intervalIntegrable _ _)
      (fun t ht => hbelow t ht.2) (by linarith)
  have := P_avg hs0.1
  have h2 := hs0.2
  nlinarith

lemma P_antitone : AntitoneOn P (Ici 1) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  rcases le_total y 2 with hy2 | hy2
  · rw [sol_init _ hy2, sol_init _ (hxy.trans hy2)]
  rcases le_total x 2 with hx2 | hx2
  · rw [sol_init _ hx2, ← sol_init (-1) (le_refl (2 : ℝ))]
    rw [sol_two_point _ le_rfl hy2]
    have : 0 ≤ ∫ t in (2 : ℝ)..y, P (t - 1) / (t - 1) :=
      intervalIntegral.integral_nonneg hy2 fun t ht => div_nonneg (P_pos _).le (by linarith [ht.1])
    linarith
  · rw [sol_two_point _ hx2 hxy]
    have : 0 ≤ ∫ t in x..y, P (t - 1) / (t - 1) :=
      intervalIntegral.integral_nonneg hxy fun t ht => div_nonneg (P_pos _).le (by linarith [ht.1])
    linarith

lemma P_le_two {s : ℝ} (hs : 1 ≤ s) : P s ≤ 2 := by
  have := P_antitone (show (1 : ℝ) ∈ Ici 1 from self_mem_Ici) (show s ∈ Ici 1 from hs) hs
  rwa [sol_init _ (by norm_num : (1 : ℝ) ≤ 2)] at this

lemma P_step {s : ℝ} (hs : 2 ≤ s) : (s - 1) * P s ≤ P (s - 1) := by
  rw [P_avg hs]
  have : ∫ t in (s - 1)..s, P t ≤ ∫ t in (s - 1)..s, P (s - 1) :=
    intervalIntegral.integral_mono_on (by linarith) (P_cont.intervalIntegrable _ _)
      intervalIntegrable_const fun t ht =>
        P_antitone (show s - 1 ∈ Ici 1 by simp; linarith)
          (show t ∈ Ici 1 by simp; linarith [ht.1]) ht.1
  simpa using this

/-- **Decay of `P`.** -/
theorem P_decay {s : ℝ} (hs : 1 ≤ s) : P s ≤ 2 * Real.exp 5 * Real.exp (-s) := by
  have key : ∀ n : ℕ, ∀ s : ℝ, 1 ≤ s → s ≤ n → P s ≤ 2 * Real.exp 5 * Real.exp (-s) := by
    intro n
    induction n with
    | zero => intro s h1 h2; norm_num at h2; linarith
    | succ n ih =>
      intro s h1 h2
      rcases le_total s 5 with h5 | h5
      · have : 1 ≤ Real.exp 5 * Real.exp (-s) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
        have := P_le_two h1
        nlinarith
      · have hprev := ih (s - 1) (by linarith) (by push_cast at h2; linarith)
        have hstep := P_step (show 2 ≤ s by linarith)
        have he : Real.exp (-(s - 1)) = Real.exp 1 * Real.exp (-s) := by
          rw [← Real.exp_add]; ring_nf
        have he1 : Real.exp 1 ≤ 4 := by
          have := Real.exp_one_lt_d9; linarith
        have hpos : 0 < 2 * Real.exp 5 * Real.exp (-s) := by positivity
        have hPpos := P_pos s
        rw [he] at hprev
        nlinarith
  exact key ⌈s⌉₊ s hs (Nat.le_ceil s)

end LeanFormalizations.Erdos385.LinearSieve.Delay

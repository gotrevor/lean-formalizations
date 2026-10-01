/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.DelayP

/-!
# The Jurkat–Richert comparison functions from the delay equations (phase E5, step 4)

`Q = 2sω(s)` (Buchstab) and `P = m(s)` solve `Q' = Q(s−1)/(s−1)`, `P' = −P(s−1)/(s−1)` with
`Q = P = 2` on `(−∞, 2]`.  With `ω∞ = lim Q/(2s)` and `λ = C/ω∞`,
`α = λ(Q − P)/2`, `β = λ(Q + P)/2` are the scaled `Cs f(s)`, `Cs F(s)`.

Leaves:
* `delay_solution` (pure ODE analysis, believed 99%): existence, positivity
  (`(s−1)P(s) = ∫_{s−1}^s P`), and super-exponential convergence
  (`sω(s) = (s−1)ω(s−1) + ∫_{s−2}^{s−1} ω` makes `ω(s)` an average over the previous window;
  the oscillation contracts by `≈ 1/s` per unit step).
* `omega_le` (`ω∞ ≤ e^{−γ}`, i.e. `λ ≥ 1`; true with equality).  Route without Laplace transforms:
  the rough-number count `Φ(N, z)` (problem `r ≡ 0`, interval `[1, N]`) obeys the forward Buchstab
  identity with positive terms, `Φ ≥ π(N) − π(z) ~ N / log N` on `(1, 2]` (PNT), so its normalised
  liminf dominates `Q/2`; and `Φ ≤ S⁺`, whose normalisation is `≤ Cs + M e^{−s}`
  (`fundamental_lemma`).  Note: the pure-ODE statement below is a theorem about the number `ω∞`
  only; its proof must import that sieve input.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open MeasureTheory Set Filter

/-- `C = e^{−γ}`, the Mertens constant `∏_{p<z}(1−1/p) ~ C / log z`. -/
noncomputable def mertC : ℝ := Real.exp (-Real.eulerMascheroniConstant)

/-- The delay system data: `Q`, `P` with initial value `2` and the integrated equations. -/
def IsDelayPair (Q P : ℝ → ℝ) : Prop :=
  Continuous Q ∧ Continuous P ∧ (∀ s, s ≤ 2 → Q s = 2 ∧ P s = 2) ∧
  ∀ s s' : ℝ, 2 ≤ s → s ≤ s' →
    Q s' = Q s + ∫ t in s..s', Q (t - 1) / (t - 1) ∧
    P s = P s' + ∫ t in s..s', P (t - 1) / (t - 1)

/-- Leaf: positivity of `P = m` (route: `(s−1)P(s) = ∫_{s−1}^s P`, first-zero contradiction). -/
theorem solP_pos : ∀ s, 0 < Delay.sol (-1) s := Delay.P_pos

/-- Leaf: decay of `P` (route: `P(s) ≤ P(s−1)/(s−1)` from the same identity and `P` decreasing). -/
theorem solP_decay : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, 2 ≤ s → Delay.sol (-1) s ≤ M * Real.exp (-s) :=
  ⟨2 * Real.exp 5, by positivity, fun _ hs => Delay.P_decay (by linarith)⟩

/-- Leaf: `Q/(2s) → ω` exponentially (route: `u = Q/s` satisfies
`s u(s) = (s−1)u(s−1) + ∫_{s−2}^{s−1} u`; values stay in the hull of the previous two-window,
whose width `L` obeys `L(n+1) ≤ L(n−1)/(n−1) + L(n)/n`). -/
theorem solQ_conv : ∃ ω M : ℝ, 0 < ω ∧ 0 ≤ M ∧ ∀ s, 2 ≤ s →
    |Delay.sol 1 s - 2 * ω * s| ≤ M * Real.exp (-s) := by
  sorry

/-- Existence, positivity and exponential convergence of the delay pair. -/
theorem delay_solution : ∃ Q P : ℝ → ℝ, IsDelayPair Q P ∧ (∀ s, 0 < Q s ∧ 0 < P s) ∧
    ∃ ω M : ℝ, 0 < ω ∧ 0 ≤ M ∧ ∀ s, 2 ≤ s →
      |Q s - 2 * ω * s| ≤ M * Real.exp (-s) ∧ |P s| ≤ M * Real.exp (-s) := by
  obtain ⟨ω, M1, hω, hM1, hQ⟩ := solQ_conv
  obtain ⟨M2, hM2, hP⟩ := solP_decay
  refine ⟨Delay.sol 1, Delay.sol (-1), ⟨Delay.sol_continuous 1, Delay.sol_continuous (-1),
    fun s hs => ⟨Delay.sol_init 1 hs, Delay.sol_init (-1) hs⟩, fun s s' hs hss => ⟨?_, ?_⟩⟩,
    fun s => ⟨by linarith [Delay.solQ_ge_two s], solP_pos s⟩, ω, M1 + M2, hω, by positivity,
    fun s hs => ⟨?_, ?_⟩⟩
  · rw [Delay.sol_two_point 1 hs hss, one_mul]
  · rw [Delay.sol_two_point (-1) hs hss]; ring
  · have he := (Real.exp_pos (-s)).le
    exact (hQ s hs).trans (by nlinarith)
  · have he := (Real.exp_pos (-s)).le
    rw [abs_of_pos (solP_pos s)]
    exact (hP s hs).trans (by nlinarith)

/-- Leaf: `ω∞ ≤ e^{−γ}` (Buchstab's limit; equality is classical). -/
theorem omega_le : ∀ Q P : ℝ → ℝ, IsDelayPair Q P → ∀ ω M : ℝ, 0 < ω →
    (∀ s, 2 ≤ s → |Q s - 2 * ω * s| ≤ M * Real.exp (-s)) → ω ≤ mertC := by
  sorry

/-- **The Jurkat–Richert comparison functions** `α = Cs f(s)`, `β = Cs F(s)`. -/
theorem comparison_functions : ∃ α β : ℝ → ℝ, Continuous α ∧ Continuous β ∧
    (∀ s, 1 < s → s ≤ 2 → α s ≤ 0 ∧ 2 ≤ β s) ∧
    (∀ s s' : ℝ, 2 ≤ s → s ≤ s' →
      α s = α s' - ∫ t in s..s', β (t - 1) / (t - 1) ∧
      β s = β s' - ∫ t in s..s', α (t - 1) / (t - 1)) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 2 ≤ s →
      |α s - mertC * s| ≤ M * Real.exp (-s) ∧ |β s - mertC * s| ≤ M * Real.exp (-s)) ∧
    (∀ s, 2 < s → 0 < α s) := by
  obtain ⟨Q, P, hQP, hpos, ω, M, hω, hM, hdec⟩ := delay_solution
  obtain ⟨hQc, hPc, hinit, heq⟩ := hQP
  have hωC := omega_le Q P ⟨hQc, hPc, hinit, heq⟩ ω M hω fun s hs => (hdec s hs).1
  have hC : 0 < mertC := Real.exp_pos _
  set l := mertC / ω with hl
  have hl1 : 1 ≤ l := by rw [hl, le_div_iff₀ hω]; linarith
  have hlω : l * ω = mertC := by rw [hl]; field_simp
  have hl0 : 0 < l := by linarith
  -- integrability of the shifted quotients
  have hii : ∀ (f : ℝ → ℝ), Continuous f → ∀ s s', 2 ≤ s → s ≤ s' →
      IntervalIntegrable (fun t => f (t - 1) / (t - 1)) volume s s' := by
    intro f hf s s' hs hss
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div (hf.comp (continuous_id.sub continuous_const)).continuousOn
      (continuous_id.sub continuous_const).continuousOn fun t ht => ?_
    rw [uIcc_of_le hss] at ht
    show t - 1 ≠ 0; linarith [ht.1]
  refine ⟨fun s => l * (Q s - P s) / 2, fun s => l * (Q s + P s) / 2,
    by fun_prop, by fun_prop, ?_, ?_, ?_, ?_⟩
  · intro s _ hs2
    obtain ⟨h1, h2⟩ := hinit s hs2
    simp only [h1, h2]
    constructor <;> nlinarith
  · intro s s' hs hss
    obtain ⟨eQ, eP⟩ := heq s s' hs hss
    have iQ := hii Q hQc s s' hs hss
    have iP := hii P hPc s s' hs hss
    have hsplit : ∀ (c : ℝ) (σ : ℝ), (∫ t in s..s', l * (Q (t - 1) + σ * P (t - 1)) / 2 / (t - 1)) =
        l / 2 * ((∫ t in s..s', Q (t - 1) / (t - 1)) + σ * ∫ t in s..s', P (t - 1) / (t - 1)) := by
      intro _ σ
      calc (∫ t in s..s', l * (Q (t - 1) + σ * P (t - 1)) / 2 / (t - 1))
          = ∫ t in s..s', l / 2 * (Q (t - 1) / (t - 1) + σ * (P (t - 1) / (t - 1))) :=
            intervalIntegral.integral_congr fun t _ => by ring
        _ = l / 2 * ∫ t in s..s', (Q (t - 1) / (t - 1) + σ * (P (t - 1) / (t - 1))) :=
            intervalIntegral.integral_const_mul _ _
        _ = _ := by
            rw [intervalIntegral.integral_add iQ (iP.const_mul σ),
              intervalIntegral.integral_const_mul]
    have h1 := hsplit 0 1
    have h2 := hsplit 0 (-1)
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at h1 h2
    constructor
    · rw [h1]; beta_reduce; rw [eQ, eP]; ring
    · rw [h2]; beta_reduce; rw [eQ, eP]; ring
  · refine ⟨l / 2 * M + l / 2 * M, by positivity, fun s hs => ?_⟩
    obtain ⟨hq, hp⟩ := hdec s hs
    rw [abs_le] at hq hp
    have he := (Real.exp_pos (-s)).le
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith
  · intro s hs
    obtain ⟨eQ, eP⟩ := heq 2 s le_rfl hs.le
    obtain ⟨hQ2, hP2⟩ := hinit 2 le_rfl
    have iQ := hii Q hQc 2 s le_rfl hs.le
    have iP := hii P hPc 2 s le_rfl hs.le
    have hQi : 0 < ∫ t in (2:ℝ)..s, Q (t - 1) / (t - 1) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on iQ (fun t ht => ?_) hs
      exact div_pos (hpos _).1 (by linarith [ht.1])
    have hPi : 0 < ∫ t in (2:ℝ)..s, P (t - 1) / (t - 1) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on iP (fun t ht => ?_) hs
      exact div_pos (hpos _).2 (by linarith [ht.1])
    have : 0 < Q s - P s := by linarith
    positivity

end LeanFormalizations.Erdos385.LinearSieve

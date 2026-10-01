/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Deviation
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.ZeroContour

/-!
# Erdős #385 power saving: local zero detection (phase E9b, the crux)

**Why not `NearOneLargeValues`.**  The frozen `NearOneLargeValues` (PowerSaving.lean) asks, for
*every* smooth compactly supported weight `f`, that large values `‖vkDev f P t‖ ≥ P^{1−η}` number
`≪ T^{Bη^{3/2}} (log T)^C`.  The only known mechanism is the local explicit formula: a large value
at `t` forces a zero `ρ` with `β ≥ 1 − O(η)` and `|γ − t| ≤ L`, where `L` is the height at which
the Mellin tail `∫_{|u|>L} |mellin f(1+iu)| du` drops below `P^{−η}`.  A single zero at
`β = 1 − η/2` then produces `≍ L` large values around `γ`.  For a Gevrey weight
(`|mellin f(1+iu)| ≤ e^{−c|u|^α}`) `L` is polylogarithmic and the count is fine; but a general
`C_c^∞` weight can have Mellin decay as slow as `exp(−(log u)²)` (`SlowMellinWeight`), giving
`L = exp(√(η log P))`, which exceeds `T^{Bη^{3/2}}` once `η ≪ (log P)^{−1/2}`, a range VK does
not empty.  So `nearOneLargeValues_of_density` would need zero-free information beyond VK.  It
stays a disclosed hole, off the headline path (Maze row "NearOneLargeValues for every weight").

**What the headline needs** (`LargeValueCount`, LargeValueSum.lean) is only a count
`≪ (log Z)^C u^{−1/2} = (log P)^C P^{η/2}` at `P = √Z`, `u/2 = P^{−η}`.  A polynomial loss
`L ≍ P^{η/3}` is affordable.  That is `LocalZeroDetect` below; with `NearOneZeroDensity` it gives
`#large ≤ (2L+1)·2N(1 − 2η − o(1), 2T) ≪ P^{η/3 + O(η^{3/2})} (log P)^C ≤ P^{η/2}` for `η ≤ η₀`.

## Route for `localZeroDetect_of_richert` (contrapositive; PROVED 2026-10-01)

Suppose no zero has `Re ρ ≥ 1 − 3η₂/2` and `|Im ρ − t| ≤ L + 1`, where
`η₂ = η + 3 log log P / log P`, `L = (A/2) P^{η/3} log P`.  Write `G(s) = F(s) P^s H(s + it)`,
`F = mellin f`, `H = ζ'/ζ + 1/(w − 1)` (`zetaH`).  By V4 (`smoothTwist_sub_main_eq`),
`vkDev = −(1/2π) ∫_ℝ G(2 + iy) dy`.
1. **Tails on `Re s = 2`**, `|y| > P`: `≤ P² B · K/P³`.
2. **Shift `[c, 2] × [−P, P]`**, `c = 1 + 1/log P`: `|H| ≤ 3 log P` on `Re w ≥ c`
   (`logDeriv_zeta_dirichlet_bound`); horizontals `≤ 3K log P / P²`.
3. **Middle tails on `Re s = c`**, `L < |y| ≤ P`: `≤ 3e K P log P / L³` (`F ≪ y^{−4}`).
4. **Shift `[1 − η₂, c] × [−L, L]`**: by Landau's local lemma (`Landau.local_landau` on
   `closedBall (1 + η₂ + iy₀) (4η₂)`; growth from Richert for `σ ≤ 1` and PNT+ `ZetaUpperBnd` for
   `σ ≥ 1`, centre from PNT+ `ZetaLowerBound3`), `|H| ≤ K (log P)²` on the box.  Left side
   `≤ Kπ P^{1−η₂} (log P)² = Kπ P^{1−η} / log P`; horizontals `≤ K e P (log P)² / L⁴`.
Each piece is `≤ P^{1−η}/8` for `P ≥ P₀`, contradiction.
-/

namespace LeanFormalizations.Erdos385

open Real Complex LeanFormalizations.Literature

/-- **Local zero detection.**  A large deviation `‖vkDev f P t‖ ≥ P^{1−η}` of the smoothed prime
sum at a height `t` with `A P^{η/3} log P ≤ |t| ≤ P⁴` forces a zero of `ζ` with real part
`≥ 1 − 2η − A log log P / log P` within `A P^{η/3} log P / 2` of `t`.  The polynomial window
`P^{η/3}` is the price of a general `C^∞` weight (Mellin decay `≪ |u|^{−4}`); see the header. -/
def LocalZeroDetect : Prop :=
  ∀ f : ℝ → ℂ, (∀ k : ℕ, ContDiff ℝ k f) → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
    ∃ A P₀ : ℝ, 0 ≤ A ∧ ∀ P η t : ℝ, P₀ ≤ P → 0 < η → η ≤ 1 / 16 → |t| ≤ P ^ 4 →
      A * P ^ (η / 3) * Real.log P ≤ |t| →
      P ^ (1 - η) ≤ ‖vkDev f P t‖ →
      ∃ ρ : ℂ, riemannZeta ρ = 0 ∧
        1 - 2 * η - A * Real.log (Real.log P) / Real.log P ≤ ρ.re ∧
        |ρ.im - t| ≤ A * P ^ (η / 3) * Real.log P / 2

/-- The numerics of the contour assembly: the five pieces sum to `≤ 2u`, `u = P^{1−η}`. -/
lemma zc_numeric {K₃ K K₁ CH ℓ p u Ps Q c₁ : ℝ} (hK₃0 : 0 ≤ K₃) (hK0 : 0 ≤ K) (hK₁0 : 0 ≤ K₁)
    (hCH0 : 0 ≤ CH) (hℓ2 : 2 ≤ ℓ) (hp1 : 1 ≤ p) (hu0 : 0 < u) (hσ : Ps * ℓ ^ 3 = u)
    (hQ : Q = K₃ * Real.exp 1 * π * (2 + CH) / 8 + K * π * (12 * K₁ + 1) +
      K₃ * Real.exp 1 * (12 * K₁ + 1) / 32 + 1)
    (hc₁ : c₁ = K₃ * (2 + CH) * π + 2 * K₃ * (2 + CH) + 1) (hQℓ : Q ≤ ℓ) (hc₁ℓ : c₁ * ℓ ≤ u) :
    K₃ * |2 + CH| * π +
      (2 * (K₃ * (2 * ℓ + CH)) +
        (2 * (K₃ * (Real.exp 1 * (p ^ 3 * u)) * (2 * ℓ + CH) / (2 * p * ℓ) ^ 4 * π) +
          (K * Ps * (12 * K₁ * ℓ ^ 2 + 1) * π +
            2 * (K₃ * (Real.exp 1 * (p ^ 3 * u)) * (12 * K₁ * ℓ ^ 2 + 1) / (2 * p * ℓ) ^ 6)))) ≤
      2 * u := by
  have hℓ0 : 0 < ℓ := by linarith
  have hp0 : 0 < p := by linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hp34 : p ^ 3 ≤ p ^ 4 := pow_le_pow_right₀ hp1 (by norm_num)
  have hp36 : p ^ 3 ≤ p ^ 6 := pow_le_pow_right₀ hp1 (by norm_num)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by linarith
  have hℓ2' : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hℓ3 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hℓ5 : ℓ ^ 2 ≤ ℓ ^ 5 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hℓ6 : ℓ ^ 2 ≤ ℓ ^ 3 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have fr1 : (2 * ℓ + CH) * p ^ 3 / (p ^ 4 * ℓ ^ 4) ≤ (2 + CH) / ℓ := by
    rw [div_le_div_iff₀ (by positivity) hℓ0]
    have h1 : (2 * ℓ + CH) * ℓ ≤ (2 + CH) * ℓ ^ 4 := by
      have a := mul_le_mul_of_nonneg_left (hℓ2'.trans hℓ3) hCH0
      have e1 : (2 * ℓ + CH) * ℓ = 2 * ℓ ^ 2 + CH * ℓ := by ring
      have e2 : (2 + CH) * ℓ ^ 4 = 2 * ℓ ^ 4 + CH * ℓ ^ 4 := by ring
      rw [e1, e2]; linarith
    calc (2 * ℓ + CH) * p ^ 3 * ℓ = ((2 * ℓ + CH) * ℓ) * p ^ 3 := by ring
      _ ≤ ((2 + CH) * ℓ ^ 4) * p ^ 4 := by gcongr
      _ = (2 + CH) * (p ^ 4 * ℓ ^ 4) := by ring
  have fr2 : (12 * K₁ * ℓ ^ 2 + 1) / ℓ ^ 3 ≤ (12 * K₁ + 1) / ℓ := by
    rw [div_le_div_iff₀ (by positivity) hℓ0]
    have : 12 * K₁ * ℓ ^ 2 + 1 ≤ (12 * K₁ + 1) * ℓ ^ 2 := by nlinarith
    calc (12 * K₁ * ℓ ^ 2 + 1) * ℓ ≤ (12 * K₁ + 1) * ℓ ^ 2 * ℓ := by gcongr
      _ = (12 * K₁ + 1) * ℓ ^ 3 := by ring
  have fr3 : (12 * K₁ * ℓ ^ 2 + 1) * p ^ 3 / (p ^ 6 * ℓ ^ 6) ≤ (12 * K₁ + 1) / ℓ := by
    rw [div_le_div_iff₀ (by positivity) hℓ0]
    have : (12 * K₁ * ℓ ^ 2 + 1) * ℓ ≤ (12 * K₁ + 1) * ℓ ^ 6 := by
      have h36 : ℓ ^ 3 ≤ ℓ ^ 6 := pow_le_pow_right₀ hℓ1 (by norm_num)
      have h16 : ℓ ≤ ℓ ^ 6 := (pow_le_pow_right₀ hℓ1 (by norm_num) : ℓ ^ 1 ≤ ℓ ^ 6) |>.trans_eq' (pow_one ℓ)
      have a := mul_le_mul_of_nonneg_left h36 hK₁0
      have e1 : (12 * K₁ * ℓ ^ 2 + 1) * ℓ = 12 * (K₁ * ℓ ^ 3) + ℓ := by ring
      have e2 : (12 * K₁ + 1) * ℓ ^ 6 = 12 * (K₁ * ℓ ^ 6) + ℓ ^ 6 := by ring
      rw [e1, e2]; linarith
    calc (12 * K₁ * ℓ ^ 2 + 1) * p ^ 3 * ℓ = ((12 * K₁ * ℓ ^ 2 + 1) * ℓ) * p ^ 3 := by ring
      _ ≤ ((12 * K₁ + 1) * ℓ ^ 6) * p ^ 6 := by gcongr
      _ = (12 * K₁ + 1) * (p ^ 6 * ℓ ^ 6) := by ring
  have hT3 : 2 * (K₃ * (Real.exp 1 * (p ^ 3 * u)) * (2 * ℓ + CH) / (2 * p * ℓ) ^ 4 * π) ≤
      K₃ * Real.exp 1 * π / 8 * u * ((2 + CH) / ℓ) := by
    have e : 2 * (K₃ * (Real.exp 1 * (p ^ 3 * u)) * (2 * ℓ + CH) / (2 * p * ℓ) ^ 4 * π) =
        K₃ * Real.exp 1 * π / 8 * u * ((2 * ℓ + CH) * p ^ 3 / (p ^ 4 * ℓ ^ 4)) := by
      field_simp; ring
    rw [e]; gcongr
  have hT4 : K * Ps * (12 * K₁ * ℓ ^ 2 + 1) * π ≤ K * π * u * ((12 * K₁ + 1) / ℓ) := by
    have e : K * Ps * (12 * K₁ * ℓ ^ 2 + 1) * π = K * π * u * ((12 * K₁ * ℓ ^ 2 + 1) / ℓ ^ 3) := by
      rw [← hσ]; field_simp
    rw [e]; gcongr
  have hT5 : 2 * (K₃ * (Real.exp 1 * (p ^ 3 * u)) * (12 * K₁ * ℓ ^ 2 + 1) / (2 * p * ℓ) ^ 6) ≤
      K₃ * Real.exp 1 / 32 * u * ((12 * K₁ + 1) / ℓ) := by
    have e : 2 * (K₃ * (Real.exp 1 * (p ^ 3 * u)) * (12 * K₁ * ℓ ^ 2 + 1) / (2 * p * ℓ) ^ 6) =
        K₃ * Real.exp 1 / 32 * u * ((12 * K₁ * ℓ ^ 2 + 1) * p ^ 3 / (p ^ 6 * ℓ ^ 6)) := by
      field_simp; ring
    rw [e]; gcongr
  have hT12 : K₃ * |2 + CH| * π + 2 * (K₃ * (2 * ℓ + CH)) ≤ u := by
    rw [abs_of_nonneg (by positivity)]
    have : K₃ * (2 + CH) * π + 2 * (K₃ * (2 * ℓ + CH)) ≤ c₁ * ℓ := by
      rw [hc₁]
      have h1 : K₃ * (2 + CH) * π ≤ K₃ * (2 + CH) * π * ℓ := by
        have : 0 ≤ K₃ * (2 + CH) * π := by positivity
        nlinarith
      have h2 : 2 * (K₃ * (2 * ℓ + CH)) ≤ 2 * K₃ * (2 + CH) * ℓ := by
        have a := mul_le_mul_of_nonneg_left hℓ1 (mul_nonneg hK₃0 hCH0)
        have e1 : 2 * (K₃ * (2 * ℓ + CH)) = 4 * K₃ * ℓ + 2 * (K₃ * CH * 1) := by ring
        have e2 : 2 * K₃ * (2 + CH) * ℓ = 4 * K₃ * ℓ + 2 * (K₃ * CH * ℓ) := by ring
        rw [e1, e2]; linarith
      nlinarith
    linarith
  have hsum : (Q - 1) * (u / ℓ) ≤ u := by
    rw [mul_div_assoc', div_le_iff₀ hℓ0]
    have := mul_le_mul_of_nonneg_right (show Q - 1 ≤ ℓ by linarith) hu0.le
    linarith
  · 
    have e : (Q - 1) * (u / ℓ) = K₃ * Real.exp 1 * π / 8 * u * ((2 + CH) / ℓ) +
        K * π * u * ((12 * K₁ + 1) / ℓ) + K₃ * Real.exp 1 / 32 * u * ((12 * K₁ + 1) / ℓ) := by
      rw [hQ]; field_simp; ring
    linarith

set_option maxHeartbeats 1000000 in
/-- **Contour assembly** (contrapositive of local zero detection, `A = 8`). -/
theorem vkDev_lt_of_zeroFree (h : RichertZetaGrowth) {f : ℝ → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ Set.Ioi 0) :
    ∃ P₀ : ℝ, ∀ P η t : ℝ, P₀ ≤ P → 0 < η → η ≤ 1 / 16 → |t| ≤ P ^ 4 →
      8 * P ^ (η / 3) * Real.log P ≤ |t| →
      (∀ ρ : ℂ, riemannZeta ρ = 0 →
        1 - 2 * η - 8 * Real.log (Real.log P) / Real.log P ≤ ρ.re →
          4 * P ^ (η / 3) * Real.log P < |ρ.im - t|) →
      ‖vkDev f P t‖ < P ^ (1 - η) := by
  obtain ⟨a, b, ha, hab, hs⟩ := exists_support_Icc hc ht
  have hFd : Differentiable ℂ (mellin f) := mellin_differentiable (hf 0).continuous ha hs
  obtain ⟨K₃, hK₃0, hK₃⟩ := mellin_cube_decay hf ha hab hs
  obtain ⟨K, hK0, hK⟩ := mellin_pointwise hf ha hab hs
  obtain ⟨CH, hCH0, hCH⟩ := zetaH_bound_right
  obtain ⟨K₁, y₁, hK₁0, hloc⟩ := local_logDeriv_bound h
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = K₃ * Real.exp 1 * π * (2 + CH) / 8 + K * π * (12 * K₁ + 1) +
    K₃ * Real.exp 1 * (12 * K₁ + 1) / 32 + 1 := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = K₃ * (2 + CH) * π + 2 * K₃ * (2 + CH) + 1 := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.1
    (zc_eventually (y₁ := y₁) (Q := Q) ha (show 0 ≤ c₁ by rw [hc₁]; positivity))
  refine ⟨P₀, fun P η t hP hη hη16 ht4 hty hfree => ?_⟩
  obtain ⟨haP, hP16, hlam1, h48, hLP48, hy₁, hQℓ, hc₁ℓ⟩ := hP₀ P hP
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hℓe : Real.exp 1 ≤ Real.log P := by
    rwa [← Real.le_log_iff_exp_le (Real.log_pos (by linarith))]
  have hℓ2 : 2 ≤ Real.log P := by have := Real.exp_one_gt_d9; linarith
  have hℓ0 : 0 < Real.log P := by linarith
  have hpη : P ^ (η / 3) ≤ P ^ ((1 : ℝ) / 48) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hLP : 2 * P ^ (η / 3) * Real.log P ≤ P := by
    have : 2 * P ^ (η / 3) * Real.log P ≤ 2 * P ^ ((1 : ℝ) / 48) * Real.log P := by gcongr
    linarith
  have hbox0 := box_H_bound hK₁0 hloc hP16 hlam1 h48 hη hη16 ht4 hLP hty hy₁ hfree
  -- the V4 identity
  have hV4 := smoothTwist_sub_main_eq hf ha hab hs haP t
  have hdev : vkDev f P t = -((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, zcG f P t (2 + y * I) := hV4
  have hH₂ : ∀ w : ℂ, w.re = 2 → ‖zetaH w‖ ≤ 2 + CH := fun w hw => by
    have := hCH w (by rw [hw]; norm_num); rw [hw] at this; norm_num at this; exact this
  obtain ⟨hint, htail⟩ := zc_tail hFd hK₃0 hK₃ hH₂ (t := t) hP1
  have hsplit : (∫ y : ℝ, zcG f P t (2 + y * I)) =
      (∫ y in (-P)..P, zcG f P t (2 + y * I)) + ∫ y in (Set.Ioc (-P) P)ᶜ, zcG f P t (2 + y * I) := by
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_add_compl measurableSet_Ioc hint]
  -- the line `Re s = c`
  have hc1 : 1 < 1 + 1 / Real.log P := by have : 0 < 1 / Real.log P := by positivity
                                          linarith
  have hc2 : 1 + 1 / Real.log P ≤ 2 := by
    have : 1 / Real.log P ≤ 1 := by rw [div_le_one hℓ0]; linarith
    linarith
  have hHc : ∀ w : ℂ, 1 + 1 / Real.log P ≤ w.re → ‖zetaH w‖ ≤ 2 * Real.log P + CH := by
    intro w hw
    have h1 := hCH w (by linarith)
    have h2 : 2 / (w.re - 1) ≤ 2 * Real.log P := by
      rw [div_le_iff₀ (by linarith)]
      have : 1 ≤ Real.log P * (w.re - 1) := by
        rw [← div_le_iff₀' hℓ0]; linarith
      nlinarith
    linarith
  have hEq : P ^ (1 + 1 / Real.log P) = Real.exp 1 * P := by
    rw [Real.rpow_add hP0, Real.rpow_one, Real.rpow_def_of_pos hP0, mul_one_div_cancel hℓ0.ne',
      mul_comm]
  have hr1 := zc_rect1 hFd hK₃ (t := t) hc1 hc2 hP1 (fun w hw _ => hHc w hw)
  have hL0 : 0 < 2 * P ^ (η / 3) * Real.log P := by positivity
  have hr2 := zc_split hFd hK₃ (t := t) hc1 hc2 hP1 hL0 hLP hEq.le
    (fun w hw => hHc w hw.ge)
  have hlamℓ : 3 / Real.log P ≤ 3 * Real.log (Real.log P) / Real.log P :=
    div_le_div_of_nonneg_right (by linarith) hℓ0.le
  have hlam16 : 3 * Real.log (Real.log P) / Real.log P ≤ 1 / 16 := by
    rw [div_le_iff₀ hℓ0]; linarith
  have hiℓ : 0 < 1 / Real.log P := by positivity
  have hiℓ2 : 1 / Real.log P ≤ 1 / 2 := by rw [div_le_div_iff₀ hℓ0 (by norm_num)]; linarith
  have h3ℓ : 0 < 3 / Real.log P := by positivity
  have hr3 := zc_rect2 hFd (K := K) (H₁ := 12 * K₁ * Real.log P ^ 2 + 1) (E := Real.exp 1 * P)
    (fun s h1 h2 => (hK s h1 h2).1) hK₃
    (σ₁ := 1 - (η + 3 * Real.log (Real.log P) / Real.log P)) (c := 1 + 1 / Real.log P) (t := t)
    (by linarith) (by linarith) (by linarith) hc2 hP1 hL0 hEq.le
    (fun w h1 h2 h3 => hbox0 w h1 (by
      have : 1 / Real.log P ≤ 3 / Real.log P :=
        div_le_div_of_nonneg_right (by norm_num) hℓ0.le
      linarith) h3)
  have hnorm : ‖vkDev f P t‖ = 1 / (2 * π) * ‖∫ y : ℝ, zcG f P t (2 + y * I)‖ := by
    rw [hdev, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have htot : ‖∫ y : ℝ, zcG f P t (2 + y * I)‖ ≤ K₃ * |2 + CH| * π +
      (2 * (K₃ * (2 * Real.log P + CH)) +
        (2 * (K₃ * (Real.exp 1 * P) * (2 * Real.log P + CH) / (2 * P ^ (η / 3) * Real.log P) ^ 4 * π) +
          (K * P ^ (1 - (η + 3 * Real.log (Real.log P) / Real.log P)) *
              (12 * K₁ * Real.log P ^ 2 + 1) * π +
            2 * (K₃ * (Real.exp 1 * P) * (12 * K₁ * Real.log P ^ 2 + 1) /
              (2 * P ^ (η / 3) * Real.log P) ^ 6)))) := by
    rw [hsplit]
    have := norm_add_le (∫ y in (-P)..P, zcG f P t (2 + y * I))
      (∫ y in (Set.Ioc (-P) P)ᶜ, zcG f P t (2 + y * I))
    linarith
  -- numerics
  have hu0 : 0 < P ^ (1 - η) := by positivity
  have hsq : √P ≤ P ^ (1 - η) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hp1 : 1 ≤ P ^ (η / 3) := Real.one_le_rpow hP1 (by positivity)
  have hPu : P = (P ^ (η / 3)) ^ 3 * P ^ (1 - η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0]; norm_num
  have hσ : P ^ (1 - (η + 3 * Real.log (Real.log P) / Real.log P)) * Real.log P ^ 3 =
      P ^ (1 - η) := by
    have e1 : 1 - (η + 3 * Real.log (Real.log P) / Real.log P) =
        (1 - η) + -(3 * Real.log (Real.log P) / Real.log P) := by ring
    rw [e1, Real.rpow_add hP0, mul_assoc]
    have e2 : P ^ (-(3 * Real.log (Real.log P) / Real.log P)) * Real.log P ^ 3 = 1 := by
      rw [Real.rpow_def_of_pos hP0]
      have e3 : Real.log P * -(3 * Real.log (Real.log P) / Real.log P) =
          -(3 * Real.log (Real.log P)) := by field_simp
      rw [e3]
      conv_lhs => rw [← Real.exp_log hℓ0]
      rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast
      rw [Real.log_exp]; simp
    rw [e2, mul_one]
  generalize P ^ (1 - (η + 3 * Real.log (Real.log P) / Real.log P)) = Ps at htot hσ
  generalize P ^ (η / 3) = p at htot hPu hp1
  generalize P ^ (1 - η) = u at htot hPu hu0 hsq hσ hnorm ⊢
  generalize Real.log P = ℓ at htot hσ hQℓ hc₁ℓ hℓ2
  have hEP : Real.exp 1 * P = Real.exp 1 * (p ^ 3 * u) := by rw [← hPu]
  rw [hEP] at htot
  have hall := htot.trans (zc_numeric hK₃0 hK0 hK₁0 hCH0 hℓ2 hp1 hu0 hσ hQ hc₁ hQℓ
    (hc₁ℓ.trans hsq))
  rw [hnorm]
  have hπ : 1 < π := by linarith [Real.pi_gt_three]
  calc 1 / (2 * π) * ‖∫ y : ℝ, zcG f P t (2 + y * I)‖ ≤ 1 / (2 * π) * (2 * u) := by gcongr
    _ = u / π := by field_simp
    _ < u := div_lt_self hu0 hπ

/-- **The crux of phase E9b**: local zero detection from Richert's growth bound (route in the
header: V4 + two rectangle shifts + Landau's local lemma at scale `η₂`).  PROVED, `A = 8`. -/
theorem localZeroDetect_of_richert (h : RichertZetaGrowth) : LocalZeroDetect := by
  intro f hf hc ht
  obtain ⟨P₀, hP₀⟩ := vkDev_lt_of_zeroFree h hf hc ht
  refine ⟨8, P₀, by norm_num, fun P η t hP hη hη16 ht4 hty hdev => ?_⟩
  by_contra hno
  push Not at hno
  refine absurd hdev (not_le.2 (hP₀ P η t hP hη hη16 ht4 hty fun ρ hρ hre => ?_))
  have := hno ρ hρ hre
  linarith

/-- **The obstruction to `NearOneLargeValues` for every weight** (Maze anchor): a smooth weight
supported in `(0, ∞)` whose Mellin transform on `Re s = 1` beats every `C e^{−|u|^α}`
infinitely often.  Believed true (95%: sum of bumps at scales `2^{−k}` with weights `e^{−k²}`
gives decay `≍ exp(−(log u)²)`); not proved here.  With such a weight, one zero at
`β = 1 − η/2` makes `≍ exp(√(η log P))` large values, more than `T^{Bη^{3/2}}` for
`(log P)^{−2/3} ≪ η ≪ (log P)^{−1/2}`. -/
def SlowMellinWeight : Prop :=
  ∃ f : ℝ → ℂ, (∀ k : ℕ, ContDiff ℝ k f) ∧ HasCompactSupport f ∧ tsupport f ⊆ Set.Ioi 0 ∧
    ∀ α C : ℝ, 0 < α → ∃ u : ℝ, C * Real.exp (-|u| ^ α) < ‖mellin f (1 + u * I)‖

end LeanFormalizations.Erdos385

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.PNTFromVK.Kernel
import LeanFormalizations.NumberTheory.Erdos385.PNTFromVK.Contour
import LeanFormalizations.Literature.Erdos385VK

/-!
# Phase E3e helper: assembly of the de la Vallée Poussin PNT

At scale `x`, `L = log x`: `η = exp(−√L)`, `T = η^{−4} = exp(4√L)`, `X = 2x`, `c = 1 + 1/log X`,
weight `wt (e^η) B η` (lower support edge exactly `1`), `B = x e^{±η}`.

* Sandwich: `ψ(B e^{−η}) ≤ Re Σ Λ(n) wt(n) ≤ ψ(B e^η)` (`Λ(1) = 0`, `e^{2η} < 2`).
* Main term `∫ wt ∈ [B e^{−η} − e^{2η}, B e^η − 1]` (`mellin_wt_one`).
* Error (`contour_estimate`, `M = 4K₀`, `D = 2K₃ η^{−3}`): the tail is `≍ x η`, the horizontal
  sides are tiny, and the main line is `x · T · √L · exp(−(1−σ₁)L) ≪ x η` because
  `(1 − σ₁) L ≥ (4√L)^{−3/4} L ≍ L^{5/8} ≫ 5√L`.
-/

open Real Filter MeasureTheory Complex Asymptotics
open scoped Chebyshev

namespace LeanFormalizations.Erdos385.PNTVK

open LeanFormalizations.Erdos385 LeanFormalizations.Literature

/-- **Uniform Mellin bounds for the weight.** -/
theorem wt_mellin_bounds : ∃ K₀ K₃ : ℝ, 0 ≤ K₀ ∧ 0 ≤ K₃ ∧
    ∀ A B η X : ℝ, 0 < A → 0 < B → 0 < η → η ≤ 1 → A ≤ X → B ≤ X → ∀ s : ℂ, 1 / 2 ≤ s.re →
      s.re ≤ 2 →
      ‖mellin (wt A B η) s‖ ≤ 4 * K₀ * X ^ s.re ∧
      ‖mellin (wt A B η) s‖ * |s.im| ^ 4 ≤ 2 * K₃ * η⁻¹ ^ 3 * X ^ s.re := by
  sorry

/-- **The sandwich.**  With lower edge `A = e^η` (`η ≤ 1/4`), the weighted prime sum lies between
`ψ(B e^{−η})` and `ψ(B e^η)`. -/
theorem smoothTwist_wt_sandwich {B η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hB : Real.exp η ≤ B) :
    (smoothTwist (wt (Real.exp η) B η) 1 0).im = 0 ∧
      ψ (B * Real.exp (-η)) ≤ (smoothTwist (wt (Real.exp η) B η) 1 0).re ∧
      (smoothTwist (wt (Real.exp η) B η) 1 0).re ≤ ψ (B * Real.exp η) := by
  sorry

/-- **The main-line exponent beats `5√L`.** -/
theorem mainLine_eventually :
    ∀ᶠ L : ℝ in atTop, Real.sqrt L * Real.exp (5 * Real.sqrt L -
      (4 * Real.sqrt L) ^ (-(3 / 4 : ℝ)) * L) ≤ 1 := by
  sorry

/-- **PNT with error `x η`, `η = exp(−√log x)`.** -/
theorem psi_sub_le (h : VKZeroFreeLogDeriv) :
    ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |ψ x - x| ≤ K * (x * Real.exp (-Real.sqrt (Real.log x))) := by
  sorry

theorem dlvp_of_VK (h : VKZeroFreeLogDeriv) : DLVPStatement := by
  obtain ⟨K, hK⟩ := psi_sub_le h
  refine ⟨1, one_pos, IsBigO.of_bound K ?_⟩
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x * Real.exp (-1 * Real.sqrt (Real.log x)) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0]
  simpa only [Pi.sub_apply, id, neg_mul, one_mul] using hx

end LeanFormalizations.Erdos385.PNTVK

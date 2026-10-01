/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Log-coordinate change of variables, as an upper bound

`∫⁻_{[L,U]} ‖G(log v)‖² v^k dv ≤ U^{k+1} ∫⁻ ‖G‖²`, from `v = e^u`, `dv = e^u du`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Erdos385.Parseval

theorem lintegral_log_le {G : ℝ → ℂ} (k : ℕ) {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) :
    ∫⁻ v in Icc L U, ‖G (Real.log v)‖ₑ ^ 2 * ENNReal.ofReal (v ^ k) ≤
      ENNReal.ofReal (U ^ (k + 1)) * ∫⁻ u, ‖G u‖ₑ ^ 2 := by
  set g : ℝ → ℝ≥0∞ := (Icc L U).indicator fun v ↦ ‖G (Real.log v)‖ₑ ^ 2 * ENNReal.ofReal (v ^ k)
  have hsub : Icc L U ⊆ Real.exp '' univ := by
    rw [image_univ, Real.range_exp]
    exact fun v hv ↦ lt_of_lt_of_le hL hv.1
  have h1 : ∫⁻ v in Icc L U, ‖G (Real.log v)‖ₑ ^ 2 * ENNReal.ofReal (v ^ k) =
      ∫⁻ v in Real.exp '' univ, g v := by
    rw [setLIntegral_indicator measurableSet_Icc, inter_eq_left.mpr hsub]
  rw [h1, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn g,
    Measure.restrict_univ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun u ↦ ?_
  simp only [g]
  by_cases hu : Real.exp u ∈ Icc L U
  · rw [indicator_of_mem hu, Real.log_exp, abs_of_pos (Real.exp_pos u)]
    have he : ENNReal.ofReal (Real.exp u) * ENNReal.ofReal (Real.exp u ^ k) ≤
        ENNReal.ofReal (U ^ (k + 1)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos u).le]
      apply ENNReal.ofReal_le_ofReal
      rw [pow_succ']
      exact mul_le_mul hu.2 (pow_le_pow_left₀ (Real.exp_pos u).le hu.2 k) (by positivity)
        (by linarith [hu.1])
    calc _ = ‖G u‖ₑ ^ 2 * (ENNReal.ofReal (Real.exp u) * ENNReal.ofReal (Real.exp u ^ k)) := by
            ring
      _ ≤ ‖G u‖ₑ ^ 2 * ENNReal.ofReal (U ^ (k + 1)) := by gcongr
      _ = _ := mul_comm _ _
  · rw [indicator_of_notMem hu, mul_zero]; exact zero_le

end Erdos385.Parseval

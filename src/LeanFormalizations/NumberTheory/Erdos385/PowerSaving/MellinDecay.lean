/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll

/-!
# Erdős #385 power saving: second-order Mellin decay on `Re s = 1` (phase E9b)

`mellin_decay_two`: for `C²` `f` supported in `(a, b) ⊂ (0, ∞)`,
`|mellin f (1 − it)| t² ≤ K`, from `mellin_xDeriv` (`mellin (x f') s = −s mellin f s`) and the
first-order bound `mellin_one_sub_mul_I_decay` applied to `x f'`.
-/

namespace LeanFormalizations.Erdos385

open Complex

theorem mellin_decay_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ x, f x ≠ 0 → a < x ∧ x < b) :
    ∃ K : ℝ, ∀ t : ℝ, ‖mellin f (1 - t * I)‖ * t ^ 2 ≤ K := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' (n := 1) (by exact hf)
  have hxD : ContDiff ℝ 1 (xDeriv f) := by
    unfold xDeriv
    exact (ofRealCLM.contDiff).mul hd
  have hts : tsupport f ⊆ Set.Icc a b :=
    closure_minimal (fun x hx => ⟨(hs x hx).1.le, (hs x hx).2.le⟩) isClosed_Icc
  have hsD : ∀ x, xDeriv f x ≠ 0 → a / 2 < x ∧ x < b + 1 := by
    intro x hx
    have : deriv f x ≠ 0 := fun h => hx (by simp [xDeriv, h])
    have := hts (support_deriv_subset this)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  obtain ⟨K, hK⟩ := mellin_one_sub_mul_I_decay hxD (by positivity : 0 < a / 2)
    (by linarith : a / 2 ≤ b + 1) hsD
  refine ⟨K, fun t => ?_⟩
  set s : ℂ := 1 - t * I with hsdef
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hsdef] at this
  have heq := mellin_xDeriv hf1 ha hab (fun x hx => ⟨(hs x hx).1.le, (hs x hx).2.le⟩) hs0
  have hst : |t| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    simpa [hsdef] using this
  have h1 := hK t
  rw [heq, norm_neg, norm_mul] at h1
  have ht2 : t ^ 2 = |t| * |t| := by rw [abs_mul_abs_self t]; ring
  rw [ht2]
  calc ‖mellin f s‖ * (|t| * |t|) ≤ ‖mellin f s‖ * (‖s‖ * |t|) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right hst (abs_nonneg t)
    _ = ‖s‖ * ‖mellin f s‖ * |t| := by ring
    _ ≤ K := h1

end LeanFormalizations.Erdos385

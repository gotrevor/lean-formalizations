/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385, phase E4: the three terms of `bad_count_le`, as pure real inequalities
-/

namespace LeanFormalizations.Erdos385.Exceptional

/-- Small `n`: `R + y ≤ X e^{−L^θ}` once `2 log L + L^θ ≤ L`, `L = log X`. -/
theorem term1_le {X L y E : ℝ} (hX : 0 < X) (hL : L = Real.log X) (hL1 : 1 ≤ L)
    (hy0 : 0 ≤ y) (hy : y ≤ L / 8) (hE : 2 * Real.log L + E ≤ L) :
    y ^ 2 + y ≤ X * Real.exp (-E) := by
  have h1 : y ^ 2 + y ≤ L ^ 2 := by nlinarith
  have hX' : X = Real.exp L := by rw [hL, Real.exp_log hX]
  have h2 : L ^ 2 = Real.exp (2 * Real.log L) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring, Real.exp_add,
      Real.exp_log (by linarith)]
    ring
  rw [hX', ← Real.exp_add]
  calc y ^ 2 + y ≤ L ^ 2 := h1
    _ = Real.exp (2 * Real.log L) := h2
    _ ≤ Real.exp (L + -E) := Real.exp_le_exp.2 (by linarith)

/-- Tail term: `P e^{−u} (X/P + 1) ≤ 2 X e^{−E}` when `P ≤ X`, `E ≤ u`. -/
theorem term2_le {P X u E T : ℝ} (hP : 0 < P) (hPX : P ≤ X) (hEu : E ≤ u)
    (hT : T ≤ P * Real.exp (-u)) (hT0 : 0 ≤ T) :
    T * (X / P + 1) ≤ 2 * X * Real.exp (-E) := by
  have h1 : T * (X / P + 1) ≤ P * Real.exp (-u) * (X / P + 1) :=
    mul_le_mul_of_nonneg_right hT (by
      have : 0 ≤ X / P := div_nonneg (by linarith) hP.le
      linarith)
  have h2 : P * Real.exp (-u) * (X / P + 1) = Real.exp (-u) * (X + P) := by
    field_simp
  have h3 : Real.exp (-u) ≤ Real.exp (-E) := Real.exp_le_exp.2 (by linarith)
  have h4 : 0 ≤ X + P := by linarith
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ Real.exp (-E) * (X + P) := mul_le_mul_of_nonneg_right h3 h4
    _ ≤ Real.exp (-E) * (2 * X) := by gcongr; linarith
    _ = _ := by ring

/-- Sieved term: `P (X + Q²) / (Pr · W) ≤ 2 X e^{−E}` when `P ≤ y Pr`, `Q² ≤ X`,
`W ≥ e^{2E}`, `y ≤ e^E`. -/
theorem term3_le {P X Q2 y Pr W E : ℝ} (hP : 0 < P) (hy : 0 < y) (hPr : P ≤ y * Pr)
    (hQ : Q2 ≤ X) (hQ0 : 0 ≤ Q2) (hX : 0 ≤ X) (hW : Real.exp (2 * E) ≤ W) (hyE : y ≤ Real.exp E) :
    P * ((X + Q2) / (Pr * W)) ≤ 2 * X * Real.exp (-E) := by
  have hPr0 : 0 < Pr := by
    by_contra h; push Not at h; nlinarith
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos _) hW
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have h1 : P * (X + Q2) ≤ y * Pr * (2 * X) := by
    have : X + Q2 ≤ 2 * X := by linarith
    calc P * (X + Q2) ≤ (y * Pr) * (X + Q2) := mul_le_mul_of_nonneg_right hPr (by linarith)
      _ ≤ y * Pr * (2 * X) := by gcongr
  have h2 : y ≤ Real.exp (-E) * W := by
    calc y ≤ Real.exp E := hyE
      _ = Real.exp (-E) * Real.exp (2 * E) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-E) * W := by gcongr
  calc P * (X + Q2) ≤ y * Pr * (2 * X) := h1
    _ ≤ (Real.exp (-E) * W) * Pr * (2 * X) := by gcongr
    _ = _ := by ring

end LeanFormalizations.Erdos385.Exceptional

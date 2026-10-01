/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Low
import LeanFormalizations.NumberTheory.Erdos385.Parseval.LogChange

/-!
# The high band: a pure `L²` bound on window differences

`∫⁻_{[X,2X]} ‖D g‖² ≤ 280 X³/h₁² ∫⁻ ‖g‖²` for any measurable `g`, `0 < h₁ ≤ h₂ ≤ X`.
-/

open MeasureTheory Complex Set
open scoped ENNReal

noncomputable section

namespace Erdos385.Parseval

/-- `∫⁻_{[X,2X]} ‖(x+h) g(log(x+h))‖² ≤ (3X)³ ∫⁻ ‖g‖²`. -/
lemma lintegral_shift_le {g : ℝ → ℂ} {X h : ℝ} (hX : 0 < X) (hh : 0 ≤ h) (hhX : h ≤ X) :
    ∫⁻ x in Icc X (2 * X), ‖((x + h : ℝ) : ℂ) * g (Real.log (x + h))‖ₑ ^ 2 ≤
      ENNReal.ofReal ((3 * X) ^ 3) * ∫⁻ u, ‖g u‖ₑ ^ 2 := by
  set F : ℝ → ℝ≥0∞ := fun v ↦ ‖g (Real.log v)‖ₑ ^ 2 * ENNReal.ofReal (v ^ 2)
  have hF : ∀ v, ‖((v : ℝ) : ℂ) * g (Real.log v)‖ₑ ^ 2 = F v := by
    intro v
    simp only [F, enorm_mul, mul_pow]
    rw [mul_comm]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs]
  simp_rw [hF]
  calc ∫⁻ x in Icc X (2 * X), F (x + h)
      = ∫⁻ x, (Icc (X + h) (2 * X + h)).indicator F (x + h) := by
        rw [← lintegral_indicator measurableSet_Icc]
        congr 1 with x
        by_cases hx : x ∈ Icc X (2 * X)
        · rw [indicator_of_mem hx, indicator_of_mem (by constructor <;> linarith [hx.1, hx.2])]
        · rw [indicator_of_notMem hx, indicator_of_notMem (fun h' ↦ hx
            ⟨by linarith [h'.1], by linarith [h'.2]⟩)]
    _ = ∫⁻ v, (Icc (X + h) (2 * X + h)).indicator F v :=
        lintegral_add_right_eq_self _ h
    _ ≤ ∫⁻ v in Icc X (3 * X), F v := by
        rw [← lintegral_indicator measurableSet_Icc]
        refine lintegral_mono fun v ↦ ?_
        by_cases hv : v ∈ Icc (X + h) (2 * X + h)
        · rw [indicator_of_mem hv, indicator_of_mem (show v ∈ Icc X (3 * X) from
            ⟨by linarith [hv.1], by linarith [hv.2]⟩)]
        · rw [indicator_of_notMem hv]; exact zero_le
    _ ≤ _ := lintegral_log_le 2 hX (by linarith)

/-- **High band.**  A pure `L²` bound on the window difference. -/
theorem lintegral_winDif_le {g : ℝ → ℂ} (hg : Measurable g) {X h₁ h₂ : ℝ} (hX : 0 < X)
    (hh₁ : 0 < h₁) (h12 : h₁ ≤ h₂) (h2X : h₂ ≤ X) :
    ∫⁻ x in Icc X (2 * X), ‖winDif g h₁ h₂ x‖ₑ ^ 2 ≤
      ENNReal.ofReal (432 * X ^ 3 / h₁ ^ 2) * ∫⁻ u, ‖g u‖ₑ ^ 2 := by
  have hh₂ : 0 < h₂ := hh₁.trans_le h12
  set A : ℝ → ℝ → ℂ := fun h x ↦ ((x + h : ℝ) : ℂ) * g (Real.log (x + h))
  have hA : ∀ h, Measurable fun x ↦ ‖A h x‖ₑ ^ 2 := fun h ↦ by
    simp only [A]; fun_prop
  have hpt : ∀ x, ‖winDif g h₁ h₂ x‖ₑ ^ 2 ≤ ENNReal.ofReal (4 / h₁ ^ 2) *
      (‖A h₁ x‖ₑ ^ 2 + 2 * ‖A 0 x‖ₑ ^ 2 + ‖A h₂ x‖ₑ ^ 2) := by
    intro x
    have e0 : A 0 x = (x : ℂ) * g (Real.log x) := by simp [A]
    have hreal : ‖winDif g h₁ h₂ x‖ ^ 2 ≤ 4 / h₁ ^ 2 *
        (‖A h₁ x‖ ^ 2 + 2 * ‖A 0 x‖ ^ 2 + ‖A h₂ x‖ ^ 2) := by
      have t1 : ‖winDelta g x h₁ / h₁‖ ≤ (‖A h₁ x‖ + ‖A 0 x‖) / h₁ := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh₁]
        gcongr
        rw [winDelta, ← e0]; exact norm_sub_le _ _
      have t2 : ‖winDelta g x h₂ / h₂‖ ≤ (‖A h₂ x‖ + ‖A 0 x‖) / h₁ := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh₂]
        calc ‖winDelta g x h₂‖ / h₂ ≤ (‖A h₂ x‖ + ‖A 0 x‖) / h₂ := by
              gcongr; rw [winDelta, ← e0]; exact norm_sub_le _ _
          _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hh₁ h12
      have t3 : ‖winDif g h₁ h₂ x‖ ≤ (‖A h₁ x‖ + 2 * ‖A 0 x‖ + ‖A h₂ x‖) / h₁ := by
        unfold winDif
        refine (norm_sub_le _ _).trans ?_
        calc _ ≤ (‖A h₁ x‖ + ‖A 0 x‖) / h₁ + (‖A h₂ x‖ + ‖A 0 x‖) / h₁ := add_le_add t1 t2
          _ = _ := by ring
      have := pow_le_pow_left₀ (norm_nonneg _) t3 2
      refine this.trans ?_
      rw [div_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [sq_nonneg (‖A h₁ x‖ - ‖A 0 x‖), sq_nonneg (‖A h₂ x‖ - ‖A 0 x‖),
        sq_nonneg (‖A h₁ x‖ - ‖A h₂ x‖)]
    have conv : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z ↦ by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [conv, conv, conv, conv, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hb : ∀ h, 0 ≤ h → h ≤ X → ∫⁻ x in Icc X (2 * X), ‖A h x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((3 * X) ^ 3) * ∫⁻ u, ‖g u‖ₑ ^ 2 := fun h h0 hX' ↦
    lintegral_shift_le hX h0 hX'
  calc ∫⁻ x in Icc X (2 * X), ‖winDif g h₁ h₂ x‖ₑ ^ 2
      ≤ ∫⁻ x in Icc X (2 * X), ENNReal.ofReal (4 / h₁ ^ 2) *
          (‖A h₁ x‖ₑ ^ 2 + 2 * ‖A 0 x‖ₑ ^ 2 + ‖A h₂ x‖ₑ ^ 2) := lintegral_mono hpt
    _ = ENNReal.ofReal (4 / h₁ ^ 2) * ((∫⁻ x in Icc X (2 * X), ‖A h₁ x‖ₑ ^ 2) +
          2 * (∫⁻ x in Icc X (2 * X), ‖A 0 x‖ₑ ^ 2) +
          ∫⁻ x in Icc X (2 * X), ‖A h₂ x‖ₑ ^ 2) := by
        rw [lintegral_const_mul _ (((hA h₁).add ((hA 0).const_mul 2)).add (hA h₂)),
          lintegral_add_left ((hA h₁).add ((hA 0).const_mul 2)),
          lintegral_add_left (hA h₁), lintegral_const_mul _ (hA 0)]
    _ ≤ ENNReal.ofReal (4 / h₁ ^ 2) * (ENNReal.ofReal ((3 * X) ^ 3) * (∫⁻ u, ‖g u‖ₑ ^ 2) +
          2 * (ENNReal.ofReal ((3 * X) ^ 3) * (∫⁻ u, ‖g u‖ₑ ^ 2)) +
          ENNReal.ofReal ((3 * X) ^ 3) * (∫⁻ u, ‖g u‖ₑ ^ 2)) := by
        gcongr
        · exact hb h₁ hh₁.le (h12.trans h2X)
        · exact hb 0 le_rfl hX.le
        · exact hb h₂ hh₂.le h2X
    _ = ENNReal.ofReal (432 * X ^ 3 / h₁ ^ 2) * ∫⁻ u, ‖g u‖ₑ ^ 2 := by
        rw [show ENNReal.ofReal (432 * X ^ 3 / h₁ ^ 2) =
          ENNReal.ofReal (4 / h₁ ^ 2) * (4 * ENNReal.ofReal ((3 * X) ^ 3)) by
            rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring]
        ring

end Erdos385.Parseval

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import PrimeNumberTheoremAnd.ZetaConj
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.ZeroDetect
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.FiberCount

/-!
# Erdős #385 power saving: `LargeValueCount` from local zero detection (phase E9b)

`largeValueCount_of_zeroDetect`: `LocalZeroDetect` + `NearOneZeroDensity` ⇒ `LargeValueCount δ`.

Route (85%).  `P = √Z`, `u ∈ [Z^{−η₀}, 1]`, `η := log(2/u)/log P` (so `P u/2 = P^{1−η}`,
`η ≤ 2η₀ + log 2/log P ≤ 1/16`).  Points with `|t| < max(R', A P^{η/3} log P)`,
`R' = 2√(Km/u)` (`dev_lower`'s threshold) are `1`-separated in a short interval: `≪ u^{−1/2}`
and `≪ P^{η/3} log P ≤ u^{−1/2} log P`.  Every other point has `‖vkDev‖ ≥ P^{1−η}`
(`dev_lower`), hence (`LocalZeroDetect`) a zero `ρ_t` with `Re ≥ σ := 1 − 2η − A log log P/log P`
and `|Im ρ_t − t| ≤ |t|/2`; replace `ρ_t` by `conj ρ_t` when `t < 0` (`riemannZeta_conj`), so
`0 < Im ≤ 2T`.  Fibres of `t ↦ ρ_t` have `≤ 2(A P^{η/3} log P + 1)` points (`1`-separation),
and `NearOneZeroDensity` at `(σ, 2T)`, `T = 8X ≤ 8Z`, bounds the image by
`C (16Z)^{B(1−σ)^{3/2}} log^C(16Z)`; `(1−σ)^{3/2} ≤ 2(2η)^{3/2} + 2(A log log P/log P)^{3/2}`, the
second term costing `O(1)` in the exponent, the first `P^{O(η^{3/2})} ≤ P^{η/6}` for `η ≤ η₀`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter Complex LeanFormalizations.Literature Erdos385.Parseval

/-- **The density exponent**: with `x = 2η`, `y = A log ℓ/ℓ`, `x + y ≤ s₀²`, `8B s₀ ≤ 1/6`:
`(12P²)^{B(x+y)^{3/2}} ≤ (P^η)^{1/6} ℓ^{4AB}`. -/
lemma zc_density_exp {B A P η y s₀ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hP : 1 < P)
    (hP12 : 12 * P ^ 2 ≤ P ^ 4) (hη : 0 ≤ η) (hy : 0 ≤ y) (hs₀ : 0 ≤ s₀) (hs₀1 : s₀ ≤ 1)
    (hsum : 2 * η + y ≤ s₀ ^ 2) (hBs : 8 * B * s₀ ≤ 1 / 6)
    (hyℓ : y * Real.log P = A * Real.log (Real.log P)) (hℓ : 0 < Real.log P) :
    (12 * P ^ 2) ^ (B * (2 * η + y) ^ ((3 : ℝ) / 2)) ≤
      (P ^ η) ^ ((1 : ℝ) / 6) * Real.log P ^ (4 * A * B) := by
  have hP0 : 0 < P := by linarith
  have hxy : 0 ≤ 2 * η + y := by linarith
  have h32 : (2 * η + y) ^ ((3 : ℝ) / 2) ≤ 2 * η * s₀ + y := by
    have e : (2 * η + y) ^ ((3 : ℝ) / 2) = (2 * η + y) * (2 * η + y) ^ ((1 : ℝ) / 2) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hxy (by norm_num),
        Real.rpow_one]
    have hs : (2 * η + y) ^ ((1 : ℝ) / 2) ≤ s₀ := by
      rw [← Real.sqrt_eq_rpow]
      calc √(2 * η + y) ≤ √(s₀ ^ 2) := Real.sqrt_le_sqrt hsum
        _ = s₀ := Real.sqrt_sq hs₀
    rw [e]
    calc (2 * η + y) * (2 * η + y) ^ ((1 : ℝ) / 2) ≤ (2 * η + y) * s₀ :=
          mul_le_mul_of_nonneg_left hs hxy
      _ = 2 * η * s₀ + y * s₀ := by ring
      _ ≤ 2 * η * s₀ + y := by nlinarith
  have hexp0 : 0 ≤ B * (2 * η + y) ^ ((3 : ℝ) / 2) := by positivity
  calc (12 * P ^ 2) ^ (B * (2 * η + y) ^ ((3 : ℝ) / 2))
      ≤ (P ^ 4) ^ (B * (2 * η + y) ^ ((3 : ℝ) / 2)) :=
        Real.rpow_le_rpow (by positivity) hP12 hexp0
    _ = P ^ (4 * (B * (2 * η + y) ^ ((3 : ℝ) / 2))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; norm_num
    _ ≤ P ^ (4 * (B * (2 * η * s₀ + y))) := by
        apply Real.rpow_le_rpow_of_exponent_le hP.le
        have := mul_le_mul_of_nonneg_left h32 hB
        linarith
    _ = P ^ (8 * B * s₀ * η) * P ^ (4 * B * y) := by
        rw [← Real.rpow_add hP0]; ring_nf
    _ ≤ P ^ (η / 6) * P ^ (4 * B * y) := by
        gcongr
        · exact hP.le
        · nlinarith
    _ = (P ^ η) ^ ((1 : ℝ) / 6) * Real.log P ^ (4 * A * B) := by
        have e1 : P ^ (η / 6) = (P ^ η) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_mul hP0.le]; ring_nf
        have e2 : P ^ (4 * B * y) = Real.log P ^ (4 * A * B) := by
          rw [Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos hℓ]
          congr 1
          have : Real.log P * (4 * B * y) = 4 * B * (y * Real.log P) := by ring
          rw [this, hyℓ]; ring
        rw [e1, e2]

/-- **The large-value count from zeros.** -/
theorem largeValueCount_of_zeroDetect (hZ : LocalZeroDetect) (h2 : NearOneZeroDensity) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) : LargeValueCount δ := by
  sorry

end LeanFormalizations.Erdos385

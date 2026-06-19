/-
# The Córdoba `L²` denominator — harmonic double-sum bound (ladder K4)

The Córdoba estimate lower-bounds `vol(Sδ)` by Cauchy–Schwarz against `f = ∑ₖ 1_{Tₖ}` over the
δ-separated tube family of K3. Its **denominator** is

  `∫ f² = ∑_{j,k} vol(Tⱼ ∩ Tₖ) ≤ 6π δ · ∑_{j,k} 1/(|k−j|+1)`   (by `volume_inter_dirTube_le`).

This file proves the purely combinatorial heart of that denominator: the double sum of the
harmonic profile `1/(|k−j|+1)` over an `n × n` index block is `≤ 2 n · Hₙ ≤ 2 n (1 + log n)`.
With `n ≈ δ⁻¹` this is the `δ⁻¹ · log(1/δ)` factor that — multiplied by the `6π δ` from the K2
overlap bound — yields the `δ · log(1/δ)` `L²` mass, hence `vol(Sδ) ≳ 1/log(1/δ)`.

The key estimate is per-row: for each fixed `j`, the two "arms" `k < j` and `k ≥ j` each contribute
at most `Hₙ` (each reciprocal value is realised at most twice across the row). `mathlib`'s
`harmonic_le_one_add_log` then converts `Hₙ` to `1 + log n`.

Reference: A. Córdoba (1977). See `PLAN.md` (K4).
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Directions
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset
open scoped Real

namespace LeanFormalizations.Kakeya2D

/-- The harmonic number as a real sum of reciprocals `∑_{i<n} 1/(i+1)`. -/
theorem harmonic_real (n : ℕ) :
    (harmonic n : ℝ) = ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) := by
  rw [harmonic, Rat.cast_sum]
  apply sum_congr rfl
  intro i _
  push_cast
  rw [one_div]

/-- **Per-row bound.** For each fixed index `j < n`, the harmonic-profile row
`∑_{k<n} 1/(|k−j|+1)` is at most `2 Hₙ`: split at `j` into the right arm `k ≥ j` (reindex
`k = j+i`, giving `∑_{i<n−j} 1/(i+1) ≤ Hₙ`) and the left arm `k < j` (reflect, giving
`∑_{k<j} 1/(k+2) ≤ Hₙ`). -/
theorem inner_sum_le {n j : ℕ} (hj : j < n) :
    ∑ k ∈ range n, (1 : ℝ) / (|(k : ℝ) - j| + 1) ≤ 2 * (harmonic n : ℝ) := by
  rw [harmonic_real, two_mul,
    ← sum_range_add_sum_Ico (fun k => (1 : ℝ) / (|(k : ℝ) - (j : ℝ)| + 1)) hj.le]
  apply add_le_add
  · -- left arm: k < j, distance j − k, reflect to 1/(k+2)
    calc ∑ k ∈ range j, (1 : ℝ) / (|(k : ℝ) - (j : ℝ)| + 1)
        = ∑ k ∈ range j, (1 : ℝ) / ((k : ℝ) + 2) := by
          rw [← sum_range_reflect (fun k => (1 : ℝ) / (|(k : ℝ) - (j : ℝ)| + 1)) j]
          apply sum_congr rfl
          intro k hk
          rw [mem_range] at hk
          have hcast : ((j - 1 - k : ℕ) : ℝ) - (j : ℝ) = -((k : ℝ) + 1) := by
            have hk1 : k ≤ j - 1 := by omega
            have hj1 : 1 ≤ j := by omega
            rw [Nat.cast_sub hk1, Nat.cast_sub hj1, Nat.cast_one]
            ring
          rw [hcast, abs_neg, abs_of_nonneg (by positivity)]
          ring_nf
      _ ≤ ∑ k ∈ range j, (1 : ℝ) / ((k : ℝ) + 1) := by
          apply sum_le_sum
          intro k _
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) :=
          sum_le_sum_of_subset_of_nonneg
            (fun x hx => mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx) hj.le))
            (fun i _ _ => by positivity)
  · -- right arm: k ≥ j, distance k − j, reindex to 1/(i+1)
    calc ∑ k ∈ Ico j n, (1 : ℝ) / (|(k : ℝ) - (j : ℝ)| + 1)
        = ∑ i ∈ range (n - j), (1 : ℝ) / ((i : ℝ) + 1) := by
          rw [sum_Ico_eq_sum_range]
          apply sum_congr rfl
          intro i _
          have : ((j + i : ℕ) : ℝ) - (j : ℝ) = (i : ℝ) := by push_cast; ring
          rw [this, abs_of_nonneg (by positivity)]
      _ ≤ ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) :=
          sum_le_sum_of_subset_of_nonneg
            (fun x hx => mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx) (Nat.sub_le n j)))
            (fun i _ _ => by positivity)

/-- **The harmonic double-sum bound.** Over the full `n × n` index block,
`∑_{j,k<n} 1/(|k−j|+1) ≤ 2 n Hₙ`. -/
theorem double_sum_le (n : ℕ) :
    ∑ j ∈ range n, ∑ k ∈ range n, (1 : ℝ) / (|(k : ℝ) - j| + 1) ≤ 2 * n * (harmonic n : ℝ) := by
  calc ∑ j ∈ range n, ∑ k ∈ range n, (1 : ℝ) / (|(k : ℝ) - j| + 1)
      ≤ ∑ _j ∈ range n, 2 * (harmonic n : ℝ) := by
        apply sum_le_sum
        intro j hj
        rw [mem_range] at hj
        exact inner_sum_le hj
    _ = 2 * n * (harmonic n : ℝ) := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **K4 denominator, log form.** `∑_{j,k<n} 1/(|k−j|+1) ≤ 2 n (1 + log n)`. With `n ≈ δ⁻¹`
this is the `δ⁻¹ log(1/δ)` growth that drives `vol(Sδ) ≳ 1/log(1/δ)`. -/
theorem double_sum_le_log (n : ℕ) :
    ∑ j ∈ range n, ∑ k ∈ range n, (1 : ℝ) / (|(k : ℝ) - j| + 1)
      ≤ 2 * n * (1 + Real.log n) := by
  refine (double_sum_le n).trans ?_
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (by positivity)

end LeanFormalizations.Kakeya2D

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

open Finset MeasureTheory
open scoped Real ENNReal

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

/-! ### The K4 denominator in geometric form

Summing the K2↔K3 per-pair overlap bound `volume_inter_dirTube_le` over the `N × N` index block
and feeding `double_sum_le_log` converts the geometric `∑_{j,k} vol(Tⱼ ∩ Tₖ)` into the analytic
`L²` mass `6π δ · 2N(1 + log N)`. With `N ≈ δ⁻¹` this is `≈ δ · log(1/δ)`. -/

/-- **K4 denominator (geometric form).** For the δ-tube family at net-angles `j·δ` (`j < N`, with
`N δ ≤ 1` so every pair stays within Jordan's `π/2` window), the total pairwise overlap mass is
`≤ 6π δ · 2N(1 + log N)`. The base points `b j` are arbitrary — overlap depends only on the
directions. This is the `∫ f²` denominator of the Córdoba Cauchy–Schwarz estimate. -/
theorem sum_overlap_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : (N : ℝ) * δ ≤ 1)
    (b : ℕ → Plane) :
    ∑ j ∈ range N, ∑ k ∈ range N,
        volume (tube (b j) (dir ((j : ℝ) * δ)) δ ∩ tube (b k) (dir ((k : ℝ) * δ)) δ)
      ≤ ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
  have hπ := Real.pi_pos
  have h1π : (1 : ℝ) ≤ π / 2 := by linarith [Real.two_le_pi]
  have hc : (0 : ℝ) ≤ 6 * π * δ := by nlinarith [mul_nonneg hπ.le hδ.le]
  -- pairwise separation bound, valid for all j,k < N
  have hsep : ∀ j ∈ range N, ∀ k ∈ range N, |(k : ℝ) - j| * δ ≤ π / 2 := by
    intro j hj k hk
    rw [mem_range] at hj hk
    have hjr : (j : ℝ) < N := by exact_mod_cast hj
    have hkr : (k : ℝ) < N := by exact_mod_cast hk
    have habs : |(k : ℝ) - j| ≤ N := by
      rw [abs_le]
      exact ⟨by linarith [(by positivity : (0 : ℝ) ≤ (k : ℝ))],
             by linarith [(by positivity : (0 : ℝ) ≤ (j : ℝ))]⟩
    calc |(k : ℝ) - j| * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right habs hδ.le
      _ ≤ 1 := hN
      _ ≤ π / 2 := h1π
  calc ∑ j ∈ range N, ∑ k ∈ range N,
          volume (tube (b j) (dir ((j : ℝ) * δ)) δ ∩ tube (b k) (dir ((k : ℝ) * δ)) δ)
      ≤ ∑ j ∈ range N, ∑ k ∈ range N, ENNReal.ofReal (6 * π * δ / (|(k : ℝ) - j| + 1)) := by
        apply sum_le_sum; intro j hj; apply sum_le_sum; intro k hk
        exact volume_inter_dirTube_le hδ hδ1 (hsep j hj k hk)
    _ = ENNReal.ofReal (∑ j ∈ range N, ∑ k ∈ range N, 6 * π * δ / (|(k : ℝ) - j| + 1)) := by
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun j _ => Finset.sum_nonneg (fun k _ => div_nonneg hc (by positivity)))]
        apply sum_congr rfl; intro j _
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg hc (by positivity))]
    _ ≤ ENNReal.ofReal (6 * π * δ * (2 * N * (1 + Real.log N))) := by
        apply ENNReal.ofReal_le_ofReal
        have hfac : ∑ j ∈ range N, ∑ k ∈ range N, 6 * π * δ / (|(k : ℝ) - j| + 1)
            = 6 * π * δ * ∑ j ∈ range N, ∑ k ∈ range N, (1 : ℝ) / (|(k : ℝ) - j| + 1) := by
          rw [Finset.mul_sum]; apply sum_congr rfl; intro j _
          rw [Finset.mul_sum]; apply sum_congr rfl; intro k _
          rw [mul_one_div]
        rw [hfac]
        exact mul_le_mul_of_nonneg_left (double_sum_le_log N) hc

/-- **K4 numerator.** `∫ f = ∑ₖ vol(Tₖ) ≥ N · 2δ` — each tube of the family has area `≥ 2δ`
(`volume_tube_ge`). With `N ≈ δ⁻¹` the numerator is `≳ 2`, the `∫ f ≳ 1` mass of the Córdoba
Cauchy–Schwarz estimate. -/
theorem sum_tube_ge {δ : ℝ} (b : ℕ → Plane) (N : ℕ) :
    (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)
      ≤ ∑ k ∈ range N, volume (tube (b k) (dir ((k : ℝ) * δ)) δ) := by
  calc (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ)
      = ∑ _k ∈ range N, ENNReal.ofReal (2 * δ) := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ range N, volume (tube (b k) (dir ((k : ℝ) * δ)) δ) :=
        sum_le_sum (fun k _ => volume_tube_ge (norm_dir _))

end LeanFormalizations.Kakeya2D

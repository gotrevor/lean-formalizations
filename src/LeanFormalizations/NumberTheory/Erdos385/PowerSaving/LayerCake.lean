/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385 power saving: sums from counts (layer cake, phase E9b)

`sum_le_of_count`: if `0 ≤ v_i ≤ V` and `#{i : v_i > u} ≤ M u^{−1/2}` for all `0 < u ≤ V`, then
`Σ v_i ≤ 2 M √V`.  This is the level sum of the near-set `L¹` bound with no explicit dyadic
decomposition: `Σ v_i = ∫_0^V #{v_i > u} du ≤ ∫_0^V M u^{−1/2} du`.
-/

namespace Erdos385.Parseval

open MeasureTheory Set

lemma integral_indicator_Iio {v V : ℝ} (hv0 : 0 ≤ v) (hvV : v ≤ V) :
    ∫ u in Ioc 0 V, (Iio v).indicator (fun _ => (1 : ℝ)) u = v := by
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have : Iio v ∩ Ioc 0 V = Ioo 0 v := by
    ext u; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [this, setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith), sub_zero]

theorem sum_le_of_count {ι : Type*} (S : Finset ι) (v : ι → ℝ) {V M : ℝ} (hV : 0 < V)
    (hv0 : ∀ i ∈ S, 0 ≤ v i) (hvV : ∀ i ∈ S, v i ≤ V)
    (hN : ∀ u, 0 < u → u ≤ V → ((S.filter fun i => u < v i).card : ℝ) ≤ M * u ^ (-(1 / 2 : ℝ))) :
    ∑ i ∈ S, v i ≤ 2 * M * √V := by
  classical
  have hint : ∀ i, IntegrableOn ((Iio (v i)).indicator (fun _ => (1 : ℝ))) (Ioc 0 V) := fun i =>
    (integrableOn_const (by simp)).indicator measurableSet_Iio
  have hsum : ∑ i ∈ S, v i =
      ∫ u in Ioc 0 V, ∑ i ∈ S, (Iio (v i)).indicator (fun _ => (1 : ℝ)) u := by
    rw [integral_finset_sum _ fun i _ => hint i]
    exact Finset.sum_congr rfl fun i hi => (integral_indicator_Iio (hv0 i hi) (hvV i hi)).symm
  have hcount : ∀ u, ∑ i ∈ S, (Iio (v i)).indicator (fun _ => (1 : ℝ)) u =
      ((S.filter fun i => u < v i).card : ℝ) := by
    intro u
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : u < v i <;> simp [indicator, h]
  have hrpow : IntegrableOn (fun u : ℝ => M * u ^ (-(1 / 2 : ℝ))) (Ioc 0 V) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := V)
      (r := -(1 / 2 : ℝ)) (by norm_num)).const_mul M
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hV.le).1 this
  rw [hsum]
  calc ∫ u in Ioc 0 V, ∑ i ∈ S, (Iio (v i)).indicator (fun _ => (1 : ℝ)) u
      ≤ ∫ u in Ioc 0 V, M * u ^ (-(1 / 2 : ℝ)) := by
        refine setIntegral_mono_on (integrable_finset_sum _ fun i _ => hint i) hrpow
          measurableSet_Ioc fun u hu => ?_
        rw [hcount]; exact hN u hu.1 hu.2
    _ = M * ∫ u in (0 : ℝ)..V, u ^ (-(1 / 2 : ℝ)) := by
        rw [integral_const_mul, intervalIntegral.integral_of_le hV.le]
    _ = 2 * M * √V := by
        rw [integral_rpow (Or.inl (by norm_num)), Real.sqrt_eq_rpow]
        norm_num
        ring

end Erdos385.Parseval

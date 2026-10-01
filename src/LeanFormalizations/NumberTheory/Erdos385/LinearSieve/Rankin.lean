/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.GLower

/-!
# Rankin's bound for the tail of Selberg's `G` (phase E5, fundamental lemma)

`Π(z−1) − G_z(ξ) = Σ_{d ∣ P(z), d > ξ} ∏_{p∣d} 1/(p−1) ≤ ξ^{−ε} ∏_{p<z} (1 + p^ε/(p−1))`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Finset ArithmeticFunction Erdos385.Brun

lemma primeFactors_primorial (n : ℕ) :
    (primorial n).primeFactors = (range (n + 1)).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primeFactors, mem_filter, mem_range]
  constructor
  · rintro ⟨hp, hd, -⟩
    exact ⟨Nat.lt_succ_of_le ((prime_dvd_primorial_iff hp).mp hd), hp⟩
  · rintro ⟨hlt, hp⟩
    exact ⟨hp, (prime_dvd_primorial_iff hp).mpr (Nat.le_of_lt_succ hlt),
      (primorial_pos n).ne'⟩

/-- `Σ_{d ∣ n} ∏_{p ∣ d} f(p) = ∏_{p ∣ n}(1 + f(p))` for squarefree `n`. -/
lemma sum_divisors_prod {n : ℕ} (hn : Squarefree n) (f : ℕ → ℝ) :
    ∑ d ∈ n.divisors, ∏ p ∈ d.primeFactors, f p = ∏ p ∈ n.primeFactors, (1 + f p) := by
  have h := (IsMultiplicative.prodPrimeFactors f).prodPrimeFactors_one_add_of_squarefree hn
  calc ∑ d ∈ n.divisors, ∏ p ∈ d.primeFactors, f p
      = ∑ d ∈ n.divisors, prodPrimeFactors f d := sum_congr rfl fun d hd =>
          (prodPrimeFactors_apply (Nat.pos_of_mem_divisors hd).ne').symm
    _ = ∏ p ∈ n.primeFactors, (1 + prodPrimeFactors f p) := h.symm
    _ = _ := prod_congr rfl fun p hp => by
          rw [prodPrimeFactors_apply (Nat.prime_of_mem_primeFactors hp).ne_zero,
            (Nat.prime_of_mem_primeFactors hp).primeFactors, prod_singleton]

lemma rpow_eq_prod_primeFactors {d : ℕ} (hd : Squarefree d) (ε : ℝ) :
    (d : ℝ) ^ ε = ∏ p ∈ d.primeFactors, (p : ℝ) ^ ε := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  push_cast
  exact (Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) ε).symm

/-- **Rankin's tail bound.** -/
theorem mertensP_sub_selG_le (z ξ : ℕ) (hξ : 1 ≤ ξ) {ε : ℝ} (hε : 0 ≤ ε) :
    mertensP (z - 1) - selG z ξ ≤
      (ξ : ℝ) ^ (-ε) * ∏ p ∈ (range z).filter Nat.Prime, (1 + (p : ℝ) ^ ε / ((p : ℝ) - 1)) := by
  classical
  set n := primorial (z - 1)
  have hn : Squarefree n := squarefree_primorial _
  have hPF : n.primeFactors = (range z).filter Nat.Prime := by
    rw [primeFactors_primorial]
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · ext p; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨h, hp⟩; have := hp.two_le; omega
      · rintro ⟨h, _⟩; omega
    · rw [Nat.sub_add_cancel hz]
  set g : ℕ → ℝ := fun d => ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)
  have htotal : ∑ d ∈ n.divisors, g d = mertensP (z - 1) := by
    rw [sum_divisors_prod hn, primeFactors_primorial, mertensP]
    refine prod_congr rfl fun p hp => ?_
    have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
    have h0 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  have hsplit := sum_filter_add_sum_filter_not n.divisors (· ≤ ξ) g
  have hG : selG z ξ = ∑ d ∈ n.divisors.filter (· ≤ ξ), g d := rfl
  have hξpos : (0 : ℝ) < ξ := by exact_mod_cast hξ
  have htail : ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ ξ), g d ≤
      (ξ : ℝ) ^ (-ε) * ∑ d ∈ n.divisors, (d : ℝ) ^ ε * g d := by
    rw [mul_sum]
    calc ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ ξ), g d
        ≤ ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ ξ), (ξ : ℝ) ^ (-ε) * ((d : ℝ) ^ ε * g d) := by
          refine sum_le_sum fun d hd => ?_
          simp only [mem_filter, not_le] at hd
          have hg : 0 ≤ g d := prod_nonneg fun p hp => by
            have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
            exact div_nonneg zero_le_one (by linarith)
          have hdξ : (ξ : ℝ) ≤ d := by exact_mod_cast hd.2.le
          have : 1 ≤ (ξ : ℝ) ^ (-ε) * (d : ℝ) ^ ε := by
            rw [Real.rpow_neg hξpos.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
            exact Real.rpow_le_rpow hξpos.le hdξ hε
          nlinarith
      _ ≤ _ := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun d _ _ => ?_
          refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
          exact prod_nonneg fun p hp => by
            have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
            exact div_nonneg zero_le_one (by linarith)
  have hweighted : ∑ d ∈ n.divisors, (d : ℝ) ^ ε * g d =
      ∏ p ∈ (range z).filter Nat.Prime, (1 + (p : ℝ) ^ ε / ((p : ℝ) - 1)) := by
    rw [← hPF, ← sum_divisors_prod hn]
    refine sum_congr rfl fun d hd => ?_
    have hsq : Squarefree d := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [rpow_eq_prod_primeFactors hsq, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => by ring
  rw [← htotal, ← hsplit, hG, ← hweighted]
  linarith

end LeanFormalizations.Erdos385.LinearSieve

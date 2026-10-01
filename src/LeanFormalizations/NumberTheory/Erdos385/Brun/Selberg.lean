/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385 E2b: the optimal Λ² weights

For a `BoundingSieve` and a divisor-closed `L ⊆ divisors P` containing `1`, set
`G = ∑_{l ∈ L} g(l)` and `w(d) = μ(d)/(ν(d) G) ∑_{m ∈ L, d ∣ m} g(m)` on `L`.  Then `w 1 = 1`,
`mainSum (Λ² w) = 1/G`, and `|w d| ≤ g(d)/ν(d)`.
-/

namespace Erdos385.Brun

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma sum_divisors_moebius_int (n : ℕ) : ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at this
  exact this

/-- `∑_{l ∣ d ∣ m} μ(d) = [l = m] μ(l)` for squarefree `m`. -/
lemma sum_moebius_between {l m : ℕ} (hm : Squarefree m) (hlm : l ∣ m) :
    ∑ d ∈ m.divisors with l ∣ d, (μ d : ℝ) = if l = m then (μ l : ℝ) else 0 := by
  have hm0 := hm.ne_zero
  have hl0 : l ≠ 0 := fun h => hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hlm))
  obtain ⟨k, rfl⟩ := hlm
  have hk0 : k ≠ 0 := by rintro rfl; simp at hm0
  have hco : Nat.Coprime l k := Nat.coprime_of_squarefree_mul hm
  have step : ∑ d ∈ (l * k).divisors with l ∣ d, (μ d : ℝ) =
      ∑ e ∈ k.divisors, (μ l : ℝ) * μ e := by
    refine sum_nbij' (fun d => d / l) (fun e => l * e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd
      simp only [Nat.mem_divisors]
      obtain ⟨⟨hdm, -⟩, e, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hl0)]
      exact ⟨Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hl0) hdm, hk0⟩
    · intro e he
      simp only [Nat.mem_divisors] at he
      simp only [mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.mul_dvd_mul_left l he.1, by positivity⟩, dvd_mul_right l e⟩
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro e _
      exact Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hl0)
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdm, -⟩, e, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hl0)]
      have : Nat.Coprime l e := Nat.coprime_of_squarefree_mul (hm.squarefree_of_dvd hdm)
      rw [isMultiplicative_moebius.map_mul_of_coprime this]; push_cast; ring
  rw [step, ← mul_sum]
  have hs := congrArg (fun z : ℤ => (z : ℝ)) (sum_divisors_moebius_int k)
  push_cast at hs
  rw [hs]
  by_cases hk : k = 1
  · subst hk; simp
  · rw [if_neg hk, if_neg]; · ring
    intro h
    exact hk (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0) (by rw [mul_one]; exact h.symm))

section Weights

variable (s : BoundingSieve) (L : Finset ℕ)

/-- `G = ∑_{l ∈ L} g(l)`. -/
noncomputable def selbergG : ℝ := ∑ l ∈ L, s.selbergTerms l

/-- The optimal Λ² weights. -/
noncomputable def selbergW (d : ℕ) : ℝ :=
  if d ∈ L then (μ d : ℝ) / (s.nu d * selbergG s L) * ∑ m ∈ L with d ∣ m, s.selbergTerms m
  else 0

variable {s L}
variable (hLP : L ⊆ s.prodPrimes.divisors) (hL1 : 1 ∈ L) (hLcl : ∀ m ∈ L, ∀ d, d ∣ m → d ∈ L)
include hLP

lemma dvd_prodPrimes_of_mem {d : ℕ} (hd : d ∈ L) : d ∣ s.prodPrimes :=
  (Nat.mem_divisors.mp (hLP hd)).1

lemma selbergTerms_nonneg_of_mem {d : ℕ} (hd : d ∈ L) : 0 ≤ s.selbergTerms d :=
  (BoundingSieve.selbergTerms_pos (dvd_prodPrimes_of_mem hLP hd)).le

include hL1 in
lemma selbergG_pos : 0 < selbergG s L := by
  unfold selbergG
  exact sum_pos (fun l hl => BoundingSieve.selbergTerms_pos (dvd_prodPrimes_of_mem hLP hl)) ⟨1, hL1⟩

include hL1 in
lemma selbergW_one : selbergW s L 1 = 1 := by
  have hG := selbergG_pos hLP hL1
  unfold selbergW
  rw [if_pos hL1, s.nu_mult.map_one, moebius_apply_one]
  simp only [isUnit_one, IsUnit.dvd, filter_true_of_mem, implies_true, Int.cast_one, one_mul]
  rw [div_mul_eq_mul_div, one_mul]; exact div_self hG.ne'

include hLcl in
lemma sum_filter_moebius_eq {l m : ℕ} (hm : m ∈ L) :
    ∑ d ∈ s.prodPrimes.divisors with (l ∣ d ∧ d ∈ L ∧ d ∣ m), (μ d : ℝ) =
      if l = m then (μ l : ℝ) else 0 := by
  have hmP := dvd_prodPrimes_of_mem hLP hm
  have hmsq : Squarefree m := BoundingSieve.squarefree_of_dvd_prodPrimes hmP
  have hfil : s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∈ L ∧ d ∣ m) =
      m.divisors.filter (l ∣ ·) := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hl, -, hdm⟩; exact ⟨⟨hdm, hmsq.ne_zero⟩, hl⟩
    · rintro ⟨⟨hdm, -⟩, hl⟩
      exact ⟨⟨hdm.trans hmP, BoundingSieve.prodPrimes_ne_zero⟩, hl, hLcl m hm d hdm, hdm⟩
  rw [hfil]
  by_cases hlm : l ∣ m
  · exact sum_moebius_between hmsq hlm
  · rw [if_neg (fun h : l = m => hlm (h ▸ dvd_rfl))]
    refine sum_eq_zero fun d hd => ?_
    simp only [mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) hlm

include hLcl in
lemma inner_selbergW {l : ℕ} :
    ∑ d ∈ s.prodPrimes.divisors, (if l ∣ d then s.nu d * selbergW s L d else 0) =
      if l ∈ L then (μ l : ℝ) * s.selbergTerms l / selbergG s L else 0 := by
  set G := selbergG s L
  have step : ∀ d ∈ s.prodPrimes.divisors, (if l ∣ d then s.nu d * selbergW s L d else 0) =
      ∑ m ∈ L, (if l ∣ d ∧ d ∈ L ∧ d ∣ m then (μ d : ℝ) else 0) * (s.selbergTerms m / G) := by
    intro d hd
    have hν : s.nu d ≠ 0 := BoundingSieve.nu_ne_zero (Nat.mem_divisors.mp hd).1
    unfold selbergW
    by_cases hld : l ∣ d
    · by_cases hdL : d ∈ L
      · rw [if_pos hld, if_pos hdL, sum_filter, mul_sum, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        by_cases hdm : d ∣ m
        · simp only [hld, hdL, hdm, and_self, if_true]
          field_simp; rfl
        · simp [hdm]
      · simp [hld, hdL]
    · simp [hld]
  rw [sum_congr rfl step, sum_comm]
  simp_rw [← sum_mul]
  rw [sum_congr rfl fun m hm => by rw [← sum_filter, sum_filter_moebius_eq hLP hLcl hm]]
  simp_rw [ite_mul, zero_mul]
  rw [sum_ite_eq]
  split_ifs <;> ring

include hL1 hLcl in
/-- **The Selberg main term.** -/
theorem mainSum_selbergW : s.mainSum (BoundingSieve.lambdaSquared (selbergW s L)) =
    1 / selbergG s L := by
  have hG := selbergG_pos hLP hL1
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  simp_rw [inner_selbergW hLP hLcl]
  have : ∀ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
      (if l ∈ L then (μ l : ℝ) * s.selbergTerms l / selbergG s L else 0) ^ 2 =
      if l ∈ L then s.selbergTerms l / selbergG s L ^ 2 else 0 := by
    intro l hl
    split_ifs with hlL
    · have hg := BoundingSieve.selbergTerms_pos (dvd_prodPrimes_of_mem hLP hlL)
      have hμ : (μ l : ℝ) ^ 2 = 1 := by
        have := moebius_sq_eq_one_of_squarefree
          (BoundingSieve.squarefree_of_dvd_prodPrimes (dvd_prodPrimes_of_mem hLP hlL))
        exact_mod_cast this
      field_simp
      exact hμ
    · simp
  rw [sum_congr rfl this, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hLP, ← sum_div]
  unfold selbergG at hG ⊢
  field_simp

include hLcl in
/-- `|w(d)| ≤ g(d)/ν(d)`. -/
theorem abs_selbergW_le {d : ℕ} (hd : d ∈ L) (hL1 : 1 ∈ L) :
    |selbergW s L d| ≤ s.selbergTerms d / s.nu d := by
  have hG := selbergG_pos hLP hL1
  have hdP := dvd_prodPrimes_of_mem hLP hd
  have hν := BoundingSieve.nu_pos_of_dvd_prodPrimes hdP
  have hgd := BoundingSieve.selbergTerms_pos hdP
  have hS : ∑ m ∈ L with d ∣ m, s.selbergTerms m ≤ s.selbergTerms d * selbergG s L := by
    have hsplit : ∀ m ∈ L.filter (d ∣ ·),
        s.selbergTerms m = s.selbergTerms d * s.selbergTerms (m / d) := by
      intro m hm
      simp only [mem_filter] at hm
      have hmsq := BoundingSieve.squarefree_of_dvd_prodPrimes (dvd_prodPrimes_of_mem hLP hm.1)
      have hmul : d * (m / d) = m := Nat.mul_div_cancel' hm.2
      have hco : Nat.Coprime d (m / d) := Nat.coprime_of_squarefree_mul (hmul.symm ▸ hmsq)
      rw [← BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime hco, hmul]
    rw [sum_congr rfl hsplit, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hgd.le
    have hinj : Set.InjOn (· / d) (L.filter (d ∣ ·) : Set ℕ) := by
      intro a ha b hb hab
      simp only [coe_filter, Set.mem_setOf_eq] at ha hb
      simp only at hab
      rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, hab]
    rw [← sum_image (f := s.selbergTerms) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun e he _ => selbergTerms_nonneg_of_mem hLP he
    intro e he
    obtain ⟨m, hm, rfl⟩ := mem_image.mp he
    simp only [mem_filter] at hm
    exact hLcl m hm.1 _ (Nat.div_dvd_of_dvd hm.2)
  unfold selbergW
  rw [if_pos hd, abs_mul, abs_div, abs_of_nonneg (sum_nonneg fun m hm =>
    selbergTerms_nonneg_of_mem hLP (mem_filter.mp hm).1), abs_of_pos (mul_pos hν hG)]
  have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  calc |(μ d : ℝ)| / (s.nu d * selbergG s L) * ∑ m ∈ L with d ∣ m, s.selbergTerms m
      ≤ 1 / (s.nu d * selbergG s L) * (s.selbergTerms d * selbergG s L) := by
        gcongr
        exact sum_nonneg fun m hm => selbergTerms_nonneg_of_mem hLP (mem_filter.mp hm).1
    _ = s.selbergTerms d / s.nu d := by field_simp

end Weights

end Erdos385.Brun

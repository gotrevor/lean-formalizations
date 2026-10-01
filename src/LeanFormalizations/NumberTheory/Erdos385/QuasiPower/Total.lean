/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.ClassCount
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Analytic

/-!
# Erdős #385, phase E8: summing `class_count` over the classes mod `y#`

`#{bad n ≤ X} ≤ R + Y + y · C (X + Q²) (ρ + δ₀)^k` given, for every class, `k` positions in a
window of length `< y` coprime to the small primes, a pool weight `ρ^K e_K ≥ 1` (`K ≤ k`) and the
per-position bound `∑_{y < p ≤ a} 1/(p − 1) ≤ δ₀` (`total_count`).  The factor `y` is
`y# / ∏_{p ≤ y}(p − 1) ≤ y` (`Exceptional.primorial_le_mul_prod_sub_one`).
-/

namespace LeanFormalizations.Erdos385.QuasiPower

open LeanFormalizations.Erdos385 LeanFormalizations.Erdos385.Exceptional Finset

open scoped Classical in
theorem total_count {C : ℝ} (h1 : LSWith C) (hC : 0 ≤ C) {X y Y Q R k : ℕ} (ρ δ0 : ℝ)
    (hρ : 0 ≤ ρ) (hy : 1 ≤ y) (hyY : y ≤ Y) (hR : 1 ≤ R)
    (hwin : ∀ s : ℕ, ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ Y) ∧
      (∀ a ∈ A, ∀ p, p.Prime → p ≤ y → s % p ≠ a % p) ∧ (∀ a ∈ A, ∀ b ∈ A, b < a + y))
    (hQ : primorial y * Y ^ k * R ^ k ≤ Q)
    (hw : ∀ K ≤ k, 1 ≤ ρ ^ K * poolWeight ((Ioc Y R).filter Nat.Prime) K K)
    (hδ : ∀ a ≤ Y, ∑ p ∈ (Ioc y a).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ δ0) :
    (((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ) ≤
      (R + Y : ℝ) + y * (C * (X + (Q : ℝ) ^ 2) * (ρ + δ0) ^ k) := by
  classical
  set P := primorial y
  have hPpos : 0 < P := primorial_pos y
  set W0 : ℝ := ∏ p ∈ ps y, ((p : ℝ) - 1)
  have hW0 : 0 < W0 := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    linarith
  have hδ0 : 0 ≤ δ0 := by
    have := hδ 0 (Nat.zero_le _); simpa using this
  set Kc : ℝ := C * (X + (Q : ℝ) ^ 2)
  have hKc : 0 ≤ Kc := by positivity
  set cls : ℕ → Finset ℕ := fun s => (Icc 1 X).filter fun n =>
    n % P = s % P ∧ R + Y < n ∧ 5 ≤ n ∧ Bad n
  set small := (Icc 1 X).filter fun n => n ≤ R + Y
  have hsplit : ((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n) ⊆
      small ∪ (range P).biUnion cls := by
    intro n hn
    obtain ⟨hnI, hn5, hb⟩ := mem_filter.1 hn
    by_cases hs : n ≤ R + Y
    · exact mem_union_left _ (mem_filter.2 ⟨hnI, hs⟩)
    · refine mem_union_right _ (mem_biUnion.2 ⟨n % P, mem_range.2 (Nat.mod_lt _ hPpos), ?_⟩)
      exact mem_filter.2 ⟨hnI, (Nat.mod_mod _ _).symm, by omega, hn5, hb⟩
  have hsmall : (small.card : ℝ) ≤ R + Y := by
    have : small.card ≤ R + Y := by
      calc small.card ≤ (Icc 1 (R + Y)).card := card_le_card fun n hn => by
            obtain ⟨h1, h2⟩ := mem_filter.1 hn
            exact mem_Icc.2 ⟨(mem_Icc.1 h1).1, h2⟩
        _ = R + Y := by simp
    exact_mod_cast this
  have hcls : ∀ s, ((cls s).card : ℝ) ≤ Kc * (ρ + δ0) ^ k / W0 := by
    intro s
    obtain ⟨A, hAk, hA1, hAy, hAd⟩ := hwin s
    have hcc := class_count h1 hC (X := X) (Q := Q) ρ hρ s A ((Ioc Y R).filter Nat.Prime) hyY hR hA1
      hAy hAd (fun q hq => by
        have := mem_filter.1 hq; exact ⟨this.2, (mem_Ioc.1 this.1).1, (mem_Ioc.1 this.1).2⟩)
      (by rw [hAk]; exact hQ) (by rw [hAk]; exact hw)
    have hprod : ∏ a ∈ A, (ρ + ∑ p ∈ (Ioc y a).filter Nat.Prime, 1 / ((p : ℝ) - 1)) ≤
        (ρ + δ0) ^ k := by
      rw [← hAk, ← prod_const]
      refine prod_le_prod (fun a _ => ?_) fun a ha => by linarith [hδ a (hA1 a ha).2]
      have : 0 ≤ ∑ p ∈ (Ioc y a).filter Nat.Prime, 1 / ((p : ℝ) - 1) := sum_nonneg fun p hp => by
        have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
        exact div_nonneg zero_le_one (by linarith)
      linarith
    rw [le_div_iff₀ hW0]
    exact hcc.trans (mul_le_mul_of_nonneg_left hprod hKc)
  have hPW : (P : ℝ) ≤ y * W0 := primorial_le_mul_prod_sub_one y hy
  calc (((Icc 1 X).filter fun n => 5 ≤ n ∧ Bad n).card : ℝ)
      ≤ ((small ∪ (range P).biUnion cls).card : ℝ) := by exact_mod_cast card_le_card hsplit
    _ ≤ (small.card : ℝ) + ∑ s ∈ range P, ((cls s).card : ℝ) := by
        have h := (card_union_le small ((range P).biUnion cls)).trans
          (Nat.add_le_add_left card_biUnion_le _)
        exact_mod_cast h
    _ ≤ (R + Y : ℝ) + ∑ _s ∈ range P, Kc * (ρ + δ0) ^ k / W0 :=
        add_le_add hsmall (sum_le_sum fun s _ => hcls s)
    _ = (R + Y : ℝ) + P * (Kc * (ρ + δ0) ^ k) / W0 := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ (R + Y : ℝ) + y * (Kc * (ρ + δ0) ^ k) := by
        gcongr
        rw [div_le_iff₀ hW0]
        have : 0 ≤ Kc * (ρ + δ0) ^ k := by positivity
        nlinarith

end LeanFormalizations.Erdos385.QuasiPower

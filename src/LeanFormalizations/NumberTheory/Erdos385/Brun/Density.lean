/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385 E2b: local densities for the prime-pair sieve

`rho h d = #{a < d : d ∣ a (a + h)}`: multiplicative on coprime moduli, `= 1 + [p ∤ h]` at primes,
and the counting remainder `|#{n < N : d ∣ n(n+h)} − N ρ(d)/d| ≤ ρ(d)`.
-/

namespace Erdos385.Brun

open Finset

/-- A `d`-periodic predicate is counted up to an error `count Q d`. -/
lemma abs_count_periodic_sub_le (Q : ℕ → Prop) [DecidablePred Q] {d : ℕ} (hd : 0 < d)
    (hQ : ∀ n, Q (n + d) ↔ Q n) (N : ℕ) :
    |(Nat.count Q N : ℝ) - N * Nat.count Q d / d| ≤ Nat.count Q d := by
  have hper : ∀ q k, Q (q * d + k) ↔ Q k := by
    intro q k
    induction q with
    | zero => simp
    | succ q ih => rw [show (q + 1) * d + k = (q * d + k) + d by ring, hQ]; exact ih
  have hshift : ∀ q n, Nat.count (fun k => Q (q * d + k)) n = Nat.count Q n := by
    intro q n
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    exact filter_congr fun k _ => hper q k
  have hmul : ∀ q, Nat.count Q (q * d) = q * Nat.count Q d := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show (q + 1) * d = q * d + d by ring, Nat.count_add, hshift, ih]; ring
  set q := N / d; set r := N % d
  have hN : N = q * d + r := by rw [mul_comm]; exact (Nat.div_add_mod N d).symm
  have hr : r < d := Nat.mod_lt N hd
  have hcN : Nat.count Q N = q * Nat.count Q d + Nat.count Q r := by
    rw [hN, Nat.count_add, hshift, hmul]
  have hcr : Nat.count Q r ≤ Nat.count Q d := Nat.count_monotone Q hr.le
  set c := Nat.count Q d
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hrd : (r : ℝ) * c / d ≤ c := by
    rw [div_le_iff₀ hd', mul_comm (c : ℝ)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hr.le) (by positivity)
  have hexp : (N : ℝ) * c / d = q * c + r * c / d := by
    rw [hN]; push_cast; field_simp
  rw [hcN, hexp, abs_le]
  push_cast
  constructor
  · have : (0 : ℝ) ≤ Nat.count Q r := Nat.cast_nonneg _
    linarith
  · have : (0 : ℝ) ≤ r * c / d := by positivity
    have : (Nat.count Q r : ℝ) ≤ c := by exact_mod_cast hcr
    linarith

/-- Local density count: `#{a < d : d ∣ a (a + h)}`. -/
def rho (h d : ℕ) : ℕ := Nat.count (fun a => d ∣ a * (a + h)) d

lemma dvd_shift_iff (h d n : ℕ) : d ∣ (n + d) * (n + d + h) ↔ d ∣ n * (n + h) := by
  rw [show (n + d) * (n + d + h) = n * (n + h) + d * (2 * n + d + h) by ring]
  exact (Nat.dvd_add_left (dvd_mul_right d _))

/-- The counting remainder. -/
lemma abs_count_dvd_sub_le (h : ℕ) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    |(Nat.count (fun a => d ∣ a * (a + h)) N : ℝ) - N * rho h d / d| ≤ rho h d :=
  abs_count_periodic_sub_le _ hd (dvd_shift_iff h d) N

lemma dvd_mod_iff (h m a : ℕ) : m ∣ (a % m) * (a % m + h) ↔ m ∣ a * (a + h) := by
  have : (a % m) * (a % m + h) ≡ a * (a + h) [MOD m] :=
    (Nat.mod_modEq a m).mul ((Nat.mod_modEq a m).add_right h)
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun h0 => this.symm.trans h0, fun h0 => this.trans h0⟩

/-- `rho h` is multiplicative on coprime moduli (CRT). -/
lemma rho_mul (h : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (co : Nat.Coprime m n) :
    rho h (m * n) = rho h m * rho h n := by
  unfold rho
  simp only [Nat.count_eq_card_filter_range]
  rw [← card_product]
  refine card_nbij' (fun a => (a % m, a % n)) (fun x => Nat.chineseRemainder co x.1 x.2)
    ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_range, coe_filter, Set.mem_setOf_eq] at ha
    simp only [mem_range, coe_product, coe_filter, Set.mem_prod,
      Set.mem_setOf_eq]
    exact ⟨⟨Nat.mod_lt a (Nat.pos_of_ne_zero hm),
        (dvd_mod_iff h m a).mpr ((dvd_mul_right m n).trans ha.2)⟩,
      Nat.mod_lt a (Nat.pos_of_ne_zero hn),
        (dvd_mod_iff h n a).mpr ((dvd_mul_left n m).trans ha.2)⟩
  · intro x hx
    simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_setOf_eq] at hx
    obtain ⟨⟨hx1, hdx1⟩, hx2, hdx2⟩ := hx
    set k := Nat.chineseRemainder co x.1 x.2
    have hk1 : k % m = x.1 := by rw [k.prop.1]; exact Nat.mod_eq_of_lt hx1
    have hk2 : k % n = x.2 := by rw [k.prop.2]; exact Nat.mod_eq_of_lt hx2
    simp only [coe_filter, mem_range, Set.mem_setOf_eq]
    refine ⟨Nat.chineseRemainder_lt_mul co _ _ hm hn, co.mul_dvd_of_dvd_of_dvd ?_ ?_⟩
    · rw [← dvd_mod_iff, hk1]; exact hdx1
    · rw [← dvd_mod_iff, hk2]; exact hdx2
  · intro a ha
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha
    have := Nat.chineseRemainder_modEq_unique co (Nat.mod_modEq a m).symm (Nat.mod_modEq a n).symm
    exact (Nat.ModEq.eq_of_lt_of_lt this.symm (Nat.chineseRemainder_lt_mul co _ _ hm hn) ha.1)
  · intro x hx
    simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_setOf_eq] at hx
    set k := Nat.chineseRemainder co x.1 x.2
    ext
    · show k % m = x.1; rw [k.prop.1]; exact Nat.mod_eq_of_lt hx.1.1
    · show k % n = x.2; rw [k.prop.2]; exact Nat.mod_eq_of_lt hx.2.1

lemma rho_le (h d : ℕ) : rho h d ≤ d := by
  unfold rho; rw [Nat.count_eq_card_filter_range]
  exact (card_filter_le _ _).trans (card_range d).le

lemma rho_one (h : ℕ) : rho h 1 = 1 := by
  unfold rho; simp [Nat.count_succ]

lemma dvd_iff_of_lt_two_mul {p x : ℕ} (hp : 0 < p) (hx : x < 2 * p) : p ∣ x ↔ x = 0 ∨ x = p := by
  constructor
  · rintro ⟨k, rfl⟩
    have : k < 2 := by nlinarith
    interval_cases k <;> simp
  · rintro (rfl | rfl) <;> simp

/-- `ρ(p) = 1` if `p ∣ h`, else `2`. -/
lemma rho_prime (h : ℕ) {p : ℕ} (hp : p.Prime) : rho h p = if p ∣ h then 1 else 2 := by
  unfold rho; rw [Nat.count_eq_card_filter_range]
  set c := h % p with hc
  have hcp : c < p := Nat.mod_lt h hp.pos
  have hdh : p ∣ h ↔ c = 0 := Nat.dvd_iff_mod_eq_zero
  have key : ∀ a, a < p → (p ∣ a * (a + h) ↔ a = 0 ∨ a + c = 0 ∨ a + c = p) := by
    intro a ha
    rw [hp.dvd_mul]
    have h1 : p ∣ a ↔ a = 0 := ⟨fun hd => Nat.eq_zero_of_dvd_of_lt hd ha, fun h0 => h0 ▸ dvd_zero p⟩
    have h2 : p ∣ a + h ↔ p ∣ a + c := by
      conv_lhs => rw [← Nat.div_add_mod h p, ← hc]
      rw [show a + (p * (h / p) + c) = a + c + p * (h / p) by ring]
      exact Nat.dvd_add_left (dvd_mul_right p _)
    rw [h1, h2, dvd_iff_of_lt_two_mul hp.pos (by omega)]
  by_cases hc0 : c = 0
  · rw [if_pos (hdh.mpr hc0)]
    rw [show (range p).filter (fun a => p ∣ a * (a + h)) = {0} by
      ext a; simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨ha, hd⟩; have := (key a ha).mp hd; omega
      · rintro rfl; exact ⟨hp.pos, by simp⟩]
    simp
  · rw [if_neg (fun hd => hc0 (hdh.mp hd))]
    rw [show (range p).filter (fun a => p ∣ a * (a + h)) = {0, p - c} by
      ext a; simp only [mem_filter, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨ha, hd⟩; have := (key a ha).mp hd; omega
      · intro hor
        have ha : a < p := by omega
        exact ⟨ha, (key a ha).mpr (by omega)⟩]
    rw [card_insert_of_notMem (by simp; omega), card_singleton]

/-- For squarefree `d`, `ρ(d) = ∏_{p ∣ d} ρ(p)`. -/
lemma rho_eq_prod (h : ℕ) {d : ℕ} (hd : Squarefree d) :
    rho h d = ∏ p ∈ d.primeFactors, rho h p := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hk1 : k = 1 := by
      by_contra hne
      have : p * p ∣ p ^ k := by
        rw [← pow_two]; exact pow_dvd_pow p (by omega)
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hd p this))
    subst hk1
    simp [hp.primeFactors]
  | zero => exact absurd hd not_squarefree_zero
  | one => simp [rho_one]
  | coprime a b ha hb co iha ihb =>
    have hsq := Nat.squarefree_mul_iff.mp hd
    rw [rho_mul h (by omega) (by omega) co, iha hsq.2.1, ihb hsq.2.2,
      Nat.Coprime.primeFactors_mul co, prod_union co.disjoint_primeFactors]

end Erdos385.Brun

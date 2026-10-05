/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Phase 62, lap 3: Skolem's `p`-adic method for order-3 recurrences

The finiteness of exact zeros `e₂(β^n) = 0` (`SaitoTypeBRecords.finite_e2_zero_orbit`) is a
Skolem problem: `e₂(β^n)` is an integer recurrence of order 3 with constant term `N(β)²`.  This
file proves Skolem's local lemma in elementary form.

**The three-zero determinant (`skolem_det_ne_zero`).**  Fix an odd prime `p`.  For integer
sequences `c`, put `U c z = Σ_{k ≤ z} C(z,k) p^(2k) c_k`.  If `β_k = 0, 1, 0` and `α_k = 0, 0, 1`
for `k = 0, 1, 2`, then for `0 < a < b`

  `U β a · U α b − U β b · U α a ≠ 0`.

Proof in `ℚ_[p]`: the determinant is `Σ_{k,k'} p^(2(k+k')) β_k α_k' G(k,k')` with
`G(k,k') = C(a,k) C(b,k') − C(b,k) C(a,k')`, and `k! k'! G = ab(b − a) H` with `H ∈ ℤ`
(falling factorials, `sub_dvd_eval_sub`).  The term `(1,2)` is `p⁶ ab(b − a)/2`; every other
nonzero term has `k + k' ≥ 4` and norm `≤ p^(−2(k+k') + v_p(k!) + v_p(k'!)) ‖ab(b−a)‖ ≤
p^(−7) ‖ab(b−a)‖`, since `2 v_p(k!) ≤ k − 1`.

**Use.**  If `A^P = 1 + p² D` and a linear functional `ℓ` vanishes on `(1 + p²D)^z` at `z = 0, a, b`,
Cayley–Hamilton writes `ℓ(D^k) = α_k ℓ(D²) + β_k ℓ(D)` and the determinant forces
`ℓ(D) = ℓ(D²) = 0`, so `ℓ` vanishes on the whole class.
-/

namespace LeanFormalizations.Mills.Skolem

open Finset Polynomial

/-- `ab(b − a)` divides `f(a) g(b) − f(b) g(a)` when `X ∣ f` and `X ∣ g`. -/
theorem dvd_antisymm_eval {f g : ℤ[X]} (hf : X ∣ f) (hg : X ∣ g) (a b : ℤ) :
    a * b * (b - a) ∣ f.eval a * g.eval b - f.eval b * g.eval a := by
  obtain ⟨f', rfl⟩ := hf
  obtain ⟨g', rfl⟩ := hg
  simp only [eval_mul, eval_X]
  have h1 : b - a ∣ f'.eval b - f'.eval a := sub_dvd_eval_sub b a f'
  have h2 : b - a ∣ g'.eval b - g'.eval a := sub_dvd_eval_sub b a g'
  have e : a * f'.eval a * (b * g'.eval b) - b * f'.eval b * (a * g'.eval a)
      = a * b * (f'.eval a * (g'.eval b - g'.eval a) - g'.eval a * (f'.eval b - f'.eval a)) := by
    ring
  rw [e]
  exact mul_dvd_mul_left _ (dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _))

theorem X_dvd_descPochhammer {k : ℕ} (hk : 1 ≤ k) : (X : ℤ[X]) ∣ descPochhammer ℤ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [descPochhammer_succ_left]
  exact dvd_mul_right _ _

/-- `k! k'! (C(a,k) C(b,k') − C(b,k) C(a,k'))` is divisible by `ab(b − a)`. -/
theorem choose_det_dvd (a b : ℕ) {k k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k') :
    (a : ℤ) * b * (b - a) ∣ ((k.factorial * k'.factorial : ℕ) : ℤ) *
      ((a.choose k : ℤ) * b.choose k' - b.choose k * a.choose k') := by
  have h := dvd_antisymm_eval (X_dvd_descPochhammer hk) (X_dvd_descPochhammer hk') a b
  rw [descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial,
    descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial] at h
  simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul] at h
  push_cast
  convert h using 1
  ring

/-- `2 C(n,2) = n (n − 1)`. -/
theorem two_mul_choose_two (n : ℕ) : 2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  have h := descPochhammer_eval_eq_descFactorial ℤ n 2
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  simp [descPochhammer_succ_eval] at h
  linarith

/-- The Mahler-type sum `U c z = Σ_{k ≤ z} C(z,k) p^(2k) c_k`. -/
def U (p : ℕ) (c : ℕ → ℤ) (z : ℕ) : ℤ :=
  ∑ k ∈ range (z + 1), (z.choose k : ℤ) * (p : ℤ) ^ (2 * k) * c k

theorem U_eq_sum_of_le (p : ℕ) (c : ℕ → ℤ) {z N : ℕ} (h : z ≤ N) :
    U p c z = ∑ k ∈ range (N + 1), (z.choose k : ℤ) * (p : ℤ) ^ (2 * k) * c k := by
  unfold U
  apply Finset.sum_subset (range_subset_range.2 (by omega))
  intro k hk hk'
  simp only [mem_range] at hk hk'
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- `‖(n : ℚ_[p])‖ = p^(−v_p(n))` for `n ≠ 0`. -/
theorem norm_natCast_eq {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn), Padic.valuation_natCast]

/-- `2 v_p(k!) ≤ k − 1` for an odd prime `p` and `k ≥ 1`. -/
theorem two_mul_padicValNat_factorial_le {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ}
    (hk : k ≠ 0) : 2 * padicValNat p k.factorial + 1 ≤ k := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hk
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have : 2 * padicValNat p k.factorial ≤ (p - 1) * padicValNat p k.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Skolem's three-zero determinant.** -/
theorem skolem_det_ne_zero {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (α β : ℕ → ℤ)
    (hβ0 : β 0 = 0) (hβ1 : β 1 = 1) (hβ2 : β 2 = 0)
    (hα0 : α 0 = 0) (hα1 : α 1 = 0) (hα2 : α 2 = 1)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    U p β a * U p α b - U p β b * U p α a ≠ 0 := by
  set R := range (b + 1) with hR
  set G : ℕ → ℕ → ℤ := fun k k' =>
    (a.choose k : ℤ) * b.choose k' - b.choose k * a.choose k' with hG
  set T : ℕ × ℕ → ℤ := fun q =>
    (p : ℤ) ^ (2 * q.1 + 2 * q.2) * β q.1 * α q.2 * G q.1 q.2 with hT
  have hdet : U p β a * U p α b - U p β b * U p α a = ∑ q ∈ R ×ˢ R, T q := by
    rw [U_eq_sum_of_le p β hab.le, U_eq_sum_of_le p α le_rfl, U_eq_sum_of_le p β le_rfl,
      U_eq_sum_of_le p α hab.le, Finset.sum_mul_sum, Finset.sum_mul_sum,
      ← Finset.sum_sub_distrib, Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    simp only [hT, hG, pow_add]
    ring
  have hmem : ((1 : ℕ), (2 : ℕ)) ∈ R ×ˢ R := by
    simp only [hR, mem_product, mem_range]; omega
  rw [hdet, ← Finset.add_sum_erase _ _ hmem]
  -- the main term
  set X : ℤ := (a : ℤ) * b * (b - a) with hX
  have hX0 : X ≠ 0 := by
    have : (b : ℤ) - a ≠ 0 := by omega
    have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℤ) ≠ 0 := by omega
    exact mul_ne_zero (mul_ne_zero ha' hb') this
  have hmain : 2 * T (1, 2) = (p : ℤ) ^ 6 * X := by
    have ha2 := two_mul_choose_two a
    have hb2 := two_mul_choose_two b
    simp only [hT, hG, hβ1, hα2, Nat.choose_one_right]
    rw [hX]
    linear_combination (p : ℤ) ^ 6 * (a * hb2 - b * ha2)
  -- norms in `ℚ_[p]`
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hXn : 0 < ‖(X : ℚ_[p])‖ := norm_pos_iff.2 (by exact_mod_cast hX0)
  have hnorm_main : ‖(T (1, 2) : ℚ_[p])‖ = (p : ℝ) ^ (-6 : ℤ) * ‖(X : ℚ_[p])‖ := by
    have h2 : ‖((2 : ℤ) : ℚ_[p])‖ = 1 := by
      rw [Padic.norm_intCast_eq_one_iff]
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)
      simpa [Int.gcd] using this
    have := congrArg (fun z : ℤ => ‖(z : ℚ_[p])‖) hmain
    simp only [Int.cast_mul, norm_mul, h2, one_mul, Int.cast_pow, Int.cast_natCast] at this
    rw [Padic.norm_p_pow] at this
    rw [this]
    norm_num
  have hnorm_rest : ∀ q ∈ (R ×ˢ R).erase (1, 2),
      ‖(T q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-7 : ℤ) * ‖(X : ℚ_[p])‖ := by
    rintro ⟨k, k'⟩ hq
    have hq' : (k, k') ≠ ((1 : ℕ), (2 : ℕ)) := (Finset.mem_erase.1 hq).1
    by_cases hz : β k * α k' = 0
    · have : T (k, k') = 0 := by
        simp only [hT]; rw [mul_assoc ((p : ℤ) ^ _ ), hz]; ring
      rw [this, Int.cast_zero, norm_zero]; positivity
    have hβk : β k ≠ 0 := left_ne_zero_of_mul hz
    have hαk : α k' ≠ 0 := right_ne_zero_of_mul hz
    have hk0 : k ≠ 0 := fun h => hβk (h ▸ hβ0)
    have hk2 : k ≠ 2 := fun h => hβk (h ▸ hβ2)
    have hk'0 : k' ≠ 0 := fun h => hαk (h ▸ hα0)
    have hk'1 : k' ≠ 1 := fun h => hαk (h ▸ hα1)
    have hsum : 4 ≤ k + k' := by
      by_contra hlt
      apply hq'
      have : k = 1 ∧ k' = 2 := by omega
      rw [this.1, this.2]
    -- the divisibility `k! k'! G = X H`
    obtain ⟨H, hH⟩ := choose_det_dvd a b (k := k) (k' := k') (by omega) (by omega)
    set F : ℕ := k.factorial * k'.factorial with hF
    have hF0 : F ≠ 0 := by positivity
    set v : ℕ := padicValNat p F with hv
    have hvk : 2 * v + 2 ≤ k + k' := by
      have h1 := two_mul_padicValNat_factorial_le hp2 hk0
      have h2 := two_mul_padicValNat_factorial_le hp2 hk'0
      have : v = padicValNat p k.factorial + padicValNat p k'.factorial := by
        rw [hv, hF, padicValNat.mul (by positivity) (by positivity)]
      omega
    have hFn : ‖((F : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-(v : ℤ)) := norm_natCast_eq hF0
    have hGn : ‖((G k k' : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (v : ℤ) * ‖(X : ℚ_[p])‖ := by
      have e0 : (F : ℤ) * G k k' = X * H := hH
      have e := congrArg (fun z : ℤ => ‖(z : ℚ_[p])‖) e0
      simp only [Int.cast_mul, norm_mul, Int.cast_natCast] at e
      rw [hFn] at e
      have hHn : ‖((H : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one H
      have : (p : ℝ) ^ (-(v : ℤ)) * ‖((G k k' : ℤ) : ℚ_[p])‖ ≤ ‖(X : ℚ_[p])‖ := by
        rw [e]
        calc ‖(X : ℚ_[p])‖ * ‖(H : ℚ_[p])‖ ≤ ‖(X : ℚ_[p])‖ * 1 :=
              mul_le_mul_of_nonneg_left hHn (norm_nonneg _)
          _ = ‖(X : ℚ_[p])‖ := mul_one _
      calc ‖((G k k' : ℤ) : ℚ_[p])‖
          = (p : ℝ) ^ (v : ℤ) * ((p : ℝ) ^ (-(v : ℤ)) * ‖((G k k' : ℤ) : ℚ_[p])‖) := by
            rw [← mul_assoc, ← zpow_add₀ hp0.ne', add_neg_cancel, zpow_zero, one_mul]
        _ ≤ (p : ℝ) ^ (v : ℤ) * ‖(X : ℚ_[p])‖ :=
            mul_le_mul_of_nonneg_left this (zpow_nonneg hp0.le _)
    have hβn : ‖((β k : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one _
    have hαn : ‖((α k' : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one _
    have hpn : ‖((p : ℚ_[p]) ^ (2 * k + 2 * k'))‖ = (p : ℝ) ^ (-((2 * k + 2 * k' : ℕ) : ℤ)) :=
      Padic.norm_p_pow _
    have hTq : (T (k, k') : ℚ_[p]) = (p : ℚ_[p]) ^ (2 * k + 2 * k') * (β k : ℚ_[p]) *
        (α k' : ℚ_[p]) * ((G k k' : ℤ) : ℚ_[p]) := by
      simp only [hT]; push_cast; ring
    rw [hTq, norm_mul, norm_mul, norm_mul, hpn]
    have hexp : (p : ℝ) ^ (-((2 * k + 2 * k' : ℕ) : ℤ)) * (p : ℝ) ^ (v : ℤ) ≤
        (p : ℝ) ^ (-7 : ℤ) := by
      rw [← zpow_add₀ hp0.ne']
      exact zpow_le_zpow_right₀ hp1 (by push_cast; omega)
    calc (p : ℝ) ^ (-((2 * k + 2 * k' : ℕ) : ℤ)) * ‖((β k : ℤ) : ℚ_[p])‖ *
          ‖((α k' : ℤ) : ℚ_[p])‖ * ‖((G k k' : ℤ) : ℚ_[p])‖
        ≤ (p : ℝ) ^ (-((2 * k + 2 * k' : ℕ) : ℤ)) * 1 * 1 *
          ((p : ℝ) ^ (v : ℤ) * ‖(X : ℚ_[p])‖) := by
          gcongr
      _ = ((p : ℝ) ^ (-((2 * k + 2 * k' : ℕ) : ℤ)) * (p : ℝ) ^ (v : ℤ)) * ‖(X : ℚ_[p])‖ := by
          ring
      _ ≤ (p : ℝ) ^ (-7 : ℤ) * ‖(X : ℚ_[p])‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hrest : ‖((∑ q ∈ (R ×ˢ R).erase (1, 2), T q : ℤ) : ℚ_[p])‖ ≤
      (p : ℝ) ^ (-7 : ℤ) * ‖(X : ℚ_[p])‖ := by
    push_cast
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) hnorm_rest
  have hlt : (p : ℝ) ^ (-7 : ℤ) * ‖(X : ℚ_[p])‖ < (p : ℝ) ^ (-6 : ℤ) * ‖(X : ℚ_[p])‖ := by
    apply mul_lt_mul_of_pos_right _ hXn
    exact zpow_lt_zpow_right₀ (by exact_mod_cast hp.out.one_lt) (by norm_num)
  intro h0
  have hneg : T (1, 2) = -∑ q ∈ (R ×ˢ R).erase (1, 2), T q := by linarith
  have := congrArg (fun z : ℤ => ‖(z : ℚ_[p])‖) hneg
  simp only [Int.cast_neg, norm_neg] at this
  rw [hnorm_main] at this
  linarith

end LeanFormalizations.Mills.Skolem

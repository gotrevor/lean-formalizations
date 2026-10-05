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

/-! ### Matrices: Cayley–Hamilton and the binomial expansion -/

/-- Cayley–Hamilton for `3 × 3` integer matrices. -/
theorem cayley_hamilton_three (D : Matrix (Fin 3) (Fin 3) ℤ) :
    ∃ c0 c1 c2 : ℤ, D ^ 3 = c2 • D ^ 2 + c1 • D + c0 • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  have hm := D.charpoly_monic
  have hdeg : D.charpoly.natDegree = 3 := by simp [Matrix.charpoly_natDegree_eq_dim]
  have h := Matrix.aeval_self_charpoly D
  rw [hm.as_sum, hdeg] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add, map_mul,
    aeval_X_pow, aeval_X, aeval_C, pow_zero, pow_one, mul_one, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul] at h
  refine ⟨-D.charpoly.coeff 0, -D.charpoly.coeff 1, -D.charpoly.coeff 2, ?_⟩
  rw [← sub_eq_zero, ← h]
  simp only [neg_smul]
  abel

/-- The coefficients of `D^k` in the basis `D², D, 1` (`D³ = c₂D² + c₁D + c₀`). -/
def chSeq (c0 c1 c2 : ℤ) : ℕ → ℤ × ℤ × ℤ
  | 0 => (0, 0, 1)
  | k + 1 => (c2 * (chSeq c0 c1 c2 k).1 + (chSeq c0 c1 c2 k).2.1,
      c1 * (chSeq c0 c1 c2 k).1 + (chSeq c0 c1 c2 k).2.2, c0 * (chSeq c0 c1 c2 k).1)

theorem pow_eq_chSeq {D : Matrix (Fin 3) (Fin 3) ℤ} {c0 c1 c2 : ℤ}
    (hD : D ^ 3 = c2 • D ^ 2 + c1 • D + c0 • (1 : Matrix (Fin 3) (Fin 3) ℤ)) (k : ℕ) :
    D ^ k = (chSeq c0 c1 c2 k).1 • D ^ 2 + (chSeq c0 c1 c2 k).2.1 • D +
      (chSeq c0 c1 c2 k).2.2 • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  induction k with
  | zero => simp [chSeq]
  | succ k ih =>
    have h3 : D * D ^ 2 = D ^ 3 := by rw [← pow_succ']
    have h2 : D * D = D ^ 2 := by rw [sq]
    have e : D ^ (k + 1) = (chSeq c0 c1 c2 k).1 • D ^ 3 + (chSeq c0 c1 c2 k).2.1 • D ^ 2 +
        (chSeq c0 c1 c2 k).2.2 • D := by
      rw [pow_succ', ih, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_one,
        h3, h2]
    rw [e, hD]
    simp only [chSeq]
    module

theorem chSeq_zero (c0 c1 c2 : ℤ) : chSeq c0 c1 c2 0 = (0, 0, 1) := rfl
theorem chSeq_one (c0 c1 c2 : ℤ) : chSeq c0 c1 c2 1 = (0, 1, 0) := by simp [chSeq]
theorem chSeq_two (c0 c1 c2 : ℤ) : chSeq c0 c1 c2 2 = (1, 0, 0) := by simp [chSeq]

/-- The binomial expansion of `ℓ((c D + 1)^z)`. -/
theorem linear_one_add_pow (L : Matrix (Fin 3) (Fin 3) ℤ →ₗ[ℤ] ℤ)
    (D : Matrix (Fin 3) (Fin 3) ℤ) (c : ℤ) (z : ℕ) :
    L ((c • D + 1) ^ z) = ∑ k ∈ range (z + 1), (z.choose k : ℤ) * c ^ k * L (D ^ k) := by
  rw [(Commute.one_right (c • D)).add_pow',
    Nat.sum_antidiagonal_eq_sum_range_succ (fun m q => z.choose m • ((c • D) ^ m * 1 ^ q)),
    map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, map_nsmul, _root_.smul_pow, map_smul, nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Skolem, matrix form.**  If `ℓ` vanishes on `(p² D + 1)^z` at `z = 0, a, b` (`0 < a < b`),
it vanishes at every `z`. -/
theorem linear_pow_eq_zero_of_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (D : Matrix (Fin 3) (Fin 3) ℤ) (L : Matrix (Fin 3) (Fin 3) ℤ →ₗ[ℤ] ℤ) {a b : ℕ}
    (ha : 0 < a) (hab : a < b) (h0 : L 1 = 0)
    (hza : L (((p : ℤ) ^ 2 • D + 1) ^ a) = 0) (hzb : L (((p : ℤ) ^ 2 • D + 1) ^ b) = 0) (z : ℕ) :
    L (((p : ℤ) ^ 2 • D + 1) ^ z) = 0 := by
  obtain ⟨c0, c1, c2, hD⟩ := cayley_hamilton_three D
  set α : ℕ → ℤ := fun k => (chSeq c0 c1 c2 k).1 with hα
  set β : ℕ → ℤ := fun k => (chSeq c0 c1 c2 k).2.1 with hβ
  set s1 := L D with hs1
  set s2 := L (D ^ 2) with hs2
  have hLk : ∀ k, L (D ^ k) = α k * s2 + β k * s1 := by
    intro k
    rw [pow_eq_chSeq hD k, map_add, map_add, map_smul, map_smul, map_smul, h0]
    simp [hα, hβ, hs1, hs2]
  have hF : ∀ y, L (((p : ℤ) ^ 2 • D + 1) ^ y) = s1 * U p β y + s2 * U p α y := by
    intro y
    rw [linear_one_add_pow, U, U, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hLk, ← pow_mul]
    ring
  have hdet := skolem_det_ne_zero hp2 α β (by simp [hβ, chSeq_zero]) (by simp [hβ, chSeq_one])
    (by simp [hβ, chSeq_two]) (by simp [hα, chSeq_zero]) (by simp [hα, chSeq_one])
    (by simp [hα, chSeq_two]) ha hab
  rw [hF] at hza hzb
  have e1 : s1 * (U p β a * U p α b - U p β b * U p α a) = 0 := by
    linear_combination (U p α b) * hza - (U p α a) * hzb
  have e2 : s2 * (U p β a * U p α b - U p β b * U p α a) = 0 := by
    linear_combination (-(U p β b)) * hza + (U p β a) * hzb
  have hs1' : s1 = 0 := (mul_eq_zero.1 e1).resolve_right hdet
  have hs2' : s2 = 0 := (mul_eq_zero.1 e2).resolve_right hdet
  rw [hF, hs1', hs2']
  ring

/-! ### Recurrences of order 3 -/

open scoped Matrix

/-- The companion matrix of `X³ − a₂X² − a₁X − a₀`. -/
def comp3 (a0 a1 a2 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 1; a0, a1, a2]

theorem det_comp3 (a0 a1 a2 : ℤ) : (comp3 a0 a1 a2).det = a0 := by
  simp [comp3, Matrix.det_fin_three]

/-- The state vector `(w n, w (n+1), w (n+2))`. -/
def state3 (w : ℕ → ℤ) (n : ℕ) : Fin 3 → ℤ := ![w n, w (n + 1), w (n + 2)]

theorem comp3_pow_mulVec {w : ℕ → ℤ} {a0 a1 a2 : ℤ}
    (hrec : ∀ n, w (n + 3) = a2 * w (n + 2) + a1 * w (n + 1) + a0 * w n) (n : ℕ) :
    (comp3 a0 a1 a2 ^ n) *ᵥ state3 w 0 = state3 w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    ext i
    fin_cases i <;> simp [comp3, state3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hrec]
    ring

/-- `M ↦ ((B M) v)₀` as a linear functional. -/
def evalL (B : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ →ₗ[ℤ] ℤ where
  toFun M := ((B * M) *ᵥ v) 0
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mulVec]; rfl
  map_smul' c M := by
    rw [Matrix.mul_smul, Matrix.smul_mulVec]; rfl

/-- A power of an integer matrix whose determinant is prime to `q` is `≡ 1 (mod q)`. -/
theorem exists_pow_eq_smul_add_one (A : Matrix (Fin 3) (Fin 3) ℤ) {q : ℕ} (hq : 0 < q)
    (hdet : IsCoprime A.det (q : ℤ)) :
    ∃ P ≥ 1, ∃ D : Matrix (Fin 3) (Fin 3) ℤ, A ^ P = (q : ℤ) • D + 1 := by
  haveI : NeZero q := ⟨hq.ne'⟩
  set f := Int.castRingHom (ZMod q) with hf
  have hunit_det : IsUnit (f.mapMatrix A).det := by
    rw [← RingHom.map_det]
    obtain ⟨u, v, huv⟩ := hdet
    refine IsUnit.of_mul_eq_one (f u) ?_
    have := congrArg f huv
    rw [map_add, map_mul, map_mul, map_one, map_natCast, ZMod.natCast_self, mul_zero,
      add_zero] at this
    rw [mul_comm]; exact this
  have hunit : IsUnit (f.mapMatrix A) := (Matrix.isUnit_iff_isUnit_det _).2 hunit_det
  obtain ⟨u, hu⟩ := hunit
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  refine ⟨orderOf u, hfin.orderOf_pos, fun i j => (A ^ orderOf u - 1) i j / q, ?_⟩
  have hone : f.mapMatrix (A ^ orderOf u) = 1 := by
    rw [map_pow, ← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  ext i j
  have hij := congrFun (congrFun hone i) j
  have hdvd : (q : ℤ) ∣ (A ^ orderOf u - 1) i j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hf, eq_intCast] at hij
    rw [Matrix.sub_apply, Int.cast_sub, hij]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Int.mul_ediv_cancel' hdvd, Matrix.sub_apply]
  ring

/-- **Skolem's lemma for order-3 recurrences**: for an odd prime `p ∤ a₀` there is a period `P`
such that three zeros in a class `n₀ + Pℕ` force all later terms of the class to vanish. -/
theorem skolem_three_zeros {w : ℕ → ℤ} {a0 a1 a2 : ℤ}
    (hrec : ∀ n, w (n + 3) = a2 * w (n + 2) + a1 * w (n + 1) + a0 * w n)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpa : ¬ (p : ℤ) ∣ a0) :
    ∃ P ≥ 1, ∀ n0 y1 y2 y3 : ℕ, y1 < y2 → y2 < y3 → w (n0 + P * y1) = 0 →
      w (n0 + P * y2) = 0 → w (n0 + P * y3) = 0 → ∀ z, w (n0 + P * (y1 + z)) = 0 := by
  set A := comp3 a0 a1 a2 with hA
  have hcop : IsCoprime A.det ((p ^ 2 : ℕ) : ℤ) := by
    rw [hA, det_comp3]
    push_cast
    apply IsCoprime.pow_right
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
    exact ((Prime.coprime_iff_not_dvd hpz).2 hpa).symm
  obtain ⟨P, hP, D, hAD⟩ := exists_pow_eq_smul_add_one A (pow_pos hp.out.pos 2) hcop
  refine ⟨P, hP, fun n0 y1 y2 y3 h12 h23 hz1 hz2 hz3 z => ?_⟩
  have hw : ∀ m, w (n0 + P * m) = evalL (A ^ n0) (state3 w 0) (((p : ℤ) ^ 2 • D + 1) ^ m) := by
    intro m
    have : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 := by push_cast; ring
    rw [this] at hAD
    show _ = ((A ^ n0 * ((p : ℤ) ^ 2 • D + 1) ^ m) *ᵥ state3 w 0) 0
    rw [← hAD, ← pow_mul, ← pow_add, comp3_pow_mulVec hrec]
    rfl
  set L := (evalL (A ^ n0) (state3 w 0)).comp
    (LinearMap.mulLeft ℤ (((p : ℤ) ^ 2 • D + 1) ^ y1)) with hL
  have hshift : ∀ m, L (((p : ℤ) ^ 2 • D + 1) ^ m) = w (n0 + P * (y1 + m)) := by
    intro m
    rw [hw, hL, LinearMap.comp_apply, LinearMap.mulLeft_apply, ← pow_add]
  have h0 : L 1 = 0 := by
    have := hshift 0
    rw [pow_zero, add_zero] at this
    rw [this, hz1]
  have ha : L (((p : ℤ) ^ 2 • D + 1) ^ (y2 - y1)) = 0 := by
    rw [hshift, show y1 + (y2 - y1) = y2 by omega, hz2]
  have hb : L (((p : ℤ) ^ 2 • D + 1) ^ (y3 - y1)) = 0 := by
    rw [hshift, show y1 + (y3 - y1) = y3 by omega, hz3]
  rw [← hshift]
  exact linear_pow_eq_zero_of_three hp2 D L (by omega) (by omega) h0 ha hb z

/-- **Skolem–Mahler–Lech for order 3 (non-degenerate case).**  If no arithmetic progression is
eventually a zero set of `w`, the zeros of `w` are finite. -/
theorem eventually_ne_zero_of_recurrence {w : ℕ → ℤ} {a0 a1 a2 : ℤ}
    (hrec : ∀ n, w (n + 3) = a2 * w (n + 2) + a1 * w (n + 1) + a0 * w n) (ha0 : a0 ≠ 0)
    (hnd : ∀ P ≥ 1, ∀ m, ∃ z, w (m + P * z) ≠ 0) :
    ∀ᶠ n in Filter.atTop, w n ≠ 0 := by
  obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (a0.natAbs + 3)
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by omega
  have hpa : ¬ (p : ℤ) ∣ a0 := by
    intro h
    have := Int.natAbs_dvd_natAbs.2 h
    simp only [Int.natAbs_natCast] at this
    have := Nat.le_of_dvd (Int.natAbs_pos.2 ha0) this
    omega
  obtain ⟨P, hP, hsk⟩ := skolem_three_zeros hrec hp2 hpa
  -- each class `r + Pℕ` has a last zero
  have hclass : ∀ r, ∃ B, ∀ y ≥ B, w (r + P * y) ≠ 0 := by
    intro r
    by_contra hcon
    push Not at hcon
    obtain ⟨y1, -, hz1⟩ := hcon 0
    obtain ⟨y2, hy2, hz2⟩ := hcon (y1 + 1)
    obtain ⟨y3, hy3, hz3⟩ := hcon (y2 + 1)
    obtain ⟨z, hz⟩ := hnd P hP (r + P * y1)
    apply hz
    rw [show r + P * y1 + P * z = r + P * (y1 + z) by ring]
    exact hsk r y1 y2 y3 (by omega) (by omega) hz1 hz2 hz3 z
  choose B hB using hclass
  set M := (Finset.range P).sup B with hM
  rw [Filter.eventually_atTop]
  refine ⟨P * (M + 1), fun n hn => ?_⟩
  have hr : n % P < P := Nat.mod_lt _ (by omega)
  have hBr : B (n % P) ≤ M := Finset.le_sup (f := B) (Finset.mem_range.2 hr)
  have hy : M ≤ n / P := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    nlinarith
  have := hB (n % P) (n / P) (le_trans hBr hy)
  rwa [Nat.mod_add_div] at this

end LeanFormalizations.Mills.Skolem

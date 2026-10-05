/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.PisotGalois
import LeanFormalizations.NumberTheory.Mills.Skolem

/-!
# Phase 62, lap 3: `e₂(β^n) ≠ 0` eventually, for every cubic Pisot `β`

For a cubic Pisot `β` with other conjugates `γ₁, γ₂`,

  `e₂(β^n) = β^n (γ₁^n + γ₂^n) + (γ₁γ₂)^n = λ₁^n + λ₂^n + λ₃^n`,
  `λ₁ = βγ₁, λ₂ = βγ₂, λ₃ = γ₁γ₂`.

With `X³ + c₂X² + c₁X + c₀` the integer minimal polynomial (Vieta), the `λᵢ` are the roots of
`X³ − c₁X² + c₀c₂X − c₀²`, so `e₂(β^n)` is the integer recurrence `e2seq`
(`e2seq_eq`).  It is non-degenerate: the `λᵢ^P` are pairwise distinct
(`PisotGalois.pow_ne_pow_of_roots`), so no progression `m + Pℕ` is a zero set (Vandermonde).
Skolem (`Skolem.eventually_ne_zero_of_recurrence`, constant term `c₀² ≠ 0`) gives the claim.
-/

namespace LeanFormalizations.Mills.E2Skolem

open Polynomial Filter LeanFormalizations.Literature LeanFormalizations.Mills
open LeanFormalizations.Mills.ShiftedMillsLarge LeanFormalizations.Mills.PisotGalois

/-- The integer sequence `λ₁^n + λ₂^n + λ₃^n` for the roots of `X³ − c₁X² + c₀c₂X − c₀²`. -/
def e2seq (c0 c1 c2 : ℤ) : ℕ → ℤ
  | 0 => 3
  | 1 => c1
  | 2 => c1 ^ 2 - 2 * (c0 * c2)
  | n + 3 => c1 * e2seq c0 c1 c2 (n + 2) - c0 * c2 * e2seq c0 c1 c2 (n + 1) +
      c0 ^ 2 * e2seq c0 c1 c2 n

theorem e2seq_rec (c0 c1 c2 : ℤ) (n : ℕ) :
    e2seq c0 c1 c2 (n + 3) = c1 * e2seq c0 c1 c2 (n + 2) + (-(c0 * c2)) * e2seq c0 c1 c2 (n + 1) +
      c0 ^ 2 * e2seq c0 c1 c2 n := by
  rw [e2seq]; ring

/-- The cubic expansion. -/
theorem cubic_expand (a b c : ℂ) :
    (X - C a) * ((X - C b) * ((X - C c) * 1)) =
      X ^ 3 + C (-(a + b + c)) * X ^ 2 + C (a * b + a * c + b * c) * X + C (-(a * b * c)) := by
  simp only [map_neg, map_add, map_mul]
  ring

/-- **Vieta** for a cubic Pisot number. -/
theorem vieta_cubic {β : ℝ} (hβ : IsPisot β) {γ1 γ2 : ℂ} (hoc : otherConj β = {γ1, γ2}) :
    (((minpoly ℤ β).coeff 0 : ℤ) : ℂ) = -((β : ℂ) * γ1 * γ2) ∧
      (((minpoly ℤ β).coeff 1 : ℤ) : ℂ) = β * γ1 + β * γ2 + γ1 * γ2 ∧
      (((minpoly ℤ β).coeff 2 : ℤ) : ℂ) = -((β : ℂ) + γ1 + γ2) := by
  have hint := hβ.2.1
  set fC := (minpoly ℤ β).map (Int.castRingHom ℂ) with hfC
  have hmon : fC.Monic := (minpoly_int_monic hint).map _
  have hβmem : (β : ℂ) ∈ (minpoly ℚ β).aroots ℂ := by
    rw [aroots_eq_roots hint]
    exact (mem_roots hmon.ne_zero).2 (eval_beta β)
  have hroots : fC.roots = (β : ℂ) ::ₘ γ1 ::ₘ γ2 ::ₘ 0 := by
    rw [hfC, ← aroots_eq_roots hint, ← Multiset.cons_erase hβmem]
    rw [otherConj] at hoc
    rw [hoc]
    rfl
  have hfac : fC = (fC.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits fC).eq_prod_roots_of_monic hmon
  rw [hroots] at hfac
  simp only [Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero] at hfac
  rw [cubic_expand] at hfac
  have hco : ∀ i, fC.coeff i = (((minpoly ℤ β).coeff i : ℤ) : ℂ) := fun i => by
    rw [hfC, coeff_map]; simp
  refine ⟨?_, ?_, ?_⟩ <;> rw [← hco, hfac] <;>
    simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] <;> norm_num

/-- `e2seq` is the power sum of the `λᵢ`. -/
theorem e2seq_eq {β γ1 γ2 : ℂ} {c0 c1 c2 : ℤ} (hc0 : (c0 : ℂ) = -(β * γ1 * γ2))
    (hc1 : (c1 : ℂ) = β * γ1 + β * γ2 + γ1 * γ2) (hc2 : (c2 : ℂ) = -(β + γ1 + γ2)) (n : ℕ) :
    (e2seq c0 c1 c2 n : ℂ) = (β * γ1) ^ n + (β * γ2) ^ n + (γ1 * γ2) ^ n := by
  have hroot : ∀ x : ℂ, x = β * γ1 ∨ x = β * γ2 ∨ x = γ1 * γ2 →
      x ^ 3 = (c1 : ℂ) * x ^ 2 - (c0 : ℂ) * c2 * x + (c0 : ℂ) ^ 2 := by
    intro x hx
    rw [hc0, hc1, hc2]
    rcases hx with rfl | rfl | rfl <;> ring
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [e2seq]; norm_num
    | 1 => simp [e2seq, hc1]
    | 2 => simp only [e2seq]; push_cast; rw [hc0, hc1, hc2]; ring
    | k + 3 =>
      rw [e2seq]
      push_cast
      rw [ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]
      have r1 := hroot (β * γ1) (Or.inl rfl)
      have r2 := hroot (β * γ2) (Or.inr (Or.inl rfl))
      have r3 := hroot (γ1 * γ2) (Or.inr (Or.inr rfl))
      linear_combination -(β * γ1) ^ k * r1 - (β * γ2) ^ k * r2 - (γ1 * γ2) ^ k * r3

/-- **Skolem for `e₂`**: for a cubic Pisot `β`, `e₂(β^n) = β^n S(n) + (γ₁γ₂)^n ≠ 0` for all
large `n`. -/
theorem eventually_e2_ne_zero {β : ℝ} (hβ : IsPisot β)
    (hcard : Multiset.card (otherConj β) = 2) :
    ∀ᶠ n : ℕ in atTop, (β : ℂ) ^ n * conjPowSum β n + (otherConj β).prod ^ n ≠ 0 := by
  have hint := hβ.2.1
  have hβ0 : (β : ℂ) ≠ 0 := by
    have : (0 : ℝ) < β := by linarith [hβ.1]
    exact_mod_cast this.ne'
  obtain ⟨γ1, γ2, hoc⟩ := Multiset.card_eq_two.1 hcard
  obtain ⟨hc0, hc1, hc2⟩ := vieta_cubic hβ hoc
  set c0 := (minpoly ℤ β).coeff 0 with hc0d
  set c1 := (minpoly ℤ β).coeff 1 with hc1d
  set c2 := (minpoly ℤ β).coeff 2 with hc2d
  -- the roots
  set fC := (minpoly ℤ β).map (Int.castRingHom ℂ) with hfC
  have hmon : fC.Monic := (minpoly_int_monic hint).map _
  have hβmem : (β : ℂ) ∈ (minpoly ℚ β).aroots ℂ := by
    rw [aroots_eq_roots hint]
    exact (mem_roots hmon.ne_zero).2 (eval_beta β)
  have hsep : (minpoly ℚ β).Separable := (minpoly.irreducible hint.tower_top).separable
  have hnodup : ((minpoly ℚ β).aroots ℂ).Nodup := nodup_roots ((separable_map _).mpr hsep)
  have hcons : (minpoly ℚ β).aroots ℂ = (β : ℂ) ::ₘ γ1 ::ₘ γ2 ::ₘ 0 := by
    rw [← Multiset.cons_erase hβmem]
    rw [otherConj] at hoc
    rw [hoc]; rfl
  rw [hcons] at hnodup
  simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.notMem_zero, or_false,
    not_or] at hnodup
  obtain ⟨⟨hβγ1, hβγ2⟩, hγ12, -⟩ := hnodup
  have hroot : ∀ z ∈ (minpoly ℚ β).aroots ℂ, fC.eval z = 0 := by
    intro z hz
    rw [aroots_eq_roots hint] at hz
    exact (mem_roots hmon.ne_zero).1 hz
  have hrγ1 := hroot γ1 (by rw [hcons]; simp)
  have hrγ2 := hroot γ2 (by rw [hcons]; simp)
  have hrβ := hroot β (by rw [hcons]; simp)
  -- `c₀ ≠ 0`
  have hc0ne : c0 ≠ 0 := by
    intro h
    have : (minpoly ℚ β).coeff 0 = 0 := by rw [minpoly_map_rat hint, coeff_map, ← hc0d, h, map_zero]
    exact minpoly.coeff_zero_ne_zero hint.tower_top (by linarith [hβ.1] : β ≠ 0) this
  have hγ10 : γ1 ≠ 0 := by
    intro h; apply hc0ne; exact_mod_cast (by rw [hc0, h]; ring : (c0 : ℂ) = 0)
  have hγ20 : γ2 ≠ 0 := by
    intro h; apply hc0ne; exact_mod_cast (by rw [hc0, h]; ring : (c0 : ℂ) = 0)
  -- the expression is `e2seq`
  have hexpr : ∀ n, (β : ℂ) ^ n * conjPowSum β n + (otherConj β).prod ^ n =
      (e2seq c0 c1 c2 n : ℂ) := by
    intro n
    rw [e2seq_eq hc0 hc1 hc2, conjPowSum, hoc]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    ring
  -- non-degeneracy
  have hnd : ∀ P ≥ 1, ∀ m, ∃ z, e2seq c0 c1 c2 (m + P * z) ≠ 0 := by
    intro P hP m
    by_contra hcon
    push Not at hcon
    have hz : ∀ z, (β * γ1) ^ m * ((β * γ1) ^ P) ^ z + (β * γ2) ^ m * ((β * γ2) ^ P) ^ z +
        (γ1 * γ2) ^ m * ((γ1 * γ2) ^ P) ^ z = 0 := by
      intro z
      have := hcon z
      have h2 : (e2seq c0 c1 c2 (m + P * z) : ℂ) = 0 := by exact_mod_cast this
      rw [e2seq_eq hc0 hc1 hc2] at h2
      rw [← h2]
      simp only [← pow_mul, ← pow_add]
    have e0 := hz 0
    have e1 := hz 1
    have e2 := hz 2
    have hx12 : (β * γ1) ^ P ≠ (β * γ2) ^ P := by
      intro h
      rw [mul_pow, mul_pow] at h
      exact pow_ne_pow_of_roots hβ hrγ1 hrγ2 hγ12 hP
        (mul_left_cancel₀ (pow_ne_zero _ hβ0) h)
    have hx13 : (β * γ1) ^ P ≠ (γ1 * γ2) ^ P := by
      intro h
      rw [mul_pow, mul_pow, mul_comm ((γ1) ^ P)] at h
      exact pow_ne_pow_of_roots hβ hrβ hrγ2 hβγ2 hP
        (mul_right_cancel₀ (pow_ne_zero _ hγ10) h)
    have hx23 : (β * γ2) ^ P ≠ (γ1 * γ2) ^ P := by
      intro h
      rw [mul_pow, mul_pow] at h
      exact pow_ne_pow_of_roots hβ hrβ hrγ1 hβγ1 hP
        (mul_right_cancel₀ (pow_ne_zero _ hγ20) h)
    set x1 := (β * γ1) ^ P
    set x2 := (β * γ2) ^ P
    set x3 := (γ1 * γ2) ^ P
    have hv : (β * γ1) ^ m * ((x1 - x2) * (x1 - x3)) = 0 := by
      simp only [pow_zero, pow_one, mul_one] at e0 e1
      linear_combination e2 - (x2 + x3) * e1 + x2 * x3 * e0
    rcases mul_eq_zero.1 hv with h | h
    · exact pow_ne_zero m (mul_ne_zero hβ0 hγ10) h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact hx12 (sub_eq_zero.1 h')
      · exact hx13 (sub_eq_zero.1 h')
  have hev := Skolem.eventually_ne_zero_of_recurrence (e2seq_rec c0 c1 c2)
    (pow_ne_zero 2 hc0ne) hnd
  filter_upwards [hev] with n hn
  rw [hexpr]
  exact_mod_cast hn

end LeanFormalizations.Mills.E2Skolem

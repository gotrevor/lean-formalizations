/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The shifted nested-interval construction

`Basic.lean` builds a Mills number from a prime chain by putting `b k` at exponent `3^k`, so its
`A` is `≳ 2`.  Mills' *constant* is the least Mills number, `≈ 1.3063…`: there the chain is
**shifted by one**, `b k` sitting at exponent `3^(k+1)` (so `⌊A^3⌋₊ = 2`, `⌊A^9⌋₊ = 11`, …).

This file is the shifted engine, stated for an abstract chain: given primes `b 0 < b 1 < …` with
`(b k)³ < b (k+1)` and `b (k+1) + 1 < (b k + 1)³`, there is an `A > 1` with
`⌊A^(3^(k+1))⌋₊ = b k` for every `k`.  `RH.lean` feeds it the greedy chain `2, 11, 1361, …`.
-/
import Mathlib
import LeanFormalizations.NumberTheory.Mills.Basic

namespace LeanFormalizations.Mills

namespace Chain

/-- `(x³) ^ (3^(k+1))⁻¹ = x ^ (3^k)⁻¹`: cubing eats one level of the root. -/
private lemma cube_root_step {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ (3:ℕ)) ^ ((((3:ℕ) ^ (k+1) : ℕ) : ℝ))⁻¹ = x ^ ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹ := by
  rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
  congr 1
  have hk : (((3:ℕ) ^ k : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

variable (b : ℕ → ℕ)

/-- Left endpoints of the shifted nested intervals. -/
private noncomputable def mu (k : ℕ) : ℝ := (b k : ℝ) ^ ((((3:ℕ) ^ (k+1) : ℕ) : ℝ))⁻¹
/-- Right endpoints of the shifted nested intervals. -/
private noncomputable def nu (k : ℕ) : ℝ := ((b k : ℝ) + 1) ^ ((((3:ℕ) ^ (k+1) : ℕ) : ℝ))⁻¹

private lemma exp_pos (k : ℕ) : (0:ℝ) < ((((3:ℕ) ^ k : ℕ) : ℝ))⁻¹ := by positivity

variable (hlo : ∀ k, (b k) ^ 3 < b (k + 1)) (hhi : ∀ k, b (k + 1) + 1 < (b k + 1) ^ 3)

include hlo in
private lemma mu_lt_succ (k : ℕ) : mu b k < mu b (k + 1) := by
  have hlt : ((b k : ℝ)) ^ (3:ℕ) < (b (k+1) : ℝ) := by exact_mod_cast hlo k
  have := Real.rpow_lt_rpow (by positivity) hlt (exp_pos (k+2))
  rwa [cube_root_step (x := (b k : ℝ)) (by positivity) (k+1)] at this

include hhi in
private lemma nu_succ_lt (k : ℕ) : nu b (k + 1) < nu b k := by
  have hlt : (b (k+1) : ℝ) + 1 < ((b k : ℝ) + 1) ^ (3:ℕ) := by
    have hc : ((b (k+1) + 1 : ℕ) : ℝ) < (((b k + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hhi k
    push_cast at hc; linarith
  have := Real.rpow_lt_rpow (by positivity) hlt (exp_pos (k+2))
  rwa [cube_root_step (x := (b k : ℝ) + 1) (by positivity) (k+1)] at this

private lemma mu_lt_nu (k : ℕ) : mu b k < nu b k :=
  Real.rpow_lt_rpow (by positivity) (by linarith) (exp_pos (k+1))

include hlo hhi in
private lemma mu_le_nu (m k : ℕ) : mu b m ≤ nu b k := by
  have hmono : Monotone (mu b) := monotone_nat_of_le_succ fun n => (mu_lt_succ b hlo n).le
  have hanti : Antitone (nu b) := antitone_nat_of_succ_le fun n => (nu_succ_lt b hhi n).le
  rcases le_total m k with hmk | hmk
  · exact le_trans (hmono hmk) (mu_lt_nu b k).le
  · exact le_trans (mu_lt_nu b m).le (hanti hmk)

include hlo hhi in
private lemma mu_bddAbove : BddAbove (Set.range (mu b)) :=
  ⟨nu b 0, by rintro _ ⟨m, rfl⟩; exact mu_le_nu b hlo hhi m 0⟩

private lemma pow_mu (k : ℕ) : (mu b k) ^ ((3:ℕ) ^ (k+1)) = (b k : ℝ) :=
  Real.rpow_inv_natCast_pow (by positivity) (by positivity)

private lemma pow_nu (k : ℕ) : (nu b k) ^ ((3:ℕ) ^ (k+1)) = (b k : ℝ) + 1 :=
  Real.rpow_inv_natCast_pow (by positivity) (by positivity)

include hlo hhi in
private lemma floor_pow_iSup (k : ℕ) :
    ⌊(⨆ n, mu b n) ^ ((3:ℕ) ^ (k+1))⌋₊ = b k := by
  set A : ℝ := ⨆ n, mu b n with hA
  have hlo' : mu b k < A :=
    lt_of_lt_of_le (mu_lt_succ b hlo k) (le_ciSup (mu_bddAbove b hlo hhi) (k+1))
  have hhi' : A < nu b k :=
    lt_of_le_of_lt (ciSup_le fun m => mu_le_nu b hlo hhi m (k+1)) (nu_succ_lt b hhi k)
  have hmupos : (0:ℝ) ≤ mu b k := by unfold mu; positivity
  have h1 : (b k : ℝ) < A ^ ((3:ℕ) ^ (k+1)) := by
    rw [← pow_mu b k]; exact pow_lt_pow_left₀ hlo' hmupos (by positivity)
  have h2 : A ^ ((3:ℕ) ^ (k+1)) < (b k : ℝ) + 1 := by
    rw [← pow_nu b k]
    exact pow_lt_pow_left₀ hhi' (le_of_lt (lt_of_le_of_lt hmupos hlo')) (by positivity)
  have hnn : (0:ℝ) ≤ A ^ ((3:ℕ) ^ (k+1)) := le_trans (Nat.cast_nonneg _) h1.le
  rw [Nat.floor_eq_iff hnn]
  exact ⟨h1.le, h2⟩

end Chain

/-- **The shifted construction.**  A prime chain with `(b k)³ < b (k+1)` and
`b (k+1) + 1 < (b k + 1)³`, starting at `b 0 ≥ 2`, yields a real `A > 1` whose floors at the
exponents `3^(k+1)` are exactly the chain. -/
theorem exists_shifted_of_chain {b : ℕ → ℕ} (h2 : 2 ≤ b 0)
    (hlo : ∀ k, (b k) ^ 3 < b (k + 1)) (hhi : ∀ k, b (k + 1) + 1 < (b k + 1) ^ 3) :
    ∃ A : ℝ, 1 < A ∧ ∀ k, ⌊A ^ ((3:ℕ) ^ (k+1))⌋₊ = b k := by
  refine ⟨(⨆ n, Chain.mu b n), ?_, fun k => Chain.floor_pow_iSup b hlo hhi k⟩
  have hfl := Chain.floor_pow_iSup b hlo hhi 0
  have hApos : 0 < (⨆ n, Chain.mu b n) := by
    have hle : Chain.mu b 0 ≤ (⨆ n, Chain.mu b n) := le_ciSup (Chain.mu_bddAbove b hlo hhi) 0
    refine lt_of_lt_of_le ?_ hle
    unfold Chain.mu
    positivity
  have hge : (2:ℝ) ≤ (⨆ n, Chain.mu b n) ^ ((3:ℕ) ^ (0+1)) := by
    refine le_trans ?_ (Nat.floor_le (by positivity))
    rw [hfl]; exact_mod_cast h2
  norm_num at hge
  by_contra hcon
  push Not at hcon
  have := pow_le_one₀ hApos.le hcon (n := 3)
  linarith

end LeanFormalizations.Mills

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The finite-`j` Dubickas recursion

Step 4 of the "no-gap" route (`PROBE-DUBICKAS-NOGAP.md`), part 2.  With `b u j := −A_{2u+1} j`
(so `b u j = A_{2u} j` for `u ≥ 1` and large `j`, and `b 0 j = −A_1 j → −C`), the Graeffe
identity becomes, for `k ≥ 1`,

    2·b k j = Σ_{u+v=k−1} b u j · b v j + (b ((k−1)/2) (j+1) if k is odd) + O(q_j²).

Reading it off: multiply `eSmall_graeffe_isolate` by `β^(2·2^j)`; the pairs `(p₁,p₂)` of the
Graeffe sum with `p₁` odd are exactly the image of `antidiagonal (k−1)` under
`(u,v) ↦ (2u+1, 2v+1)` and contribute `b u j · b v j` each, while the pairs with `p₁` even carry
a spare `q_j²`, as does the `e_k(j+1)` term when `k` is even.

## Status: SORRY-FREE
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasNormalized

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Transcendence LeanFormalizations.Mills
open LeanFormalizations.Literature

variable {β : ℝ}

/-- `b u j = −A_{2u+1} j`. -/
noncomputable def bb (β : ℝ) (u j : ℕ) : ℂ := -AA β (2 * u + 1) j

theorem pw_odd (u : ℕ) : pw (2 * u + 1) = 1 := by unfold pw; simp [Nat.mul_add_mod]
theorem pw_even {n : ℕ} (h : n % 2 = 0) : pw n = 2 := by unfold pw; simp [h]

/-- `b u j = A_{2u} j` for `u ≥ 1` and all large `j`. -/
theorem bb_eq_AA (hβ : IsPisot β) {U : ℝ} {J₀ : ℕ}
    (hbase : ∀ j ≥ J₀, ‖eSmall β 1 (2 ^ j)‖ ≤ U * qq β j) {u : ℕ} (hu : 1 ≤ u) :
    ∃ J : ℕ, ∀ j ≥ J, bb β u j = AA β (2 * u) j := by
  obtain ⟨J, hJ⟩ := AA_odd_succ hβ hbase hu
  exact ⟨J, fun j hj => by rw [bb, hJ j hj, neg_neg]⟩

/-- `eSmall` in terms of `A` and `q`. -/
theorem eSmall_eq_AA_mul (hβ1 : 1 < β) (n j : ℕ) :
    eSmall β n (2 ^ j) = AA β n j * ((qq β j : ℝ) : ℂ) ^ pw n := by
  have hBQ : ((β : ℂ) ^ 2 ^ j) * ((qq β j : ℝ) : ℂ) = 1 := by
    have h := beta_mul_qq hβ1 j
    have h2 : (((β ^ 2 ^ j * qq β j : ℝ)) : ℂ) = ((1 : ℝ) : ℂ) := by rw [h]
    push_cast at h2
    exact h2
  rw [AA, mul_assoc, ← mul_pow, hBQ, one_pow, mul_one]

/-- **The finite-`j` recursion.** -/
theorem bb_rec_approx (hβ : IsPisot β) {U : ℝ} {J₀ : ℕ}
    (hbase : ∀ j ≥ J₀, ‖eSmall β 1 (2 ^ j)‖ ≤ U * qq β j) {k : ℕ} (hk : 1 ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ J : ℕ, ∀ j ≥ J,
      ‖2 * bb β k j - ((∑ p ∈ Finset.antidiagonal (k - 1), bb β p.1 j * bb β p.2 j)
        + (if k % 2 = 1 then bb β ((k - 1) / 2) (j + 1) else 0))‖ ≤ M * qq β j ^ 2 := by
  classical
  have hβ1 : 1 < β := hβ.1
  have hβ0 : (0 : ℝ) < β := by linarith
  obtain ⟨C, hC0, J₁, hJ₁⟩ := norm_AA_le hβ hbase (2 * k + 1)
  obtain ⟨J₂, hJ₂⟩ := bb_eq_AA hβ hbase hk
  refine ⟨C + (2 * k + 1) * C ^ 2, by positivity, max J₁ J₂, fun j hj => ?_⟩
  have hj1 : J₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj2 : J₂ ≤ j := le_trans (le_max_right _ _) hj
  set Q : ℂ := ((qq β j : ℝ) : ℂ) with hQdef
  have hQ0 : Q ≠ 0 := by
    rw [hQdef]
    exact_mod_cast ne_of_gt (qq_pos hβ1 j)
  set F : Finset (ℕ × ℕ) := {p ∈ Finset.antidiagonal (2 * k) | p.1 ≠ 0 ∧ p.2 ≠ 0} with hFdef
  -- rewrite every `eSmall` in terms of `A` and `Q`
  have heA : ∀ n : ℕ, eSmall β n (2 ^ j) = AA β n j * Q ^ pw n := fun n =>
    eSmall_eq_AA_mul hβ1 n j
  have hQsucc : ((qq β (j + 1) : ℝ) : ℂ) = Q ^ 2 := by
    rw [qq_succ hβ1 j, hQdef]; push_cast; ring
  have heA' : eSmall β k (2 ^ (j + 1)) = AA β k (j + 1) * (Q ^ 2) ^ pw k := by
    rw [eSmall_eq_AA_mul hβ1 k (j + 1), hQsucc]
  -- the odd half of the Graeffe sum, reindexed
  have hodd : (∑ q ∈ Finset.antidiagonal (k - 1), -(bb β q.1 j * bb β q.2 j * Q ^ 2))
      = ∑ p ∈ {p ∈ F | p.1 % 2 = 1},
          (-1 : ℂ) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j) := by
    refine Finset.sum_nbij' (i := fun q : ℕ × ℕ => (2 * q.1 + 1, 2 * q.2 + 1))
      (j := fun p : ℕ × ℕ => ((p.1 - 1) / 2, (p.2 - 1) / 2)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_antidiagonal] at hq
      simp only [hFdef, Finset.mem_filter, Finset.mem_antidiagonal]
      omega
    · intro p hp
      simp only [hFdef, Finset.mem_filter, Finset.mem_antidiagonal] at hp
      rw [Finset.mem_antidiagonal]
      omega
    · intro q _; simp only [Prod.ext_iff]; omega
    · intro p hp
      simp only [hFdef, Finset.mem_filter, Finset.mem_antidiagonal] at hp
      simp only [Prod.ext_iff]
      omega
    · intro q hq
      rw [Finset.mem_antidiagonal] at hq
      dsimp only
      rw [heA, heA, pw_odd, pw_odd, pow_one]
      have h1 : AA β (2 * q.1 + 1) j = -bb β q.1 j := by rw [bb, neg_neg]
      have h2 : AA β (2 * q.2 + 1) j = -bb β q.2 j := by rw [bb, neg_neg]
      have h3 : (-1 : ℂ) ^ (2 * q.1 + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      rw [h1, h2, h3]
      ring
  -- the even half
  have heven : ∀ p ∈ {p ∈ F | ¬ p.1 % 2 = 1},
      (-1 : ℂ) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j)
        = AA β p.1 j * AA β p.2 j * Q ^ 4 := by
    intro p hp
    simp only [hFdef, Finset.mem_filter, Finset.mem_antidiagonal] at hp
    obtain ⟨⟨hsum, h1, h2⟩, hpar⟩ := hp
    have he1 : p.1 % 2 = 0 := by omega
    have he2 : p.2 % 2 = 0 := by omega
    rw [heA, heA, pw_even he1, pw_even he2]
    have hs : (-1 : ℂ) ^ p.1 = 1 := by
      obtain ⟨t, ht⟩ : ∃ t, p.1 = 2 * t := ⟨p.1 / 2, by omega⟩
      rw [ht, pow_mul]; norm_num
    rw [hs]
    ring
  -- assemble the Graeffe identity
  have hiso := eSmall_graeffe_isolate β hk j
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun p : ℕ × ℕ => p.1 % 2 = 1)
    (fun p => (-1 : ℂ) ^ p.1 * eSmall β p.1 (2 ^ j) * eSmall β p.2 (2 ^ j))
  rw [← hodd, Finset.sum_congr rfl heven] at hsplit
  rw [← hsplit, heA'] at hiso
  rw [heA, pw_even (by omega : (2 * k) % 2 = 0)] at hiso
  -- `bb k j = A_{2k} j`
  rw [← hJ₂ j hj2] at hiso
  -- pull the sums out
  have hS1 : (∑ q ∈ Finset.antidiagonal (k - 1), -(bb β q.1 j * bb β q.2 j * Q ^ 2))
      = -((∑ q ∈ Finset.antidiagonal (k - 1), bb β q.1 j * bb β q.2 j) * Q ^ 2) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  have hS2 : (∑ p ∈ {p ∈ F | ¬ p.1 % 2 = 1}, AA β p.1 j * AA β p.2 j * Q ^ 4)
      = (∑ p ∈ {p ∈ F | ¬ p.1 % 2 = 1}, AA β p.1 j * AA β p.2 j) * Q ^ 4 := by
    rw [Finset.sum_mul]
  rw [hS1, hS2] at hiso
  -- divide by `Q²` and identify the error term
  set S : ℂ := ∑ q ∈ Finset.antidiagonal (k - 1), bb β q.1 j * bb β q.2 j with hSdef
  set T : ℂ := ∑ p ∈ {p ∈ F | ¬ p.1 % 2 = 1}, AA β p.1 j * AA β p.2 j with hTdef
  have hmain : 2 * bb β k j - (S + (if k % 2 = 1 then bb β ((k - 1) / 2) (j + 1) else 0))
      = (if k % 2 = 1 then 0 else (-1 : ℂ) ^ k * AA β k (j + 1) * Q ^ 2) - T * Q ^ 2 := by
    by_cases hkpar : k % 2 = 1
    · -- `k` odd: `pw k = 1` and `(−1)^k A_k(j+1) = b_{(k−1)/2}(j+1)`
      obtain ⟨t, ht⟩ : ∃ t, k = 2 * t + 1 := ⟨(k - 1) / 2, by omega⟩
      have hpwk : pw k = 1 := by rw [ht]; exact pw_odd t
      have hsig : (-1 : ℂ) ^ k = -1 := by rw [ht, pow_succ, pow_mul]; norm_num
      have hbt : AA β k (j + 1) = -bb β ((k - 1) / 2) (j + 1) := by
        rw [bb, neg_neg, ht]; congr 1; omega
      rw [hpwk, hsig, hbt] at hiso
      rw [if_pos hkpar, if_pos hkpar]
      have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero 2 hQ0
      refine mul_right_cancel₀ hQ2 ?_
      rw [hQdef] at hiso ⊢
      push_cast at hiso ⊢
      linear_combination hiso
    · -- `k` even: `pw k = 2`
      have hpwk : pw k = 2 := pw_even (by omega)
      rw [hpwk] at hiso
      rw [if_neg hkpar, if_neg hkpar]
      have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero 2 hQ0
      refine mul_right_cancel₀ hQ2 ?_
      rw [hQdef] at hiso ⊢
      push_cast at hiso ⊢
      linear_combination hiso
  rw [hmain]
  -- bound the error
  have hQnorm : ‖Q‖ = qq β j := by
    rw [hQdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (qq_pos hβ1 j)]
  have hQ2n : ‖Q ^ 2‖ = qq β j ^ 2 := by rw [norm_pow, hQnorm]
  have hTb : ‖T‖ ≤ (2 * k + 1) * C ^ 2 := by
    rw [hTdef]
    refine le_trans (norm_sum_le _ _) ?_
    have hb : ∀ p ∈ {p ∈ F | ¬ p.1 % 2 = 1}, ‖AA β p.1 j * AA β p.2 j‖ ≤ C ^ 2 := by
      intro p hp
      simp only [hFdef, Finset.mem_filter, Finset.mem_antidiagonal] at hp
      obtain ⟨⟨hsum, h1, h2⟩, _⟩ := hp
      rw [norm_mul, pow_two]
      exact mul_le_mul (hJ₁ p.1 (by omega) (by omega) j hj1)
        (hJ₁ p.2 (by omega) (by omega) j hj1) (norm_nonneg _) hC0
    calc ∑ p ∈ {p ∈ F | ¬ p.1 % 2 = 1}, ‖AA β p.1 j * AA β p.2 j‖
        ≤ ∑ _p ∈ {p ∈ F | ¬ p.1 % 2 = 1}, C ^ 2 := Finset.sum_le_sum hb
      _ = (({p ∈ F | ¬ p.1 % 2 = 1}).card : ℝ) * C ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * k + 1) * C ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h2 : F.card ≤ 2 * k + 1 := by
            rw [hFdef]
            have h := Finset.card_filter_le (Finset.antidiagonal (2 * k))
              (fun p : ℕ × ℕ => p.1 ≠ 0 ∧ p.2 ≠ 0)
            rwa [Finset.Nat.card_antidiagonal] at h
          have h1 := Finset.card_filter_le F (fun p : ℕ × ℕ => ¬ p.1 % 2 = 1)
          exact_mod_cast le_trans h1 h2
  have hAb : ‖(if k % 2 = 1 then (0 : ℂ) else (-1 : ℂ) ^ k * AA β k (j + 1) * Q ^ 2)‖
      ≤ C * qq β j ^ 2 := by
    by_cases hkpar : k % 2 = 1
    · rw [if_pos hkpar, norm_zero]; positivity
    · rw [if_neg hkpar, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hQ2n]
      exact mul_le_mul_of_nonneg_right (hJ₁ k (by omega) (by omega) (j + 1) (by omega))
        (by positivity)
  calc ‖(if k % 2 = 1 then (0 : ℂ) else (-1 : ℂ) ^ k * AA β k (j + 1) * Q ^ 2) - T * Q ^ 2‖
      ≤ ‖(if k % 2 = 1 then (0 : ℂ) else (-1 : ℂ) ^ k * AA β k (j + 1) * Q ^ 2)‖
        + ‖T * Q ^ 2‖ := norm_sub_le _ _
    _ ≤ C * qq β j ^ 2 + ((2 * k + 1) * C ^ 2) * qq β j ^ 2 := by
        refine add_le_add hAb ?_
        rw [norm_mul, hQ2n]
        exact mul_le_mul_of_nonneg_right hTb (by positivity)
    _ = (C + (2 * k + 1) * C ^ 2) * qq β j ^ 2 := by ring

end LeanFormalizations.Transcendence.Dubickas

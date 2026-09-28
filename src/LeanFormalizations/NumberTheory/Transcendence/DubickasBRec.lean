/-
# The Dubickas "no-gap" route: the combinatorial finish

This file holds the *terminal* step of the elementary route to `c_eq_zero_or_two_noGap`
(`DubickasNoGap.lean`), isolated as a statement about an abstract sequence so that it can be
proved and checked independently of the analysis that produces that sequence.

## Where the sequence comes from (see `PROBE-DUBICKAS-NOGAP.md` for the full route)

Let `β` be the Pisot number of `exists_pisot_trace_ident`, `B = β^N` with `N = 2^j`, and let
`e_k(N)` be the `k`-th elementary symmetric function of the *small* conjugate powers
`β_2^N, …, β_d^N`.  Writing `C = c/2 ∈ ℤ` and `q = B⁻¹`, the analysis gives asymptotics

    e_{2i}(N) = a_{2i} q² + O(q³),      e_{2i+1}(N) = a_{2i+1} q + O(q²),

with `a_{2i+1} = −a_{2i}`.  Setting `b i := a_{2i}` (so `b 0 = −C`), the Graeffe identity
`e_k(2N) = e_k(N)² + 2 Σ_{m=1}^{k} (−1)^m e_{k−m}(N) e_{k+m}(N)` collapses, on the `q²`
coefficients, to the single recursion

    2 b (n+1) = Σ_{u+v=n} b u * b v + (b (n/2) if n is even).

Finally `deg β = d` forces `e_k ≡ 0` for `k > d − 1`, i.e. `b` has **finite support**.  The
theorem below says that this is only possible for `C = 0` or `C = 1`, i.e. `c ∈ {0, 2}`.

## Status: SORRY-FREE
-/
import Mathlib

namespace LeanFormalizations.Transcendence.Dubickas

open Finset

variable {K : Type*} [Field K] [CharZero K]

/-- A sequence obeying the Dubickas recursion with `b 0 = 0` vanishes identically. -/
theorem bRec_eq_zero_of_head_eq_zero {b : ℕ → K}
    (hrec : ∀ n : ℕ, 2 * b (n + 1)
      = (∑ p ∈ Finset.antidiagonal n, b p.1 * b p.2) + (if n % 2 = 0 then b (n / 2) else 0))
    (hb0 : b 0 = 0) : ∀ n, b n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact hb0
    | (m + 1) =>
      have hsum : (∑ p ∈ Finset.antidiagonal m, b p.1 * b p.2) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp1 : p.1 ≤ m := by
          have := Finset.antidiagonal.fst_le hp
          exact this
        rw [ih p.1 (by omega), zero_mul]
      have hhalf : (if m % 2 = 0 then b (m / 2) else 0) = 0 := by
        by_cases h : m % 2 = 0
        · rw [if_pos h, ih (m / 2) (by omega)]
        · rw [if_neg h]
      have := hrec m
      rw [hsum, hhalf, add_zero] at this
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (two_ne_zero)
      · exact h'

/-- **The combinatorial finish of the no-gap route.**  A sequence satisfying the Dubickas
recursion with head `−C` and *finite support* forces `C = 0` or `C = 1`. -/
theorem eq_zero_or_one_of_bRec_finite_support {C : K} {b : ℕ → K} (hb0 : b 0 = -C)
    (hrec : ∀ n : ℕ, 2 * b (n + 1)
      = (∑ p ∈ Finset.antidiagonal n, b p.1 * b p.2) + (if n % 2 = 0 then b (n / 2) else 0))
    (hfin : ∃ M, ∀ n ≥ M, b n = 0) : C = 0 ∨ C = 1 := by
  classical
  obtain ⟨M, hM⟩ := hfin
  set S : Finset ℕ := (Finset.range M).filter (fun n => b n ≠ 0) with hS
  by_cases hSe : S = ∅
  · -- `b` is identically zero
    left
    have hz : b 0 = 0 := by
      by_cases h0 : 0 < M
      · by_contra hne
        have : (0 : ℕ) ∈ S := by rw [hS]; simp [h0, hne]
        rw [hSe] at this; exact absurd this (Finset.notMem_empty 0)
      · exact hM 0 (by omega)
    rw [hb0] at hz
    linear_combination -hz
  · -- `m` is the top of the support
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hSe
    obtain ⟨m, hmmem, hmmax⟩ : ∃ m ∈ S, ∀ j ∈ S, j ≤ m :=
      ⟨S.max' hne, S.max'_mem hne, fun j hj => S.le_max' j hj⟩
    have hbm : b m ≠ 0 := by
      have := hmmem
      rw [hS] at this
      exact (Finset.mem_filter.1 this).2
    have habove : ∀ j, m < j → b j = 0 := by
      intro j hj
      by_cases hjM : M ≤ j
      · exact hM j hjM
      · by_contra hne
        have hjS : j ∈ S := by rw [hS]; simp [Nat.lt_of_not_le hjM, hne]
        exact absurd (hmmax j hjS) (by omega)
    -- Step 1: `b m = −1`, from the recursion at `n = 2m`.
    have hbm1 : b m = -1 := by
      have h := hrec (2 * m)
      have hsum : (∑ p ∈ Finset.antidiagonal (2 * m), b p.1 * b p.2) = b m * b m := by
        rw [← Finset.sum_subset (s₁ := {(m, m)}) ?_ ?_]
        · simp
        · intro x hx
          simp only [Finset.mem_singleton] at hx
          subst hx
          simp [Finset.mem_antidiagonal, two_mul]
        · intro x hx hxn
          simp only [Finset.mem_singleton] at hxn
          have hxa : x.1 + x.2 = 2 * m := Finset.mem_antidiagonal.1 hx
          rcases lt_trichotomy x.1 m with h1 | h1 | h1
          · rw [habove x.2 (by omega), mul_zero]
          · exact absurd (by rw [Prod.ext_iff]; exact ⟨h1, by omega⟩) hxn
          · rw [habove x.1 h1, zero_mul]
      rw [hsum, habove (2 * m + 1) (by omega), if_pos (by omega),
        show 2 * m / 2 = m by omega] at h
      have : b m * (b m + 1) = 0 := by ring_nf; ring_nf at h; linear_combination -h
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' hbm
      · linear_combination h'
    -- Step 2: everything strictly below `m` vanishes.
    have hbelow : ∀ k, k < m → b k = 0 := by
      have key : ∀ d k : ℕ, m - k = d → k < m → b k = 0 := by
        intro d
        induction d using Nat.strong_induction_on with
        | _ d ih =>
          intro k hdk hkm
          -- the recursion at `n = m + k`
          have hmid : ∀ j, k < j → j < m → b j = 0 := by
            intro j hj1 hj2
            exact ih (m - j) (by omega) j rfl hj2
          have h := hrec (m + k)
          have hsum : (∑ p ∈ Finset.antidiagonal (m + k), b p.1 * b p.2)
              = b m * b k + b k * b m := by
            rw [← Finset.sum_subset (s₁ := {(m, k), (k, m)}) ?_ ?_]
            · rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton]
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> simp [Finset.mem_antidiagonal] <;> omega
            · intro x hx hxn
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxn
              have hxa : x.1 + x.2 = m + k := Finset.mem_antidiagonal.1 hx
              rcases lt_trichotomy x.1 m with h1 | h1 | h1
              · rcases lt_trichotomy x.2 m with h2 | h2 | h2
                · -- both `< m`: one of them is `> k` (else the sum is `≤ 2k < m + k`)
                  rcases Nat.lt_or_ge k x.1 with hk1 | hk1
                  · rw [hmid x.1 hk1 h1, zero_mul]
                  · rw [hmid x.2 (by omega) h2, mul_zero]
                · exact absurd (by rw [Prod.ext_iff]; exact ⟨by omega, h2⟩) hxn.2
                · rw [habove x.2 h2, mul_zero]
              · exact absurd (by rw [Prod.ext_iff]; exact ⟨h1, by omega⟩) hxn.1
              · rw [habove x.1 h1, zero_mul]
          have hhalf : (if (m + k) % 2 = 0 then b ((m + k) / 2) else 0) = 0 := by
            by_cases hpar : (m + k) % 2 = 0
            · rw [if_pos hpar, hmid ((m + k) / 2) (by omega) (by omega)]
            · rw [if_neg hpar]
          rw [hsum, hhalf, add_zero, habove (m + k + 1) (by omega)] at h
          have : b m * b k = 0 := by linear_combination -h / 2
          rcases mul_eq_zero.1 this with h' | h'
          · exact absurd h' hbm
          · exact h'
      intro k hk
      exact key (m - k) k rfl hk
    -- Step 3: `m = 0`, hence `b 0 = −1` and `C = 1`.
    have hm0 : m = 0 := by
      by_contra hne
      have hz0 : b 0 = 0 := hbelow 0 (by omega)
      have := bRec_eq_zero_of_head_eq_zero hrec hz0 m
      exact hbm this
    right
    rw [hm0] at hbm1
    rw [hb0] at hbm1
    linear_combination -hbm1

end LeanFormalizations.Transcendence.Dubickas

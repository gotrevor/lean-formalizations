/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The digits of Mills' constant, assuming RH (Caldwell–Cheng 2005)

C. K. Caldwell, Y. Cheng, *Determining Mills' constant and a note on Honaker's problem*,
J. Integer Seq. **8** (2005), Article 05.4.1.  Local-only full text (gitignored):
`papers/caldwell-cheng-2005-mills-constant.{pdf,txt}`.

formal-conjectures states `Mills.lower_bound_of_RH`: under RH the least Mills number lies in
`(1.3063778838, 1.3063778839)`.  The route:

1. **Caldwell–Cheng Lemma 5** (`primeBetweenCubes_of_schoenfeld`): Schoenfeld's RH bound gives
   `π((n+1)³) − π(n³) ≥ (3n² + 3n + 1)/(3 log(n+1)) − (3/(4π)) (n+1)^(3/2) log(n+1) > 0` once
   `n³ ≥ 2657`, i.e. `n ≥ 14`; `n = 1, …, 13` are a finite check (`decide`/`norm_num`).
   The paper's display is in §2, just after Lemma 4.
2. **The greedy chain is the least Mills number** (`minMills_mem_Ioo_of_primeBetweenCubes`):
   with a prime in every cube gap, *every* prime `p` extends (some prime lies strictly between
   `p³` and `(p+1)³`), so the chain `b₁ = 2`, `b_{k+1}` = least prime `> b_k³` never stalls,
   and lexicographic minimality of the prime sequence gives numeric minimality of `A`.  Useful
   facts: any Mills `A` has `⌊A^(3^k)⌋₊ = b'_k` with `b'_{k+1} ∈ (b'_k³, (b'_k+1)³)`
   (see `Basic.lean`), and `b'_k ↦ A` is order-preserving.
3. **Digits**: `b₁..b₄ = 2, 11, 1361, 2521008887` (OEIS A051254; each `b_{k+1}` is the least
   prime above `b_k³`, so the gaps `b_k³+1 … b_{k+1}−1` are composite: a `decide`-sized
   check), and `b₄^(1/81) ≈ 1.30637788386308`, `(b₄+1)^(1/81) ≈ 1.30637788386948` — both
   inside the target interval.  Compare exact rational 81st powers: `1.3063778838 ^ 81 < b₄`
   and `(b₄ + 1) < 1.3063778839 ^ 81`, pure `norm_num`.
-/
import LeanFormalizations.NumberTheory.Mills.Basic
import LeanFormalizations.NumberTheory.Mills.Chain
import LeanFormalizations.Literature.Primes
import LeanFormalizations.NumberTheory.Mills.Schoenfeld

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- **Caldwell–Cheng (2005), Lemma 5**, integer form: under RH (via Schoenfeld) every gap
between consecutive cubes from `1³` on contains a prime. -/
theorem primeBetweenCubes_of_schoenfeld (hS : Schoenfeld1976) (hRH : RiemannHypothesis) :
    PrimeBetweenCubesFrom 1 :=
  primeBetweenCubes_of_schoenfeld' hS hRH

/-! ### The greedy prime chain

`lpa n` is the least prime above `n`; `gseq` is the greedy chain `2, 11, 1361, 2521008887, …`
(OEIS A051254).  With a prime in every cube gap the chain never overshoots, so `Chain.lean`'s
shifted construction turns it into a Mills number `A₀`, and lexicographic minimality of the
greedy chain makes `A₀` the least one. -/

theorem lpa_ex (n : ℕ) : ∃ p, n < p ∧ p.Prime := by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n + 1); exact ⟨p, hp1, hp2⟩

/-- The least prime strictly above `n`. -/
def lpa (n : ℕ) : ℕ := Nat.find (lpa_ex n)

theorem lpa_spec (n : ℕ) : n < lpa n ∧ (lpa n).Prime :=
  Nat.find_spec (p := fun p => n < p ∧ p.Prime) (lpa_ex n)

theorem lpa_le {n p : ℕ} (hp : p.Prime) (h : n < p) : lpa n ≤ p := by
  unfold lpa; exact Nat.find_le ⟨h, hp⟩

/-- `lpa n = v` from a *finite* composite check on the gap `(n, v)`. -/
theorem lpa_eq {n v : ℕ} (h1 : n < v) (h2 : v.Prime)
    (h3 : ∀ m ∈ Finset.Ioo n v, ¬ m.Prime) : lpa n = v := by
  refine le_antisymm (lpa_le h2 h1) ?_
  by_contra hcon
  push Not at hcon
  exact h3 _ (Finset.mem_Ioo.2 ⟨(lpa_spec n).1, hcon⟩) (lpa_spec n).2

/-- The greedy prime chain: `2, 11, 1361, 2521008887, …`, each term the least prime above the
cube of its predecessor. -/
def gseq : ℕ → ℕ
  | 0 => 2
  | k + 1 => lpa ((gseq k) ^ 3)

/-- Unfolding lemma.  Stated with a *variable* index: `gseq 3 = lpa ((gseq 2) ^ 3)` by `rfl`
sends the defeq checker off to evaluate `Nat.find` over two billion candidates. -/
theorem gseq_succ (k : ℕ) : gseq (k + 1) = lpa ((gseq k) ^ 3) := rfl

theorem gseq_zero : gseq 0 = 2 := rfl

theorem gseq_prime : ∀ k, (gseq k).Prime
  | 0 => by norm_num [gseq]
  | k + 1 => (lpa_spec _).2

theorem gseq_two_le (k : ℕ) : 2 ≤ gseq k := (gseq_prime k).two_le

theorem gseq_lo (k : ℕ) : (gseq k) ^ 3 < gseq (k + 1) := (lpa_spec _).1

theorem gseq_hi (h : PrimeBetweenCubesFrom 1) (k : ℕ) :
    gseq (k + 1) + 1 < (gseq k + 1) ^ 3 := by
  obtain ⟨p, hp, hp1, hp2⟩ := h (gseq k) (le_trans (by norm_num) (gseq_two_le k))
  have hle : gseq (k + 1) ≤ p := lpa_le hp hp1
  exact prime_add_one_lt_cube (gseq_two_le k) (gseq_prime (k + 1))
    (lt_of_le_of_lt hle hp2)

/-- The greedy chain really is `2, 11, 1361, 2521008887` at its first four terms. -/
theorem gseq_one : gseq 1 = 11 := by
  rw [gseq_succ, gseq_zero]
  refine lpa_eq (by norm_num) (by norm_num) ?_
  intro m hm
  simp only [Finset.mem_Ioo] at hm
  norm_num at hm
  obtain ⟨h1, h2⟩ := hm
  interval_cases m <;> norm_num

theorem gseq_two : gseq 2 = 1361 := by
  rw [gseq_succ, gseq_one]
  refine lpa_eq (by norm_num) (by norm_num) ?_
  intro m hm
  simp only [Finset.mem_Ioo] at hm
  norm_num at hm
  obtain ⟨h1, h2⟩ := hm
  interval_cases m <;> norm_num

theorem gseq_three : gseq 3 = 2521008887 := by
  rw [gseq_succ, gseq_two]
  refine lpa_eq (by norm_num) (by norm_num) ?_
  intro m hm
  simp only [Finset.mem_Ioo] at hm
  norm_num at hm
  obtain ⟨h1, h2⟩ := hm
  have hcases : m = 2521008882 ∨ m = 2521008883 ∨ m = 2521008884 ∨ m = 2521008885 ∨
      m = 2521008886 := by omega
  rcases hcases with h | h | h | h | h <;> subst h <;> norm_num

/-- The greedy chain gives a Mills number. -/
theorem exists_greedy_mills (h : PrimeBetweenCubesFrom 1) :
    ∃ A₀ : ℝ, 1 < A₀ ∧ IsMills A₀ ∧ ∀ k, ⌊A₀ ^ ((3:ℕ) ^ (k+1))⌋₊ = gseq k := by
  obtain ⟨A₀, hA₀1, hfl⟩ :=
    exists_shifted_of_chain (b := gseq) (le_refl 2) gseq_lo (gseq_hi h)
  refine ⟨A₀, hA₀1, fun n => ?_, hfl⟩
  obtain ⟨m, hm⟩ : ∃ m, (n : ℕ) = m + 1 :=
    ⟨(n : ℕ).pred, (Nat.succ_pred_eq_of_pos n.pos).symm⟩
  rw [hm, hfl m]
  exact (gseq_prime m).prime

/-- **The greedy chain is lexicographically least**: the digits of any Mills number dominate
it termwise. -/
theorem gseq_le_digits {A : ℝ} (hA1 : 1 < A) (hA : IsMills A) (k : ℕ) :
    gseq k ≤ ⌊A ^ ((3:ℕ) ^ (k+1))⌋₊ := by
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hprime : ∀ j : ℕ, (⌊A ^ ((3:ℕ) ^ (j+1))⌋₊).Prime := by
    intro j
    have := hA ⟨j + 1, by omega⟩
    simpa using Nat.prime_iff.2 this
  induction k with
  | zero => exact (hprime 0).two_le
  | succ k ih =>
      -- `⌊A^(3^(k+1))⌋₊ ^ 3 < ⌊A^(3^(k+2))⌋₊`
      set c : ℕ := ⌊A ^ ((3:ℕ) ^ (k+1))⌋₊ with hc
      have hcle : (c : ℝ) ≤ A ^ ((3:ℕ) ^ (k+1)) := Nat.floor_le (by positivity)
      have hcube : ((c ^ 3 : ℕ) : ℝ) ≤ A ^ ((3:ℕ) ^ (k+2)) := by
        rw [pow_succ ((3:ℕ)) (k+1), pow_mul]
        push_cast
        exact pow_le_pow_left₀ (by positivity) hcle 3
      have hfloor : c ^ 3 ≤ ⌊A ^ ((3:ℕ) ^ (k+2))⌋₊ :=
        Nat.le_floor hcube
      have hne : c ^ 3 ≠ ⌊A ^ ((3:ℕ) ^ (k+2))⌋₊ := by
        intro hEq
        have hp := hprime (k + 1)
        rw [show k + 1 + 1 = k + 2 from rfl, ← hEq] at hp
        have h2c : 2 ≤ c := (hprime k).two_le
        have : c ∣ c ^ 3 := dvd_pow_self c (by norm_num)
        rcases hp.eq_one_or_self_of_dvd c this with h | h
        · omega
        · have hlt : c ^ 1 < c ^ 3 := Nat.pow_lt_pow_right h2c (by norm_num)
          rw [pow_one, ← h] at hlt
          exact absurd hlt (lt_irrefl c)
      have hlt : c ^ 3 < ⌊A ^ ((3:ℕ) ^ (k+2))⌋₊ := lt_of_le_of_ne hfloor hne
      have hmono : (gseq k) ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left ih 3
      exact lpa_le (hprime (k+1)) (lt_of_le_of_lt hmono hlt)

/-- **Primes in every cube gap pin the least Mills number to ten digits.**  Unconditional
given the hypothesis; this is where the combinatorics and the arithmetic live. -/
theorem minMills_mem_Ioo_of_primeBetweenCubes (h : PrimeBetweenCubesFrom 1) {A : ℝ}
    (hA : IsMinMills A) : A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  obtain ⟨A₀, hA₀1, hA₀m, hA₀fl⟩ := exists_greedy_mills h
  obtain ⟨⟨hA1, hAm⟩, hAmin⟩ := hA
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hAle : A ≤ A₀ := hAmin ⟨hA₀1, hA₀m⟩
  have h81 : ((3:ℕ) ^ (3 + 1)) = 81 := by norm_num
  -- lower: `A^81 ≥ 2521008887`
  have hlow : (2521008887 : ℝ) ≤ A ^ (81:ℕ) := by
    have hd := gseq_le_digits hA1 hAm 3
    rw [gseq_three, h81] at hd
    have hc : (2521008887 : ℝ) ≤ ((⌊A ^ (81:ℕ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hd
    exact hc.trans (Nat.floor_le (by positivity))
  -- upper: `A^81 < 2521008888`
  have hup : A ^ (81:ℕ) < (2521008888 : ℝ) := by
    have hlt : A₀ ^ ((3:ℕ) ^ (3+1)) < (⌊A₀ ^ ((3:ℕ) ^ (3+1))⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [hA₀fl 3, gseq_three, h81] at hlt
    have : A ^ (81:ℕ) ≤ A₀ ^ (81:ℕ) := pow_le_pow_left₀ hA0 hAle 81
    push_cast at hlt
    linarith
  constructor
  · by_contra hcon
    push Not at hcon
    have : A ^ (81:ℕ) ≤ (1.3063778838 : ℝ) ^ (81:ℕ) := pow_le_pow_left₀ hA0 hcon 81
    have hnum : (1.3063778838 : ℝ) ^ (81:ℕ) < 2521008887 := by norm_num
    linarith
  · by_contra hcon
    push Not at hcon
    have : (1.3063778839 : ℝ) ^ (81:ℕ) ≤ A ^ (81:ℕ) :=
      pow_le_pow_left₀ (by norm_num) hcon 81
    have hnum : (2521008888 : ℝ) ≤ (1.3063778839 : ℝ) ^ (81:ℕ) := by norm_num
    linarith

/-- **formal-conjectures `Mills.lower_bound_of_RH`**, with Schoenfeld as the literature input. -/
theorem lower_bound_of_RH (hS : Schoenfeld1976) (hRH : RiemannHypothesis) {A : ℝ}
    (hA : IsMinMills A) : A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 :=
  minMills_mem_Ioo_of_primeBetweenCubes (primeBetweenCubes_of_schoenfeld hS hRH) hA

end LeanFormalizations.Mills

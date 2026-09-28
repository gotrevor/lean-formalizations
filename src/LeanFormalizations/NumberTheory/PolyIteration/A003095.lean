/-
# OEIS A003095: `a(n) = a(n−1)² + 1`, `a(0) = 0`

The elementary facts recorded on <https://oeis.org/A003095> (checked 2026-09-28).  Its growth
constant (A076949) is transcendental: `NumberTheory/Transcendence/Dubickas.lean`.

* **Strong divisibility** (Somos 2013, Kimberling 2019; Bala 2026 for the shifted families):
  from `Sylvester.lean`.
* **Bala's identities** (formula section, Jul 10 2026).
* **The Bala conjectures** (comment, 2022), proved by D. L. Harden, *Proving the Bala
  conjectures*, <https://oeis.org/A003095/a003095_1.pdf> (local copy
  `papers/harden-2026-bala-conjectures.{pdf,txt}`): the last `k` digits are eventually periodic
  with exact period 6, with explicit thresholds.  Harden's route: `d_n = a(n+2) − a(n)` satisfies
  `d_{n+1} = d_n (a(n+2) + a(n))`, so `2^(n+1) ∣ d_n`; `d'_n = a(n+3) − a(n)` gains a factor `5`
  every third step, so `5^⌊(n+5)/3⌋ ∣ d'_n`; then `a(n+6) − a(n) = d_n + d_{n+2} + d_{n+4} =
  d'_n + d'_{n+3}`.
* **Somos's cubic relation** (2017) and the last-digit cycle (Vos Post 2005).

⚠️ **One frozen statement was false as written**: `a003095_sq_dvd` (`a(n)² ∣ a(n+m) − a(m)`)
fails at `m = 0`, where it reads `a(n)² ∣ a(n)` — already false at `n = 2` (`4 ∤ 2`).  The
hypothesis `1 ≤ m` was added; it is exactly the hypothesis Bala's identity
`a003095_add_sub_eq` (from which the divisibility follows) carries.  Name and path unchanged.

Before proving a statement, sanity-check it on small `n` with `decide`/`norm_num`; a
counterexample to an OEIS formula is a valid (and reportable) outcome.
-/
import LeanFormalizations.NumberTheory.PolyIteration.Sylvester

namespace LeanFormalizations.PolyIteration

/-- **A003095**: `0, 1, 2, 5, 26, 677, 458330, …` -/
def a003095 : ℕ → ℤ
  | 0 => 0
  | n + 1 => a003095 n ^ 2 + 1

open Polynomial

/-- The defining polynomial `X² + 1`. -/
private noncomputable def Pa : ℤ[X] := X ^ 2 + C 1

private theorem a003095_succ (n : ℕ) : a003095 (n + 1) = a003095 n ^ 2 + 1 := rfl

private theorem a003095_iter (n : ℕ) : a003095 (n + 1) = Pa.eval (a003095 n) := by
  simp [Pa, a003095_succ]

private theorem Pa_even (x : ℤ) : Pa.eval (-x) = Pa.eval x := by simp [Pa]

/-- A003095 is a strong divisibility sequence (Sylvester with `P = X² + 1`). -/
theorem a003095_isStrongDivSeq : IsStrongDivSeq a003095 :=
  isStrongDivSeq_of_iterate Pa a003095 rfl a003095_iter

/-- Bala: `n ↦ a(n+k) − a(k)` is an SDS for every `k`. -/
theorem a003095_sub_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ a003095 (n + k) - a003095 k) :=
  isStrongDivSeq_sub Pa a003095 a003095_iter k

/-- Bala: `n ↦ a(n+k) + a(k)` (`n ≥ 1`) is an SDS for every `k`. -/
theorem a003095_add_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ if n = 0 then 0 else a003095 (n + k) + a003095 k) :=
  isStrongDivSeq_add Pa Pa_even a003095 a003095_iter k

/-- The one-step factorisation driving every divisibility fact below. -/
private theorem a003095_step (n m : ℕ) :
    a003095 (n + m + 1) - a003095 (m + 1) =
      (a003095 (n + m) - a003095 m) * (a003095 (n + m) + a003095 m) := by
  rw [a003095_succ, a003095_succ]; ring

/-- The shift lemma specialised to A003095: `a n − a k ∣ a (n+j) − a (k+j)`. -/
theorem a003095_sub_dvd_shift (n k j : ℕ) :
    a003095 n - a003095 k ∣ a003095 (n + j) - a003095 (k + j) :=
  sub_dvd_sub_shift Pa a003095 a003095_iter n k j

/-- Bala (2026): `a(n+m) − a(m) = a(n)² ∏_{k=1}^{m−1} (a(n+k) + a(k))` for `m ≥ 1`. -/
theorem a003095_add_sub_eq (n m : ℕ) (hm : 1 ≤ m) :
    a003095 (n + m) - a003095 m =
      a003095 n ^ 2 * ∏ k ∈ Finset.Ico 1 m, (a003095 (n + k) + a003095 k) := by
  induction m, hm using Nat.le_induction with
  | base => simp [a003095]
  | succ m hm ih =>
      rw [← Nat.add_assoc, a003095_step n m, ih, Finset.prod_Ico_succ_top hm]
      ring

/-- Bala (2026): `a(n)² ∣ a(n+m) − a(m)`.

⚠️ The `1 ≤ m` hypothesis is **not** in the OEIS phrasing but is necessary: at `m = 0` the
claim reads `a n ^ 2 ∣ a n`, false already at `n = 2` (`4 ∤ 2`).  Bala's identity
`a003095_add_sub_eq`, from which this follows, likewise requires `m ≥ 1`. -/
theorem a003095_sq_dvd (n m : ℕ) (hm : 1 ≤ m) : a003095 n ^ 2 ∣ a003095 (n + m) - a003095 m := by
  rw [a003095_add_sub_eq n m hm]; exact Dvd.intro _ rfl

/-- Bala (2026): `a(n) − a(k) ∣ a(mn) − a(mk)` for `m ≥ 1`, `n ≠ k`. -/
theorem a003095_sub_dvd (m n k : ℕ) (hm : 1 ≤ m) (hnk : n ≠ k) :
    a003095 n - a003095 k ∣ a003095 (m * n) - a003095 (m * k) := by
  -- the `k < n` case; the other follows by negating
  have main : ∀ n k : ℕ, k < n → ∀ m : ℕ, 1 ≤ m →
      a003095 n - a003095 k ∣ a003095 (m * n) - a003095 (m * k) := by
    intro n k hkn m hm
    obtain ⟨p, rfl⟩ : ∃ p, n = k + p + 1 := ⟨n - k - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    set D : ℤ := a003095 (k + p + 1) - a003095 k with hD
    have claim : ∀ i : ℕ, D ∣ a003095 (k + k * m + i * (p + 1)) - a003095 (k + k * m) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
          have hstep : D ∣ a003095 (k + k * m + (i + 1) * (p + 1))
              - a003095 (k + k * m + i * (p + 1)) := by
            have := a003095_sub_dvd_shift (k + p + 1) k (k * m + i * (p + 1))
            have e1 : k + p + 1 + (k * m + i * (p + 1)) = k + k * m + (i + 1) * (p + 1) := by
              ring
            have e2 : k + (k * m + i * (p + 1)) = k + k * m + i * (p + 1) := by ring
            rw [e1, e2] at this
            exact this
          simpa using dvd_add hstep ih
    have := claim (m + 1)
    have e3 : k + k * m + (m + 1) * (p + 1) = (m + 1) * (k + p + 1) := by ring
    have e4 : k + k * m = (m + 1) * k := by ring
    rwa [e3, e4] at this
  rcases lt_or_gt_of_ne hnk with h | h
  · have h' := main k n h m hm
    rw [← neg_sub (a003095 k) (a003095 n), ← neg_sub (a003095 (m * k)) (a003095 (m * n)),
      neg_dvd, dvd_neg]
    exact h'
  · exact main n k h m hm

/-! ### Residues -/

/-- `a(n) ≡ n (mod 2)` (Alkan 2015). -/
theorem a003095_mod_two (n : ℕ) : a003095 n % 2 = n % 2 := by
  induction n with
  | zero => simp [a003095]
  | succ n ih =>
      have key : a003095 (n + 1) % 2 = (a003095 n % 2 * (a003095 n % 2) + 1) % 2 := by
        rw [show a003095 (n + 1) = a003095 n * a003095 n + 1 by rw [a003095_succ]; ring,
          Int.add_emod, Int.mul_emod]
        simp
      rw [key, ih]
      have h : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := Int.emod_two_eq_zero_or_one _
      rcases h with h | h <;> rw [h] <;> push_cast <;> omega

/-- `a(n) mod 5` cycles `0, 1, 2` with period 3. -/
theorem a003095_mod_five (n : ℕ) : a003095 n % 5 = ((n % 3 : ℕ) : ℤ) := by
  induction n with
  | zero => simp [a003095]
  | succ n ih =>
      have key : a003095 (n + 1) % 5 = (a003095 n % 5 * (a003095 n % 5) + 1) % 5 := by
        rw [show a003095 (n + 1) = a003095 n * a003095 n + 1 by rw [a003095_succ]; ring,
          Int.add_emod, Int.mul_emod]
        simp
      rw [key, ih]
      have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h with h | h | h <;>
        [ (have h' : (n + 1) % 3 = 1 := by omega);
          (have h' : (n + 1) % 3 = 2 := by omega);
          (have h' : (n + 1) % 3 = 0 := by omega)] <;>
        rw [h, h'] <;> decide

private theorem two_dvd_pair (n : ℕ) : (2 : ℤ) ∣ a003095 (n + 2) + a003095 n := by
  have h1 := a003095_mod_two (n + 2)
  have h2 := a003095_mod_two n
  push_cast at h1 h2
  omega

private theorem odd_gap_one (n : ℕ) : ¬ (2 : ℤ) ∣ a003095 (n + 1) - a003095 n := by
  have h1 := a003095_mod_two (n + 1)
  have h2 := a003095_mod_two n
  push_cast at h1 h2
  omega

private theorem odd_gap_three (n : ℕ) : ¬ (2 : ℤ) ∣ a003095 (n + 3) - a003095 n := by
  have h1 := a003095_mod_two (n + 3)
  have h2 := a003095_mod_two n
  push_cast at h1 h2
  omega

private theorem five_dvd_pair (n : ℕ) (hn : n % 3 = 0) :
    (5 : ℤ) ∣ a003095 (n + 3) + a003095 n := by
  have h1 := a003095_mod_five (n + 3)
  have h2 := a003095_mod_five n
  rw [show (n + 3) % 3 = 0 by omega] at h1
  rw [hn] at h2
  push_cast at h1 h2
  omega

private theorem five_not_dvd_gap_two (n : ℕ) : ¬ (5 : ℤ) ∣ a003095 (n + 2) - a003095 n := by
  have h1 := a003095_mod_five (n + 2)
  have h2 := a003095_mod_five n
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h <;>
    [ (rw [show (n + 2) % 3 = 2 by omega] at h1);
      (rw [show (n + 2) % 3 = 0 by omega] at h1);
      (rw [show (n + 2) % 3 = 1 by omega] at h1)] <;>
    rw [h] at h2 <;> push_cast at h1 h2 <;> omega

/-! ### The two towers -/

/-- Harden: `2^(n+1) ∣ a(n+2) − a(n)`. -/
theorem a003095_two_pow_dvd (n : ℕ) : (2 : ℤ) ^ (n + 1) ∣ a003095 (n + 2) - a003095 n := by
  induction n with
  | zero => norm_num [a003095]
  | succ n ih =>
      have e : a003095 (n + 1 + 2) - a003095 (n + 1) =
          (a003095 (n + 2) - a003095 n) * (a003095 (n + 2) + a003095 n) := by
        have h1 : a003095 (n + 1 + 2) = a003095 (n + 2) ^ 2 + 1 := a003095_succ (n + 2)
        have h2 : a003095 (n + 1) = a003095 n ^ 2 + 1 := a003095_succ n
        rw [h1, h2]; ring
      rw [e, pow_succ]
      exact mul_dvd_mul ih (two_dvd_pair n)

/-- Harden: `5^⌊(n+5)/3⌋ ∣ a(n+3) − a(n)`. -/
theorem a003095_five_pow_dvd (n : ℕ) :
    (5 : ℤ) ^ ((n + 5) / 3) ∣ a003095 (n + 3) - a003095 n := by
  induction n with
  | zero => norm_num [a003095]
  | succ n ih =>
      have e : a003095 (n + 1 + 3) - a003095 (n + 1) =
          (a003095 (n + 3) - a003095 n) * (a003095 (n + 3) + a003095 n) := by
        have h1 : a003095 (n + 1 + 3) = a003095 (n + 3) ^ 2 + 1 := a003095_succ (n + 3)
        have h2 : a003095 (n + 1) = a003095 n ^ 2 + 1 := a003095_succ n
        rw [h1, h2]; ring
      rw [e]
      by_cases h : n % 3 = 0
      · rw [show (n + 1 + 5) / 3 = (n + 5) / 3 + 1 by omega, pow_succ]
        exact mul_dvd_mul ih (five_dvd_pair n h)
      · rw [show (n + 1 + 5) / 3 = (n + 5) / 3 by omega]
        exact ih.mul_right _

/-! ### The Bala conjectures -/

/-- **Bala's Conjecture 1** (Harden): modulo `2^k` the sequence has period dividing 2 from
`n = k − 1` on. -/
theorem a003095_period_two_pow (k n : ℕ) (hn : k - 1 ≤ n) :
    (2 : ℤ) ^ k ∣ a003095 (n + 2) - a003095 n :=
  dvd_trans (pow_dvd_pow 2 (by omega)) (a003095_two_pow_dvd n)

/-- ... and the period modulo `2^k` (`k ≥ 1`) is exactly 2: `a(n) ≡ n (mod 2)`. -/
theorem a003095_not_period_one (k n : ℕ) (hk : 1 ≤ k) :
    ¬ (2 : ℤ) ^ k ∣ a003095 (n + 1) - a003095 n := fun h =>
  odd_gap_one n (dvd_trans (dvd_pow_self 2 (by omega)) h)

/-- Harden: modulo `5^k` the period divides 3 from `n = 3k − 5` on. -/
theorem a003095_period_five_pow (k n : ℕ) (hn : 3 * k - 5 ≤ n) :
    (5 : ℤ) ^ k ∣ a003095 (n + 3) - a003095 n :=
  dvd_trans (pow_dvd_pow 5 (by omega)) (a003095_five_pow_dvd n)

private theorem two_pow_dvd_six (j n : ℕ) (hn : j ≤ n + 1) :
    (2 : ℤ) ^ j ∣ a003095 (n + 6) - a003095 n := by
  have h0 : (2 : ℤ) ^ j ∣ a003095 (n + 2) - a003095 n :=
    dvd_trans (pow_dvd_pow 2 hn) (a003095_two_pow_dvd n)
  have h1 : (2 : ℤ) ^ j ∣ a003095 (n + 4) - a003095 (n + 2) := by
    have := dvd_trans (pow_dvd_pow 2 (show j ≤ n + 2 + 1 by omega)) (a003095_two_pow_dvd (n + 2))
    rwa [show n + 2 + 2 = n + 4 from rfl] at this
  have h2 : (2 : ℤ) ^ j ∣ a003095 (n + 6) - a003095 (n + 4) := by
    have := dvd_trans (pow_dvd_pow 2 (show j ≤ n + 4 + 1 by omega)) (a003095_two_pow_dvd (n + 4))
    rwa [show n + 4 + 2 = n + 6 from rfl] at this
  have := dvd_add (dvd_add h0 h1) h2
  simpa using this

private theorem five_pow_dvd_six (k n : ℕ) (hn : 3 * k - 5 ≤ n) :
    (5 : ℤ) ^ k ∣ a003095 (n + 6) - a003095 n := by
  have h0 := a003095_period_five_pow k n hn
  have h1 : (5 : ℤ) ^ k ∣ a003095 (n + 6) - a003095 (n + 3) := by
    have := a003095_period_five_pow k (n + 3) (by omega)
    rwa [show n + 3 + 3 = n + 6 from rfl] at this
  have := dvd_add h0 h1
  simpa using this

private theorem coprime_two_five_pow (i j : ℕ) (c : ℤ) (hc : c = 2 ∨ c = 4) :
    IsCoprime (c ^ i) ((5 : ℤ) ^ j) := by
  have : IsCoprime c (5 : ℤ) := by
    rcases hc with rfl | rfl <;>
      exact Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  exact this.pow

/-- **Bala's Conjecture 2** (Harden): modulo `10^k` the period divides 6 from
`n = max(3k − 5, k − 1)` on ... -/
theorem a003095_period_ten_pow (k n : ℕ) (hn : max (3 * k - 5) (k - 1) ≤ n) :
    (10 : ℤ) ^ k ∣ a003095 (n + 6) - a003095 n := by
  have h2 := two_pow_dvd_six k n (by omega)
  have h5 := five_pow_dvd_six k n (by omega)
  have := (coprime_two_five_pow k k 2 (Or.inl rfl)).mul_dvd h2 h5
  rwa [show (2 : ℤ) ^ k * 5 ^ k = 10 ^ k by rw [← mul_pow]; norm_num] at this

/-- ... and is exactly 6 (`k ≥ 1`): neither 2 nor 3 is a period, at any `n`. -/
theorem a003095_not_period_two_three (k n : ℕ) (hk : 1 ≤ k) :
    ¬ (10 : ℤ) ^ k ∣ a003095 (n + 2) - a003095 n ∧
      ¬ (10 : ℤ) ^ k ∣ a003095 (n + 3) - a003095 n := by
  constructor
  · intro h
    exact five_not_dvd_gap_two n
      (dvd_trans (dvd_trans (by norm_num) (dvd_pow_self (10 : ℤ) (by omega : k ≠ 0))) h)
  · intro h
    exact odd_gap_three n
      (dvd_trans (dvd_trans (by norm_num) (dvd_pow_self (10 : ℤ) (by omega : k ≠ 0))) h)

/-- **Bala's Conjecture 3** (Harden): modulo `20^k` the period divides 6 from
`n = max(3k − 5, 2k − 1)` on. -/
theorem a003095_period_twenty_pow (k n : ℕ) (hn : max (3 * k - 5) (2 * k - 1) ≤ n) :
    (20 : ℤ) ^ k ∣ a003095 (n + 6) - a003095 n := by
  have h2 : (4 : ℤ) ^ k ∣ a003095 (n + 6) - a003095 n := by
    have := two_pow_dvd_six (2 * k) n (by omega)
    rwa [show (2 : ℤ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num] at this
  have h5 := five_pow_dvd_six k n (by omega)
  have := (coprime_two_five_pow k k 4 (Or.inr rfl)).mul_dvd h2 h5
  rwa [show (4 : ℤ) ^ k * 5 ^ k = 20 ^ k by rw [← mul_pow]; norm_num] at this

/-- **Bala's Conjecture 4** (Harden): for `n ≥ ⌊k/2⌋` and `1 ≤ i ≤ 6`, `a(6n+i) mod 10^k` does
not depend on `n`. -/
theorem a003095_mod_ten_pow_stable (k n i : ℕ) (hn : k / 2 ≤ n) (hi : 1 ≤ i) (hi6 : i ≤ 6) :
    a003095 (6 * (n + 1) + i) % 10 ^ k = a003095 (6 * n + i) % 10 ^ k := by
  have hidx : 6 * (n + 1) + i = (6 * n + i) + 6 := by ring
  have hbound : max (3 * k - 5) (k - 1) ≤ 6 * n + i := by omega
  have h := a003095_period_ten_pow k (6 * n + i) hbound
  rw [hidx]
  exact Int.modEq_iff_dvd.mpr (by simpa using dvd_neg.mpr h)

/-- The last digit cycles `0, 1, 2, 5, 6, 7` (Vos Post 2005). -/
theorem a003095_mod_ten (n : ℕ) : a003095 (n + 6) % 10 = a003095 n % 10 := by
  have h := a003095_period_ten_pow 1 n (by omega)
  rw [pow_one] at h
  exact Int.modEq_iff_dvd.mpr (by simpa using dvd_neg.mpr h)

/-- Somos (2017): `0 = a(n)²(a(n+1) + a(n+2)) − a(n+1)²(a(n+1) + a(n+2) + a(n+3)) + a(n+2)³`. -/
theorem a003095_somos (n : ℕ) :
    a003095 n ^ 2 * (a003095 (n + 1) + a003095 (n + 2)) +
      a003095 (n + 1) ^ 2 * (-a003095 (n + 1) - a003095 (n + 2) - a003095 (n + 3)) +
      a003095 (n + 2) ^ 3 = 0 := by
  have h1 : a003095 (n + 1) = a003095 n ^ 2 + 1 := a003095_succ n
  have h2 : a003095 (n + 2) = a003095 (n + 1) ^ 2 + 1 := a003095_succ (n + 1)
  have h3 : a003095 (n + 3) = a003095 (n + 2) ^ 2 + 1 := a003095_succ (n + 2)
  rw [h3, h2, h1]; ring

end LeanFormalizations.PolyIteration

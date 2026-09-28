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

Before proving a statement, sanity-check it on small `n` with `decide`/`norm_num`; a
counterexample to an OEIS formula is a valid (and reportable) outcome.
-/
import LeanFormalizations.NumberTheory.PolyIteration.Sylvester

namespace LeanFormalizations.PolyIteration

/-- **A003095**: `0, 1, 2, 5, 26, 677, 458330, …` -/
def a003095 : ℕ → ℤ
  | 0 => 0
  | n + 1 => a003095 n ^ 2 + 1

/-- A003095 is a strong divisibility sequence (Sylvester with `P = X² + 1`). -/
theorem a003095_isStrongDivSeq : IsStrongDivSeq a003095 := by
  sorry

/-- Bala: `n ↦ a(n+k) − a(k)` is an SDS for every `k`. -/
theorem a003095_sub_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ a003095 (n + k) - a003095 k) := by
  sorry

/-- Bala: `n ↦ a(n+k) + a(k)` (`n ≥ 1`) is an SDS for every `k`. -/
theorem a003095_add_isStrongDivSeq (k : ℕ) :
    IsStrongDivSeq (fun n ↦ if n = 0 then 0 else a003095 (n + k) + a003095 k) := by
  sorry

/-- Bala (2026): `a(n+m) − a(m) = a(n)² ∏_{k=1}^{m−1} (a(n+k) + a(k))` for `m ≥ 1`. -/
theorem a003095_add_sub_eq (n m : ℕ) (hm : 1 ≤ m) :
    a003095 (n + m) - a003095 m =
      a003095 n ^ 2 * ∏ k ∈ Finset.Ico 1 m, (a003095 (n + k) + a003095 k) := by
  sorry

/-- Bala (2026): `a(n)² ∣ a(n+m) − a(m)`. -/
theorem a003095_sq_dvd (n m : ℕ) : a003095 n ^ 2 ∣ a003095 (n + m) - a003095 m := by
  sorry

/-- Bala (2026): `a(n) − a(k) ∣ a(mn) − a(mk)` for `m ≥ 1`, `n ≠ k`. -/
theorem a003095_sub_dvd (m n k : ℕ) (hm : 1 ≤ m) (hnk : n ≠ k) :
    a003095 n - a003095 k ∣ a003095 (m * n) - a003095 (m * k) := by
  sorry

/-- **Bala's Conjecture 1** (Harden): modulo `2^k` the sequence has period dividing 2 from
`n = k − 1` on. -/
theorem a003095_period_two_pow (k n : ℕ) (hn : k - 1 ≤ n) :
    (2 : ℤ) ^ k ∣ a003095 (n + 2) - a003095 n := by
  sorry

/-- ... and the period modulo `2^k` (`k ≥ 1`) is exactly 2: `a(n) ≡ n (mod 2)`. -/
theorem a003095_not_period_one (k n : ℕ) (hk : 1 ≤ k) :
    ¬ (2 : ℤ) ^ k ∣ a003095 (n + 1) - a003095 n := by
  sorry

/-- Harden: modulo `5^k` the period divides 3 from `n = 3k − 5` on. -/
theorem a003095_period_five_pow (k n : ℕ) (hn : 3 * k - 5 ≤ n) :
    (5 : ℤ) ^ k ∣ a003095 (n + 3) - a003095 n := by
  sorry

/-- **Bala's Conjecture 2** (Harden): modulo `10^k` the period divides 6 from
`n = max(3k − 5, k − 1)` on ... -/
theorem a003095_period_ten_pow (k n : ℕ) (hn : max (3 * k - 5) (k - 1) ≤ n) :
    (10 : ℤ) ^ k ∣ a003095 (n + 6) - a003095 n := by
  sorry

/-- ... and is exactly 6 (`k ≥ 1`): neither 2 nor 3 is a period, at any `n`. -/
theorem a003095_not_period_two_three (k n : ℕ) (hk : 1 ≤ k) :
    ¬ (10 : ℤ) ^ k ∣ a003095 (n + 2) - a003095 n ∧
      ¬ (10 : ℤ) ^ k ∣ a003095 (n + 3) - a003095 n := by
  sorry

/-- **Bala's Conjecture 3** (Harden): modulo `20^k` the period divides 6 from
`n = max(3k − 5, 2k − 1)` on. -/
theorem a003095_period_twenty_pow (k n : ℕ) (hn : max (3 * k - 5) (2 * k - 1) ≤ n) :
    (20 : ℤ) ^ k ∣ a003095 (n + 6) - a003095 n := by
  sorry

/-- **Bala's Conjecture 4** (Harden): for `n ≥ ⌊k/2⌋` and `1 ≤ i ≤ 6`, `a(6n+i) mod 10^k` does
not depend on `n`. -/
theorem a003095_mod_ten_pow_stable (k n i : ℕ) (hn : k / 2 ≤ n) (hi : 1 ≤ i) (hi6 : i ≤ 6) :
    a003095 (6 * (n + 1) + i) % 10 ^ k = a003095 (6 * n + i) % 10 ^ k := by
  sorry

/-- The last digit cycles `0, 1, 2, 5, 6, 7` (Vos Post 2005). -/
theorem a003095_mod_ten (n : ℕ) : a003095 (n + 6) % 10 = a003095 n % 10 := by
  sorry

/-- `a(n) ≡ n (mod 2)` (Alkan 2015). -/
theorem a003095_mod_two (n : ℕ) : a003095 n % 2 = n % 2 := by
  sorry

/-- Somos (2017): `0 = a(n)²(a(n+1) + a(n+2)) − a(n+1)²(a(n+1) + a(n+2) + a(n+3)) + a(n+2)³`. -/
theorem a003095_somos (n : ℕ) :
    a003095 n ^ 2 * (a003095 (n + 1) + a003095 (n + 2)) +
      a003095 (n + 1) ^ 2 * (-a003095 (n + 1) - a003095 (n + 2) - a003095 (n + 3)) +
      a003095 (n + 2) ^ 3 = 0 := by
  sorry

end LeanFormalizations.PolyIteration

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.OrbitSum
import LeanFormalizations.NumberTheory.Mills.SaitoFibonacci
import LeanFormalizations.NumberTheory.Mills.TheoremDGround

/-!
# Phase 52: Theorem A: order-`d` recurrences at inert primes; Tribonacci `T(3^n) + h`

**Theorem A.**  Let `A ∈ M_d(ℤ)` with `χ_A` irreducible mod the prime `c`, `d` odd, and suppose
`μ_(≤d)(ℤ_c) = {±1}` (`c = 2`, or no `k ∈ [3, d]` divides `c − 1`).  Let `u(N) = (A^N)_(ij)` with
`i ≠ j`, growing in absolute value along `c^n`, and suppose `c ∤ u(c^r)` for **some** `r < d`.  Then
`u(c^n) + h` is composite (not prime in `ℤ`) for infinitely many `n`, for **every** `h ∈ ℤ`.

Corollary: **`T(3^n) + h` and `T(5^n) + h` are composite i.o. for every `h`** (Tribonacci,
`T 0 = T 1 = 0`, `T 2 = 1`).  `X³ − X² − X − 1` is irreducible mod 3 and mod 5, and
`T 3 = 1`, `T 5 = 4`.  (Also mod 23, not stated.)

## Route (phase 32's survivor argument, order `d`)
Assume `p_n := u(c^n) + h` is prime for all `n ≥ n₀`.
1. **Filter** (`SaitoFibonacci.exists_entry_pow_congr` / `TheoremDGround`): for large `n`, either
   `p_n` divides some later `p_m` (`m > n`), which is impossible once `|u|` grows (`p_m` prime and
   `|p_m| > |p_n|`), or `p_n^i ≡ 1 (mod c^(e_n))` for some `1 ≤ i ≤ d`, with `e_n → ∞`
   (`TheoremDGround.exists_pow_sub_one_of_lt_padicValNat_glCard`, `e_n ≈ n/d − v_c(d!) − 1`).
2. **Window:** with `μ_(≤d)(ℤ_c) = {±1}`, `p_n^i ≡ 1 (mod c^e)` with `i ≤ d` forces
   `p_n ≡ ±1 (mod c^(e − O(1)))`.  (`c` odd: the order of `p_n` mod `c` divides `gcd(i, c − 1)`,
   which is `1` or `2`; lift by the `ℤ/c^e` cyclic structure, or `pow_sub_one`-factor
   `p^i − 1 = (p − 1)(…)`/`(p² − 1)(…)` and count valuations.  `c = 2`: `p` odd, `p ≡ ±1 mod 4`
   plus LTE.)
3. **Orbit sum** (phase 51, `OrbitSum.orbit_sum_entry_congr`): `Σ_(k<d) u(c^(n+k)) ≡ 0 (mod c^(n+1))`.
   With `s_k := p_(n+k) ∈ {±1} + c^e ℤ`, get `Σ_(k<d) s_k ≡ d·h (mod c^(min(e, n+1)))`.  For `n` large
   both sides are small integers (`|Σ ±1| ≤ d`, `h` fixed), so `Σ_(k<d) ε_k = d·h` exactly with
   `ε_k ∈ {±1}`.  `d` is odd, so `|d·h| ≤ d` forces `h = ±1` and every `ε_k = h`.
4. Then `u(c^(n+k)) ≡ 0 (mod c^e)` for every `k < d`.  But by the period (phase 51,
   `OrbitSum.pow_prime_pow_add_card_congr`), `u(c^m) ≡ u(c^(m mod d)) (mod c)`, and the residues
   `n, …, n+d−1` cover `r`: contradiction with `c ∤ u(c^r)`.

Frozen: the three statements below and the def `trib`; all earlier statements; `Literature/`.
No `private`.  Helpers public; add as many as needed.
-/

namespace LeanFormalizations.Mills.TheoremA

open Matrix Filter

/-- **Theorem A.** -/
theorem entry_prime_pow_add_not_prime {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ}
    (hc : c.Prime) (hirr : Irreducible (A.charpoly.map (Int.castRingHom (ZMod c))))
    (hodd : Odd d) (hmu : c = 2 ∨ ∀ k, 3 ≤ k → k ≤ d → ¬ k ∣ c - 1) {i j : Fin d} (hij : i ≠ j)
    (hnz : ∃ r < d, ¬ (c : ℤ) ∣ (A ^ (c ^ r)) i j)
    (hgrow : Tendsto (fun n => |(A ^ (c ^ n)) i j|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((A ^ (c ^ n)) i j + h) := by
  sorry

/-- Tribonacci: `T 0 = T 1 = 0`, `T 2 = 1`, `T (n+3) = T (n+2) + T (n+1) + T n`. -/
def trib : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => trib (n + 2) + trib (n + 1) + trib n

/-- **`T(3^n) + h` is composite for infinitely many `n`, for every `h`.** -/
theorem trib_three_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (trib (3 ^ n) + h) := by
  sorry

/-- **`T(5^n) + h` is composite for infinitely many `n`, for every `h`.** -/
theorem trib_five_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (trib (5 ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.TheoremA

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremA

/-!
# Phase 53: prime-free intervals around Tribonacci `T(3^n)` (Theorem C for an order-3 recurrence)

For `n ≡ 95 (mod 1980)`, all seven numbers `T(3^n) + h` with `|h| ≤ 3` are composite.  Each is
divisible by a fixed small prime:

| `h` | prime | `ord_p(A)` | `T(3^95) mod p` |
|---|---|---|---|
| −3 | 53 | 52 = 2²·13 | 3 |
| −2 | 5 | 31 | 2 |
| −1 | 7 | 48 = 2⁴·3 | 1 |
| 0 | 13 | 168 = 2³·3·7 | 0 |
| 1 | 593 | 3256 = 2³·11·37 | 592 |
| 2 | 47 | 46 = 2·23 | 45 |
| 3 | 5 | 31 | 2 |

`A = TheoremA.tribMat` (`T N = (A^N) 2 0` is `TheoremA.tribMat_pow_apply`).  Found by
`scripts/tribonacci-covering-search.py 3 14 800` and checked for `k < 6` by `scripts/tribonacci-covering-verify.py`.
Control: at `n = 96` six of the seven divisibilities fail.

## Route
1. For each `p`: `A^o = 1` over `ZMod p` with `o = ord_p(A)` from the table (`decide`/`native_decide`
   on `Matrix (Fin 3) (Fin 3) (ZMod p)`; split `o` with `pow_mul` if `npow` is slow).
2. `o ∣ 3^95 · (3^1980 − 1)` (`norm_num`/`decide` on `ℕ`), so `3^(1980k + 95) ≡ 3^95 (mod o)`, hence
   `A^(3^(1980k+95)) = A^(3^95)` over `ZMod p`.  (`3^95 ≥ v₃(o)` trivially; `3^1980 ≡ 1` modulo the
   3-free part of `o`.)  Use `pow_eq_pow_mod`-style reduction: `A^N = A^(N % o)` when `A^o = 1`.
3. `(A^(3^95)) 2 0` over `ZMod p` from the table (`native_decide` with the reduced exponent
   `3^95 % o`).  Transfer to `ℤ` via `Matrix.map` / `Int.cast` and phase 52's `trib = entry` lemma.
4. Composite: `trib (3^(1980k+95)) + h` is divisible by `p` and exceeds `p` in absolute value
   (`T(3^95)` is astronomically larger than 593; monotonicity of `trib`), so it is not prime.

Frozen: `tribCoverPrime` and the three statements below; all earlier statements; `Literature/`.
No `private`.
-/

namespace LeanFormalizations.Mills.TribonacciCovering

open LeanFormalizations.Mills.TheoremA Filter

/-- The covering prime for the shift `h`, `|h| ≤ 3`. -/
def tribCoverPrime (h : ℤ) : ℤ :=
  if h = -3 then 53 else if h = -2 then 5 else if h = -1 then 7 else if h = 0 then 13
  else if h = 1 then 593 else if h = 2 then 47 else 5

/-- **Covering:** `p_h ∣ T(3^(1980k + 95)) + h` for every `k` and `|h| ≤ 3`. -/
theorem trib_three_pow_covering (k : ℕ) (h : ℤ) (hh : |h| ≤ 3) :
    tribCoverPrime h ∣ trib (3 ^ (1980 * k + 95)) + h := by
  sorry

/-- **Seven consecutive composites** around `T(3^(1980k + 95))`. -/
theorem trib_three_pow_prime_free (k : ℕ) (h : ℤ) (hh : |h| ≤ 3) :
    ¬ Prime (trib (3 ^ (1980 * k + 95)) + h) := by
  sorry

/-- **Prime-free intervals `[T(3^n) − 3, T(3^n) + 3]` for infinitely many `n`.** -/
theorem trib_three_pow_prime_free_often :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ 3 → ¬ Prime (trib (3 ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.TribonacciCovering

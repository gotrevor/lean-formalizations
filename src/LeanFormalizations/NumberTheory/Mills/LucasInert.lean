/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasPrimePow

/-!
# Phase 36: `U_(c^n)(P,Q) + h` is composite i.o. at every odd prime `c` inert in `ℚ(√D)`

Phase 34 did Fibonacci; phase 33 did `c = 2` for all `P, Q` odd (the condition that `2` is inert
in `ℚ(√D)`, `D = P² − 4Q`).  This phase generalizes both at odd `c`.  See
`SWEEP-PRIME-MODULUS.md`.  The sign flip was checked numerically for 756 cases
(`|P|, |Q| ≤ 5`, `c ≤ 13`, `n ≤ 2`).

## Route
`lucasU P Q N = (A^N) 1 0` with `A = !![P, -Q; 1, 0]` (phase 33), `det A = Q`, and
`A^N = !![U_(N+1), −Q U_N; U_N, −Q U_(N−1)]`.
1. `lucasU_frobenius_inert`: `c ∣ U_(c+1)` and `c ∣ U_c + 1`, i.e. `A^(c+1) ≡ Q·I (mod c)`.
   `X² − PX + Q` is irreducible over `ZMod c` because `D` is a non-square, so Frobenius
   swaps its roots: `x^c = x'` and `x^(c+1) = x x' = Q`.  Generalize phase 34's
   `fib_frobenius_inert` proof (which was the case `P = 1`, `Q = −1`).
2. `lucasU_prime_pow_succ_add`: `c^(n+1) ∣ U(c^(n+1)) + U(c^n)`.  Lift step 1 to
   `A^(c^n (c+1)) ≡ Q^(c^n) I (mod c^(n+1))` (binomial), then read entry `(1,0)` of
   `A^(c^(n+1)) · A^(c^n) ≡ Q^(c^n) I`, using `U_(−N) = −Q^(−N) U_N` or directly the product
   formula `U_(a+b) = U_a U_(b+1) − Q U_(a−1) U_b`.  Follow phase 34's `fib_prime_pow_succ_add`.
3. Main theorem as in phase 34, using `pow_dvd_sub_or_add_of_lt_padicValNat` and
   `exists_entry_pow_congr` (with `p ∤ Q` for large `|p_n|`).  `h = 0`: `U(c^n) ∣ U(c^(n+1))`
   plus growth.  `h = ±1`: `U(c^n) ≡ (−1)^n (mod c)` is a unit.  Values may be negative and
   non-monotone, so work with `natAbs` and a large multiple of the period `j` (as in phase 33).

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.LucasInert

open LeanFormalizations.Mills.ThreeAdic LeanFormalizations.Mills.LucasTwoPow Filter

/-- Frobenius at an inert prime: `A^(c+1) ≡ Q·I (mod c)`, entrywise. -/
theorem lucasU_frobenius_inert {P Q : ℤ} {c : ℕ} (hc : c.Prime)
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) :
    (c : ℤ) ∣ lucasU P Q (c + 1) ∧ (c : ℤ) ∣ lucasU P Q c + 1 := by
  sorry

/-- **The sign flip at an inert prime.** -/
theorem lucasU_prime_pow_succ_add {P Q : ℤ} {c : ℕ} (hc : c.Prime) (hQ : ¬ (c : ℤ) ∣ Q)
    (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c)) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ lucasU P Q (c ^ (n + 1)) + lucasU P Q (c ^ n) := by
  sorry

/-- **`U_(c^n)(P,Q) + h` is composite infinitely often**, for every odd prime `c ∤ Q` that is
inert in `ℚ(√(P² − 4Q))`, whenever `|U(c^n)| → ∞`, and every `h`. -/
theorem lucasU_prime_pow_add_not_prime {P Q : ℤ} {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hQ : ¬ (c : ℤ) ∣ Q) (hD : ¬ IsSquare ((P ^ 2 - 4 * Q : ℤ) : ZMod c))
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (c ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.LucasInert

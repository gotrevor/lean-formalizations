/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ShiftedWindow

/-!
# Phase 47: `A^(c^n)` is eventually periodic `c`-adically (Teichmüller limit, in integers)

Foundation for the limit-point sub-node (R2) of `ShiftedTraceRigidity` (`ROADMAP-PRIME-TOWERS.md` §4-live):
the sequence `A^(c^n)` has finitely many `c`-adic limit points, as a congruence statement about
integer matrices (no `ℤ_c` needed).

## Route
1. Let `A` be invertible mod `c` and `ord = c^a · o` its order in `GL_d(ZMod c)` with `c ∤ o`.  Take `f ≥ 1` with
   `c^f ≡ 1 (mod o)` (e.g. `f = φ(o)`, or `1` if `o = 1`).
2. Base (`n = a`): `A^(c^(a+f)) ≡ A^(c^a) (mod c)`, because `ord ∣ c^a (c^f − 1)`.  More generally the same holds for all `n ≥ a`.
3. Lifting: if `X ≡ Y (mod c^e)` entrywise, `e ≥ 1`, and `X`, `Y` commute (both are powers of `A`), then
   `X^c ≡ Y^c (mod c^(e+1))`.  Write `X = Y + c^e Z` with `Z` a polynomial in `A`; in the binomial
   expansion every term but `Y^c` is divisible by `c^(e+1)` (`c ∣ binom(c, i)` for `0 < i < c`, and
   `c^(ce) ⊇ c^(e+1)`).
4. Induction on `n ≥ a` with `A^(c^(n+1+f)) = (A^(c^(n+f)))^c` gives exponent `n − a + 1`.

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
-/

namespace LeanFormalizations.Mills.TeichmullerCongruence

theorem pow_prime_pow_period_congr {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) {c : ℕ} (hc : c.Prime)
    (hunit : ¬ (c : ℤ) ∣ A.det) :
    ∃ f a : ℕ, 1 ≤ f ∧ ∀ n ≥ a, ∀ i j,
      (c : ℤ) ^ (n - a + 1) ∣ (A ^ (c ^ (n + f)) - A ^ (c ^ n)) i j := by
  sorry

end LeanFormalizations.Mills.TeichmullerCongruence

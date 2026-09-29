/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoFibonacci

/-!
# Phase 33: Saito's Problem 1.8 for every Lucas sequence `U(P,Q)` with `P, Q` odd

Phase 32 answered Saito's Problem 1.8 (arXiv:2504.14968): `F(2^n) + h` is composite i.o. for
every `h`.  The argument uses only three facts, each of which holds for the Lucas sequence
`U_N(P,Q)` (`U₀ = 0`, `U₁ = 1`, `U_(N+2) = P U_(N+1) − Q U_N`) whenever `P` and `Q` are odd:
1. `U(2^n)` is odd (`U_N` is even iff `3 ∣ N` when `P, Q` are odd).
2. **Sign flip**: `2^(n+1) ∣ U(2^(n+1)) + U(2^n)` for `n ≥ 1`.  `U(2m) = U(m) V(m)` with
   `V(m) = 2U(m+1) − P U(m)`, and `V(2m) = V(m)^2 − 2Q^m`; since `Q^(2^n) ≡ 1 (mod 2^(n+2))`,
   the induction `2^(n+1) ∣ V(2^n) + 1` of phase 32 goes through with one extra term.
   Base: `V(2) + 1 = P^2 − 2Q + 1 ≡ 2 − 2Q ≡ 0 (mod 4)`.  Checked numerically for
   `(P,Q) ∈ {(1,-1),(3,1),(1,3),(3,-1),(5,3),(-1,-5),(7,-3)}`, `n ≤ 10`.
3. **Mechanism**: `U_N = (A^N) 1 0` for `A = !![P, -Q; 1, 0]`, `det A = Q`; for a prime
   `p ∤ Q` the phase-32 lemma `exists_entry_pow_congr` applies (it is `private` in
   `SaitoFibonacci.lean`: make it public, changing nothing else there).

Differences from phase 32 the proof must handle:
- `U(2^n)` need not be positive or monotone; the hypothesis is `|U(2^n)| → ∞`.  Work with
  `natAbs`.  Prime in `ℤ` is up to sign.
- The mechanism gives some `j ≥ 1` with `p ∣ U(2^(n+j)) − U(2^n)`; the proof shows
  `D^(c^(m+j)) = D^(c^m)`, hence also for every multiple of `j`.  Use a large multiple so that
  `|p_(n+kj)| > |p_n|` (growth), contradicting primality.
- `p ∤ Q` holds once `|p_n| > |Q|`.
- The `(1, 1)` sequence is periodic (degenerate), which is why growth is assumed.

Frozen: every statement below; `SaitoFibonacci.lean` statements (only the visibility of
`exists_entry_pow_congr` may change); `ThreeAdic`, `SharedConjecture`, `Projective`, `Literature/`.
-/

namespace LeanFormalizations.Mills.LucasTwoPow

open LeanFormalizations.Mills.ThreeAdic Filter

/-- The Lucas sequence `U_N(P,Q)`, as the `(1,0)` entry of `!![P, -Q; 1, 0] ^ N`. -/
def lucasU (P Q : ℤ) (N : ℕ) : ℤ := ((!![P, -Q; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ N) 1 0

/-- Sanity: `U(1, -1)` is Fibonacci. -/
theorem lucasU_one_neg_one (N : ℕ) : lucasU 1 (-1) N = Nat.fib N := by
  sorry

/-- The recurrence, as a sanity check on the definition. -/
theorem lucasU_add_two (P Q : ℤ) (N : ℕ) :
    lucasU P Q (N + 2) = P * lucasU P Q (N + 1) - Q * lucasU P Q N := by
  sorry

/-- `U(2^n)` is odd when `P, Q` are odd. -/
theorem lucasU_two_pow_odd {P Q : ℤ} (hP : Odd P) (hQ : Odd Q) (n : ℕ) :
    Odd (lucasU P Q (2 ^ n)) := by
  sorry

/-- **The sign flip** for `P, Q` odd. -/
theorem two_pow_dvd_lucasU_two_pow_succ_add {P Q : ℤ} (hP : Odd P) (hQ : Odd Q) (n : ℕ)
    (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n + 1) ∣ lucasU P Q (2 ^ (n + 1)) + lucasU P Q (2 ^ n) := by
  sorry

/-- **Saito's Problem 1.8, for every Lucas sequence with `P, Q` odd.**  If `|U(2^n)| → ∞`
then `U(2^n) + h` is not prime for infinitely many `n`, for every integer `h`. -/
theorem lucasU_two_pow_add_not_prime {P Q : ℤ} (hP : Odd P) (hQ : Odd Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (2 ^ n)|) atTop atTop) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasU P Q (2 ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.LucasTwoPow

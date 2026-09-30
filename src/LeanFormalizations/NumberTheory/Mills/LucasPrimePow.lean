/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciPrimePow

/-!
# Phase 35: `L(c^n) + h` is composite i.o. for every odd prime `c` and every `h`

Lucas numbers `L(N) = tr A^N` (`A = !![1,1;1,0]`) are a **trace** sequence, so Frobenius fixes
them and there is no sign flip (phase 34).  Instead we use an **exact** composition identity.
See `SWEEP-PRIME-MODULUS.md`.

## Route
Let `lucasV x q k` be the Lucas `V`-sequence with parameters `P = x`, `Q = q`
(`V₀ = 2`, `V₁ = x`, `V_(k+2) = x V_(k+1) − q V_k`).
1. `lucasV_mul_odd`: for odd `m`, `V_(c·m)(P,−1) = lucasV (V_m) (−1) c`.  Route: for a 2×2 matrix `B`,
   Cayley–Hamilton gives `B^2 = (tr B) B − (det B) I`, so `tr (B^k) = lucasV (tr B) (det B) k`
   by induction; apply to `B = A^m` for `A = !![P, 1; 1, 0]` (`tr = V_m`, `det = (−1)^m = −1`).
2. `lucasV_neg_one_growth`: for odd `c ≥ 3` and `x ≠ 0`, `|x| + 3 ≤ |lucasV x (−1) c|`.  For
   `x ≥ 1` the sequence is increasing from `k = 1` and `V_3 = x^3 + 3x`; for `x ≤ −1` use
   oddness, `lucasV (−x) (−1) c = −lucasV x (−1) c` for odd `c`.
3. `lucas_prime_pow_mod`: `L(c^n) ≡ 1 (mod c)` (from `lucasV x (−1) c ≡ x^c ≡ x (mod c)` and
   Fermat, or from `L(c) ≡ 1` plus step 1).
4. Main theorem.  Suppose `p_n = L(c^n) + h` is prime for all `n ≥ n₀`.
   - The filter: `SharedConjecture.exists_trace_pow_congr` with base `c` (the trace version;
     `det A = −1`), plus growth, gives `n < v_c(glCard 2 p_n)` for large `n`.  Then
     `FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat` gives `L(c^n) ≡ x_n (mod c^(n/2))`
     with `x_n ∈ {1 − h, −1 − h}`.
   - Step 1 (with `c^n` odd) and integrality of `lucasV` give `x_(n+1) ≡ lucasV x_n (−1) c`.
     Both sides lie in fixed finite sets, so for large `n` this is an equality, and
     `|x_(n+1) − x_n| ≤ 2`.
   - Step 2 forces `x_n = 0`, hence `c^(n/2) ∣ L(c^n)`, contradicting step 3.

Note that `c = 2` is genuinely excluded: `L(2^n)` (`h = 0`) is a Fermat-type open problem.

Frozen: every statement below; statements of `FibonacciPrimePow`, `SaitoFibonacci`,
`LucasTwoPow`, `ThreeAdic`, `SharedConjecture`, `Projective`, and `Literature/`.  Do not mark new
declarations `private`.
-/

namespace LeanFormalizations.Mills.LucasPrimePow

open LeanFormalizations.Mills.ThreeAdic Filter

/-- The Lucas `V`-sequence with parameters `P = x`, `Q = q`. -/
def lucasV (x q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => x
  | k + 2 => x * lucasV x q (k + 1) - q * lucasV x q k

/-- The Lucas numbers, `L(N) = F(N−1) + F(N+1)`, as integers (`L 0 = 2`). -/
def lucasL (N : ℕ) : ℤ := lucasV 1 (-1) N

theorem lucasL_eq_fib (N : ℕ) : lucasL (N + 1) = Nat.fib N + Nat.fib (N + 2) := by
  sorry

/-- **Composition.**  For odd `m`, `V_(c·m)(P, −1) = V_c(V_m(P, −1), −1)`; e.g. `L(c·m) = V_c(L(m), −1)`. -/
theorem lucasV_mul_odd (P : ℤ) (c : ℕ) {m : ℕ} (hm : Odd m) :
    lucasV P (-1) (c * m) = lucasV (lucasV P (-1) m) (-1) c := by
  sorry

/-- For odd `c ≥ 3` and `x ≠ 0`, `V_c(x, −1)` is far from `x`. -/
theorem lucasV_neg_one_growth {c : ℕ} (hc : Odd c) (hc3 : 3 ≤ c) {x : ℤ} (hx : x ≠ 0) :
    |x| + 3 ≤ |lucasV x (-1) c| := by
  sorry

/-- `L(c^n) ≡ 1 (mod c)` for a prime `c`. -/
theorem lucas_prime_pow_mod {c : ℕ} (hc : c.Prime) (n : ℕ) :
    (c : ℤ) ∣ lucasL (c ^ n) - 1 := by
  sorry

/-- **General `P`.**  For `Q = −1`, an odd prime `c ∤ P`, and every `h`, `V(c^n) + h` is composite
infinitely often.  (Same proof: `V_(c^n)(P, −1) ≡ P (mod c)` replaces step 3; `P ≠ 0` gives
growth.  If `c ∣ P` the survivors `h = ±1` genuinely appear.) -/
theorem lucasV_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP : ¬ (c : ℤ) ∣ P) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasV P (-1) (c ^ n) + h) := by
  sorry

/-- **`L(c^n) + h` is composite infinitely often, for every odd prime `c` and every `h`.** -/
theorem lucas_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime (lucasL (c ^ n) + h) := by
  sorry

end LeanFormalizations.Mills.LucasPrimePow

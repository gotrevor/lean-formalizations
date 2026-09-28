/-
# Sylvester's theorem: polynomial iterations from `0` are strong divisibility sequences

A sequence `u : ℕ → ℤ` is a **strong divisibility sequence** (SDS) if
`gcd(u m, u n) = |u (gcd m n)|` for all `m, n`.  (With `u 0 = 0` the `m = 0` case is automatic,
so this is the usual `m, n ≥ 1` definition.)

* **Sylvester** (Dickson, *History of the Theory of Numbers* I, p. 403): if `P ∈ ℤ[X]`,
  `u 0 = 0` and `u (n+1) = P(u n)`, then `u` is an SDS.
* **Bala (2026), Theorem 1**: for any start value, `n ↦ u(n+k) − u(k)` is an SDS for every `k`;
  if `P` is even, so is `n ↦ u(n+k) + u(k)`.  (P. Bala, *Sylvester's theorem and strong
  divisibility sequences*, 2026, <https://oeis.org/A000058/a000058_1.pdf>; local copy
  `papers/bala-2026-sylvester-strong-divisibility.{pdf,txt}`.)

Proof sketch for Sylvester: `a ≡ b (mod a − b)` gives `P^[n](x) ≡ P^[n](0) (mod x)`, so
`u m ∣ u (m + n) − u n`; then the Euclidean algorithm on indices, exactly as for Fibonacci
(`Nat.fib_gcd`).  Bala's Theorem 1 is Sylvester applied to `Q(x) = P(x + u k) − u k`
(resp. `P(x − u k) + u k`, using evenness).
-/
import Mathlib

namespace LeanFormalizations.PolyIteration

open Polynomial

/-- `u` is a strong divisibility sequence. -/
def IsStrongDivSeq (u : ℕ → ℤ) : Prop :=
  ∀ m n : ℕ, Int.gcd (u m) (u n) = (u (Nat.gcd m n)).natAbs

/-- **Sylvester's theorem.** -/
theorem isStrongDivSeq_of_iterate (P : ℤ[X]) (u : ℕ → ℤ) (h0 : u 0 = 0)
    (hu : ∀ n, u (n + 1) = P.eval (u n)) : IsStrongDivSeq u := by
  sorry

/-- **Bala (2026), Theorem 1 (i).** -/
theorem isStrongDivSeq_sub (P : ℤ[X]) (u : ℕ → ℤ) (hu : ∀ n, u (n + 1) = P.eval (u n))
    (k : ℕ) : IsStrongDivSeq (fun n ↦ u (n + k) - u k) := by
  sorry

/-- **Bala (2026), Theorem 1 (ii)**: for even `P`. -/
theorem isStrongDivSeq_add (P : ℤ[X]) (hP : ∀ x, P.eval (-x) = P.eval x) (u : ℕ → ℤ)
    (hu : ∀ n, u (n + 1) = P.eval (u n)) (k : ℕ) :
    IsStrongDivSeq (fun n ↦ if n = 0 then 0 else u (n + k) + u k) := by
  sorry

end LeanFormalizations.PolyIteration

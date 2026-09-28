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

/-- `Int.gcd` is unchanged along `a`-shifts of the second argument. -/
theorem intGcd_congr_of_dvd_sub {a b c : ℤ} (h : a ∣ b - c) :
    Int.gcd a b = Int.gcd a c := by
  have key : ∀ x y : ℤ, a ∣ x - y → Int.gcd a x ∣ Int.gcd a y := by
    intro x y hxy
    refine Int.dvd_gcd (Int.gcd_dvd_left a x) ?_
    have h1 : (Int.gcd a x : ℤ) ∣ x - y := dvd_trans (Int.gcd_dvd_left a x) hxy
    have h2 : (Int.gcd a x : ℤ) ∣ x := Int.gcd_dvd_right a x
    simpa using dvd_sub h2 h1
  exact Nat.dvd_antisymm (key _ _ h) (key _ _ (by simpa using (dvd_neg.mpr h)))

section
variable (P : ℤ[X]) (u : ℕ → ℤ) (hu : ∀ n, u (n + 1) = P.eval (u n))
include hu

/-- Iterating `P` preserves index-shifted differences: `u a − u b ∣ u (a+n) − u (b+n)`. -/
theorem sub_dvd_sub_shift (a b : ℕ) : ∀ n, u a - u b ∣ u (a + n) - u (b + n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have : u (a + (n + 1)) - u (b + (n + 1)) = P.eval (u (a + n)) - P.eval (u (b + n)) := by
        rw [← Nat.add_assoc, ← Nat.add_assoc, hu (a + n), hu (b + n)]
      rw [this]
      exact dvd_trans ih (Polynomial.sub_dvd_eval_sub _ _ P)

/-- With `u 0 = 0`: `u m ∣ u (t + m) − u t`. -/
theorem dvd_sub_of_add (h0 : u 0 = 0) (m t : ℕ) : u m ∣ u (t + m) - u t := by
  have := sub_dvd_sub_shift P u hu m 0 t
  rw [h0, sub_zero] at this
  rwa [Nat.add_comm m t, Nat.zero_add] at this

/-- With `u 0 = 0`: `u m ∣ u (t + m * q) − u t`. -/
theorem dvd_sub_of_add_mul (h0 : u 0 = 0) (m t q : ℕ) : u m ∣ u (t + m * q) - u t := by
  induction q with
  | zero => simp
  | succ q ih =>
      have step : u m ∣ u (t + m * q + m) - u (t + m * q) := dvd_sub_of_add P u hu h0 m _
      have : t + m * (q + 1) = t + m * q + m := by ring
      rw [this]
      simpa using dvd_add step ih

end

/-- **Sylvester's theorem.** -/
theorem isStrongDivSeq_of_iterate (P : ℤ[X]) (u : ℕ → ℤ) (h0 : u 0 = 0)
    (hu : ∀ n, u (n + 1) = P.eval (u n)) : IsStrongDivSeq u := by
  intro m n
  induction m, n using Nat.gcd.induction with
  | H0 n => simp [h0]
  | H1 m n hm ih =>
      have hnm : n % m + m * (n / m) = n := by
        have := Nat.mod_add_div n m
        omega
      have hd : u m ∣ u n - u (n % m) := by
        have := dvd_sub_of_add_mul P u hu h0 m (n % m) (n / m)
        rwa [hnm] at this
      have : Int.gcd (u m) (u n) = Int.gcd (u m) (u (n % m)) :=
        intGcd_congr_of_dvd_sub hd
      rw [this, Nat.gcd_rec m n, Int.gcd_comm]
      exact ih

/-- **Bala (2026), Theorem 1 (i).** -/
theorem isStrongDivSeq_sub (P : ℤ[X]) (u : ℕ → ℤ) (hu : ∀ n, u (n + 1) = P.eval (u n))
    (k : ℕ) : IsStrongDivSeq (fun n ↦ u (n + k) - u k) := by
  set Q : ℤ[X] := P.comp (X + C (u k)) - C (u k) with hQ
  refine isStrongDivSeq_of_iterate Q _ (by simp) ?_
  intro n
  have : n + 1 + k = (n + k) + 1 := by ring
  simp [hQ, this, hu (n + k)]

/-- **Bala (2026), Theorem 1 (ii)**: for even `P`. -/
theorem isStrongDivSeq_add (P : ℤ[X]) (hP : ∀ x, P.eval (-x) = P.eval x) (u : ℕ → ℤ)
    (hu : ∀ n, u (n + 1) = P.eval (u n)) (k : ℕ) :
    IsStrongDivSeq (fun n ↦ if n = 0 then 0 else u (n + k) + u k) := by
  set Q : ℤ[X] := P.comp (X - C (u k)) + C (u k) with hQ
  refine isStrongDivSeq_of_iterate Q _ (by simp) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (0 : ℕ) + 1 + k = k + 1 := by ring
    simp [hQ, this, hu k, hP (u k)]
  · have h1 : n ≠ 0 := hn.ne'
    have h2 : n + 1 ≠ 0 := Nat.succ_ne_zero n
    have h3 : n + 1 + k = (n + k) + 1 := by ring
    simp [hQ, h1, h3, hu (n + k)]

end LeanFormalizations.PolyIteration

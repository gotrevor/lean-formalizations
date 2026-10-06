/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Lacunary Fibonacci reciprocal sums: the tiling bedrock (phase LF1)

Erdős #267 asked whether `∑ 1/F_(n_k)` is irrational when `n (k + 1) ≥ c · n k` with `c > 1`.
Snyder 2026 settled it (`ErdosDyadic.Snyder2026Erdos267`).  Nguyen 2022 proved transcendence for
`c > 2` (`Nguyen2022`), which is sharp because `∑ 1/F_(2^k) = (7 − √5)/2` (`millin`).  The open
question is what happens at and below the boundary `c = 2`.

**Why doubling is algebraic: a tiling.**  For even `n`, `1/F_n = √5 ∑_j φ^(−(2j+1)n)`
(`fib_inv_eq_tsum_of_even`), so a sum over `n_k = 2^k` is a power series in `φ⁻¹` supported on the
odd multiples of the `2^k`.  Those sets tile the positive integers, so the series collapses.  For
`k` restricted to a set `K`, the support is `{m : v₂ m ∈ K}` (`restricted_sum_eq_tiling`).  That
set is eventually periodic iff `K` is finite or cofinite (`vTwo_eventuallyPeriodic_iff`).

⚠️ **Numerics are blind here.**  At `P` digits, only the terms with `2^k ≲ 2.3 P` are visible.
So any `K` that agrees with a cofinite set up to `k ≈ log₂ P` looks algebraic to a polynomial
search; a 400-digit `findpoly` "found" `(5 − √5)/2` for a Sturmian `K` (2026-10-05).  This
conjecture can only be tested by proof.
-/

namespace LeanFormalizations.LacunaryFib

open Filter Real

/-- **Node A (believed ~99%): the Lambert expansion for even `n`.**  `F_n = (φ^n − φ^(−n))/√5` when
`n` is even (Binet, `ψ^n = φ^(−n)`), so `1/F_n = √5 φ^(−n) / (1 − φ^(−2n))`. -/
theorem fib_inv_eq_tsum_of_even {n : ℕ} (hn : 0 < n) (he : Even n) :
    ((Nat.fib n : ℝ))⁻¹ = √5 * ∑' j : ℕ, (goldenRatio⁻¹) ^ ((2 * j + 1) * n) := by
  sorry

/-- **Node B (believed ~99%): Millin's step.**  For even `m > 0`,
`F_(m−1) F_(2m) − F_m F_(2m−1) = F_m`, so `1/F_(2m)` is a difference of consecutive convergent-like
ratios `F_(m−1)/F_m`.  Example: `m = 2` gives `1/3 = 1 − 2/3`. -/
theorem fib_two_mul_inv {m : ℕ} (hm : 0 < m) (he : Even m) :
    ((Nat.fib (2 * m) : ℝ))⁻¹ =
      (Nat.fib (m - 1) : ℝ) / Nat.fib m - (Nat.fib (2 * m - 1) : ℝ) / Nat.fib (2 * m) := by
  sorry

/-- **Millin's series (the control, believed ~99%).**  Terms `k = 0, 1` give `2`; the rest
telescope by `fib_two_mul_inv` to `F_1/F_2 − 1/φ = (3 − √5)/2`. -/
theorem millin : ∑' k : ℕ, ((Nat.fib (2 ^ k) : ℝ))⁻¹ = (7 - √5) / 2 := by
  sorry

/-- **Node B′ (believed ~95%): every doubling tail is algebraic.**  Millin's telescoping applies
to `a·2^(k+1)` for every `a > 0`, since each step index `a·2^k` with `k ≥ 1` is even.  The value
lies in `ℚ(√5)`. -/
theorem doubling_tail_algebraic (a : ℕ) (ha : 0 < a) :
    IsAlgebraic ℚ (∑' k, ((Nat.fib (a * 2 ^ (k + 1)) : ℝ))⁻¹) := by
  sorry

/-- **Node D (believed ~99%): which `2`-adic supports are periodic.**  If `K` is finite with
maximum `k₀`, the period `2^(k₀+1)` works (and the complement for cofinite `K`).  Conversely, if
`p = 2^a·b` with `b` odd is a period and `m` has `v₂ m > a`, then `v₂ (m + p) = a`, so every `k > a`
has the membership of `a`. -/
theorem vTwo_eventuallyPeriodic_iff (K : Set ℕ) :
    (∃ p > 0, ∀ᶠ m in atTop, (padicValNat 2 (m + p) ∈ K ↔ padicValNat 2 m ∈ K)) ↔
      K.Finite ∨ Kᶜ.Finite := by
  sorry

open scoped Classical in
/-- **Node E (believed ~97%): the tiling identity.**  For `K ⊆ {k ≥ 1}`, node A for each
`n = 2^k`, regrouped by the unique factorization `m = 2^(v₂ m) · odd`. -/
theorem restricted_sum_eq_tiling (K : Set ℕ) (hK : ∀ k ∈ K, 1 ≤ k) :
    ∑' k : K, ((Nat.fib (2 ^ (k : ℕ)) : ℝ))⁻¹ =
      √5 * ∑' m : ℕ, if 0 < m ∧ padicValNat 2 m ∈ K then (goldenRatio⁻¹) ^ m else 0 := by
  sorry

end LeanFormalizations.LacunaryFib

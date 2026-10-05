/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Practical.Basic

/-!
# Erdős #18: how many divisors are needed (exploration, 2026-10-05)

`h(n)`: the least `j` such that every `1 ≤ k ≤ n` is a sum of at most `j` distinct divisors of
`n` (formal-conjectures `Erdos18.practicalH`; erdosproblems.com/18, $250 on the first question).
Erdős asked: (a) infinitely many practical `m` with `h(m) < (log log m)^{O(1)}`?  (b) `h(n!) <
n^{o(1)}`?  (c) `h(n!) < (log n)^{O(1)}`?  Known: `h(n!) < n` (Erdős), `h(m) ≪ (log m)^{1/2}`
infinitely often (Vose 1985).

Recorded here:
* `card_le_pow_practicalH` (counting): `n + 1 ≤ (τ(n) + 1)^{h(n)}`.  So `h(n) ≥ log n / log τ(n)`,
  which is `≫ log log n` for every `n` (exponent ≥ 1 in (a)), and for `n!` it is `≍ (log n)²`
  (`log τ(n!) ~ C n / log n`, `C = Σ_k log(k+1)/(k(k+1)) ≈ 1.28`): `practicalH_factorial_ge`.
  So in (c) the exponent is at least 2.  Ren's derivation; not found in the sources checked
  (erdosproblems.com/18 thread, Pomerance–Weingartner 2021, Erdős–Graham 1980 p. 33, which
  states only the upper bound `< n` and guesses "perhaps even only `(log n)^c`").
* `practicalH_le_of_dense` (greedy): if every `r ∈ (K, n]` has a divisor `d ≤ r` with
  `r − d ≤ r^{1−ε}` and `r − d < d`, and every `r ≤ K` divides `n`, then each greedy step
  multiplies `log r` by `≤ 1 − ε`.  This is the reduction posted on the erdosproblems.com/18 thread
  (must4f4isik, 2026-09-14), which reports greedy bounds `G(L_61) ≤ 12`.
* `LcmDivisorsDense`: the open premise for `L_x = lcm(1..x)` with `ε = c / log x`;
  `erdos18a_of_lcmDivisorsDense` wires it to (a).  Difficulty: the premise asks for divisors of
  `L_x` in every window `[r − r^{1−c/log x}, r]`.  The divisor count `τ(m) ≤ m^{O(1/log log m)}`
  makes `ε ≍ 1/log log m` the best possible scale, so the premise is an equidistribution
  statement for `log`-divisors at that scale.  No mechanism is known (the thread notes
  Tenenbaum's divisor-density results are weaker).
-/

namespace LeanFormalizations.Practical

open Finset Filter Real

/-- The least number of distinct divisors of `n` summing to `k` (`0` if none: `sInf ∅ = 0`). -/
noncomputable def minTerms (n k : ℕ) : ℕ :=
  sInf {j | ∃ s ⊆ n.divisors, s.card = j ∧ ∑ d ∈ s, d = k}

/-- Erdős's `h(n)`: the max of `minTerms n k` over `1 ≤ k ≤ n` (as formal-conjectures'
`Erdos18.practicalH`; meaningful for practical `n`). -/
noncomputable def practicalH (n : ℕ) : ℕ := (Icc 1 n).sup (minTerms n)

/-- **Counting lower bound.**  Each `0 ≤ k ≤ n` is the sum of a set of at most `h(n)` divisors,
and there are at most `(τ(n) + 1)^{h(n)}` such sets.  Believed 99%.  Checks: `n = 6`
(`7 ≤ 5² = 25`), `n = 12` (`13 ≤ 7³ = 343`). -/
theorem card_le_pow_practicalH {n : ℕ} (hn : IsPractical n) :
    n + 1 ≤ (n.divisors.card + 1) ^ practicalH n := by
  sorry

/-- **`h(n!) ≥ (log n)² / 2` eventually** (Erdős (c) needs exponent `≥ 2`).  From
`card_le_pow_practicalH` and `log τ(n!) ≤ (C + o(1)) n / log n` with `C ≈ 1.28 < 2` (`v_p(n!) ≈
⌊n/p⌋`, PNT; the constant is `Σ_k log(k+1)/(k(k+1))`).  Believed 92% (the `τ(n!)` asymptotic is
Ren's computation, not checked against a source). -/
theorem practicalH_factorial_ge :
    ∀ᶠ n : ℕ in atTop, (log n) ^ 2 / 2 ≤ (practicalH n.factorial : ℝ) := by
  sorry

/-- **Greedy bound.**  Under the density hypothesis, the greedy algorithm (subtract the largest
divisor `≤ r`) uses strictly decreasing divisors, and after `j` steps `log r ≤ (1 − ε)^j log n
≤ log K`; one more step finishes because every `r ≤ K` divides `n`.  Believed 97%. -/
theorem practicalH_le_of_dense (n K j : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hK : 1 ≤ K)
    (hsmall : ∀ r, 1 ≤ r → r ≤ K → r ∣ n)
    (hdense : ∀ r : ℕ, K < r → r ≤ n →
      ∃ d ∈ n.divisors, d ≤ r ∧ ((r - d : ℕ) : ℝ) ≤ (r : ℝ) ^ (1 - ε) ∧ r - d < d)
    (hj : log n * (1 - ε) ^ j ≤ log K) :
    practicalH n ≤ j + 1 := by
  sorry

/-- `L_x = lcm(1, …, x)`. -/
def lcmUpTo (x : ℕ) : ℕ := (Icc 1 x).lcm id

/-- **Open premise** (erdosproblems.com/18 thread, (1)): the divisors of `L_x` are dense at scale
`r^{1 − c/log x}` above `x`. -/
def LcmDivisorsDense : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∀ r : ℕ, x < r → r ≤ lcmUpTo x →
    ∃ d ∈ (lcmUpTo x).divisors,
      d ≤ r ∧ ((r - d : ℕ) : ℝ) ≤ (r : ℝ) ^ (1 - c / log x) ∧ r - d < d

/-- **Edge:** the premise answers Erdős #18(a) (formal-conjectures `erdos_18a`, here with our
`IsPractical`): `h(L_x) = O((log x)²) = O((log log L_x)²)`, via `practicalH_le_of_dense` with
`K = x`, `ε = c / log x`, `j ≍ (log x)²` (`log L_x = ψ(x) ~ x`).  Believed 90%. -/
theorem erdos18a_of_lcmDivisorsDense (h : LcmDivisorsDense) :
    ∃ C : ℝ, 0 < C ∧ ∃ᶠ m in atTop, IsPractical m ∧
      (practicalH m : ℝ) < (log (log m)) ^ C := by
  sorry

end LeanFormalizations.Practical

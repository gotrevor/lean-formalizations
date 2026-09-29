/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Champernowne's constant is transcendental (Mahler 1937), via Roth

`C₁₀ = 0.123456789101112…`, i.e. `∑ n / 10^{L(n)}`, where `L(n)` is the number of digits of
`1, 2, …, n` written in a row, so `n` occupies the digits ending at position `L(n)`.

## Route (phase 18)

Let `N = L(10^{k−1} − 1)` be the number of digits used by the `(k−1)`-digit numbers, and let
`a = 10^{k−1}`, `x = 10^{−k}`.  The `k`-digit block `a, a+1, a+2, …` is the start of
`∑_{j ≥ 0} (a + j) x^{j+1} = a x/(1−x) + x²/(1−x)²`, a rational with denominator dividing
`(10^k − 1)²`.  So `p_k/q_k := C_N + 10^{−N}·(that rational)`, with `C_N` the first `N` digits, has
`q_k ∣ 10^N (10^k − 1)²` and agrees with `C` until the `k`-digit block runs out, at digit about
`N + 9k·10^{k−1}`.  Numerically (`scripts/champernowne-approx.py`), `−log|C − p_k/q_k| / log q_k`
is `16.2, 15.0, 13.4` for `k = 2, 3, 4`, decreasing to Amou's irrationality measure `10` (1991).
Anything above `2 + δ` for infinitely many distinct `p_k/q_k` contradicts `Roth1955`.

Leaves: the tail identity (a finite geometric-arithmetic sum plus a tail bound), the denominator
bound, the error bound `|C − p_k/q_k| ≤ q_k^{−3}` (say) for `k ≥ 2`, and distinctness of the
`p_k/q_k`.  Note that Roth's set uses `r.den` in lowest terms, which is at most `q_k`, so the
bound only improves.  Normality of `C₁₀` belongs in `normal-numbers`.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.Diophantine
import LeanFormalizations.NumberTheory.Diophantine.StephanEdges

namespace LeanFormalizations.Champernowne

open LeanFormalizations.Literature

/-- Total number of decimal digits of `1, 2, …, n`. -/
def digitsUpTo (n : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 n, (Nat.digits 10 m).length

/-- **Champernowne's constant** `0.123456789101112…`: the integer `n` is written so that its
last digit is decimal place `digitsUpTo n`. -/
noncomputable def champernowne : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / 10 ^ digitsUpTo (n + 1)

/-- Sanity anchor for the definition: the first eleven digits are `12345678910`. -/
theorem champernowne_prefix :
    ⌊champernowne * 10 ^ 11⌋ = 12345678910 := by
  sorry

/-- Champernowne's constant is irrational (unconditional). -/
theorem irrational_champernowne : Irrational champernowne := by
  sorry

/-- **Mahler (1937)**: Champernowne's constant is transcendental, from Roth's theorem. -/
theorem transcendental_champernowne (hR : Roth1955) : Transcendental ℚ champernowne := by
  sorry

/-- The same, from Stephan's machine-checked Ridout theorem (`roth1955_of_stephan`). -/
theorem transcendental_champernowne_of_stephan (h : Stephan2026Ridout) :
    Transcendental ℚ champernowne :=
  transcendental_champernowne (Diophantine.roth1955_of_stephan h)

end LeanFormalizations.Champernowne

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Combinatorics.Polyomino.Klarner

/-!
# The polynomial correction to `A(n) ≈ λⁿ`, and why exact halving is not a route

`A(n) ≤ λⁿ` always (`count_le_klarner_pow`).  The conjecture `A(n) ~ C λⁿ / n` needs, as a
first step, a **polynomial** lower correction `A(n) ≥ c λⁿ / n^K` (`PolyLowerCorrection`).
The best unconditional bound is quasi-polynomial (`BuiQuasiPolyLower`, Bui arXiv:2211.14909),
and it comes from splitting along a spanning-tree edge at an *unbalanced* size
(`BuiSplitLemma`, some `ℓ ∈ [n/4, 3n/4]`).  The `log n` in the exponent is the cost of not
controlling `ℓ`.

## What was tried (Ren, 2026-10-05) and how it died

Idea: force the split to be **exact**.  `polyLower_of_doublingReverse` shows that
`A(2n) ≤ C n^K A(n)²` gives the polynomial correction, through a dyadic telescope whose
errors are summable.  But the converse is immediate (`doublingReverse_of_polyLower`), so
`polyLower_iff_doublingReverse`: **exact halving with polynomial loss is equivalent to the
conclusion.**  Every counting premise that feeds it (for example "unbalanced products
`A(ℓ) A(2n−ℓ)` are at most polynomially larger than `A(n)²`") is equivalent too, since it
follows from the conclusion by `A(m) ≤ λᵐ`.

The only non-circular way in is **structural**: show that at least a `1/poly(n)` fraction of
`2n`-cell polyominoes have a cut edge splitting them into two `n`-cell polyominoes.  Such a
polyomino is determined by its two halves, one cell in each and a direction, so there are at
most `4n²A(n)²` of them, and the fraction bound gives `DoublingReverse`.  The heuristic warning
is that this fraction is about `n^{-θ}` under the conjecture, so the premise is true but no
easier to *see* than `θ < ∞`.  Surgery that moves `j` cells from the larger piece to the smaller
loses about `λʲ` of information, which is exactly the ratio it is trying to control.  The
mirror problem for self-avoiding walks, where cutting is free and gluing is hard, is the
Hammersley–Welsh `e^{O(√n)}` gap, open since 1962.  Maze row: "exact-halving route to θ < ∞".

Note on `BuiRatioMonotone`: increasing ratios `A(n)/A(n−1)` mean `A(n)² ≤ A(n−1)A(n+1)`,
i.e. **log-convexity**, which is what `A(n) ~ Cλⁿ/n` predicts (`−log n` is convex).
-/

namespace LeanFormalizations.Polyomino

open Filter Topology Real

/-- `A(n) ≤ λⁿ`: supermultiplicativity makes `λ = sup A(n)^{1/n}`, and `klarner` is that
supremum.  Confidence 99%. -/
theorem count_le_klarner_pow (n : ℕ) : (count n : ℝ) ≤ klarner ^ n := by sorry

/-! ## Literature inputs -/

/-- **Bui**, arXiv:2211.14909, Theorem 1: `P(n) ≥ A n^{-T log₂ n} λⁿ` for every `n`. -/
def BuiQuasiPolyLower : Prop :=
  ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ n : ℕ, 1 ≤ n →
    A * (n : ℝ) ^ (-(T * logb 2 n)) * klarner ^ n ≤ count n

/-- **Bui**, arXiv:2211.14909, Lemma 2 (from his Proposition 1, after Barequet–Barequet):
every `n`-cell polyomino splits along a spanning-tree edge into pieces of `ℓ` and `n − ℓ`
cells with `(n−1)/4 ≤ ℓ ≤ (3n+1)/4`, so `P(n) ≤ n³ P(ℓ) P(n−ℓ)` for some such `ℓ`. -/
def BuiSplitLemma : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ ℓ : ℕ, ((n : ℝ) - 1) / 4 ≤ ℓ ∧ (ℓ : ℝ) ≤ (3 * n + 1) / 4 ∧ ℓ ≤ n ∧
    (count n : ℝ) ≤ (n : ℝ) ^ 3 * count ℓ * count (n - ℓ)

/-- Open: **`A(n)/A(n−1)` is increasing** (Bui's Conjecture 2; Barequet–Golomb–Klarner,
Problem 14.3.7), i.e. `A` is log-convex.  Bui derives `P(n) ≥ 3^{-18} n^{-9} λⁿ` from it
(his Theorem 2). -/
def BuiRatioMonotone : Prop :=
  ∀ n : ℕ, 2 ≤ n → (count n : ℝ) / count (n - 1) ≤ count (n + 1) / count n

/-! ## The polynomial correction and its exact-halving form -/

/-- Open: **the polynomial lower correction**, `A(n) ≥ c λⁿ / n^K`.  Implied by
`KlarnerAsymptotic`; stronger than `BuiQuasiPolyLower`. -/
def PolyLowerCorrection : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * klarner ^ n / (n : ℝ) ^ K ≤ count n

/-- Open: **exact halving with polynomial loss**, `A(2n) ≤ C n^K A(n)²`.  The constant is
needed: at `n = 1`, `A(2) = 2 > A(1)² = 1`. -/
def DoublingReverse : Prop :=
  ∃ C K : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    (count (2 * n) : ℝ) ≤ C * (n : ℝ) ^ K * (count n : ℝ) ^ 2

/-- Why `DoublingReverse` carries a constant: `A(2) ≤ A(1)²` is false. -/
theorem not_count_two_le_count_one_sq : ¬ (count 2 ≤ count 1 ^ 2) := by
  rw [count_two, count_one]; norm_num

/-- **Exact halving gives the polynomial correction.**  English proof: with `a_m = log A(m)`,
`a_{2m} ≤ 2a_m + K log m + log C`.  Iterating `k` times from `n` and dividing by `2^k n`,
`a_{2^k n}/(2^k n) ≤ a_n/n + (1/n) ∑_{j<k} 2^{-j-1} (K log n + K j log 2 + log C)
  ≤ a_n/n + (K log(2n) + log C)/n`.
The left side tends to `log λ` (`tendsto_klarner`), so `A(n) ≥ λⁿ / (C (2n)^K)` for every
`n ≥ 1`.  Confidence 95%. -/
theorem polyLower_of_doublingReverse (h : DoublingReverse) : PolyLowerCorrection := by sorry

/-- The converse, which is why exact halving is not a route: `A(2n) ≤ λ^{2n}
≤ (n^{2K}/c²) A(n)²`.  Confidence 99%. -/
theorem doublingReverse_of_polyLower (h : PolyLowerCorrection) : DoublingReverse := by sorry

/-- **Exact halving with polynomial loss is equivalent to the polynomial correction.** -/
theorem polyLower_iff_doublingReverse : PolyLowerCorrection ↔ DoublingReverse :=
  ⟨doublingReverse_of_polyLower, polyLower_of_doublingReverse⟩

end LeanFormalizations.Polyomino

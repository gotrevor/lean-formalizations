/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Buchstab

/-!
# The crux of phase E5: `S⁻(N, N^{1/2−ε}) ≫_ε N / log N`

`siftMin_lower` is the whole linear-sieve content; `LinearSieve.lean` derives the frozen statement
from it by bookkeeping alone.  Status: disclosed `sorry`, being decomposed (see `LinearSieve.lean`'s
header for the route).
-/

namespace LeanFormalizations.Erdos385.LinearSieve

/-- **The linear-sieve lower bound for the extremal count** (Jurkat–Richert, `s > 2`). -/
theorem siftMin_lower : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ z : ℕ, (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - ε) → c * N / Real.log N ≤ siftMin N z := by
  sorry

end LeanFormalizations.Erdos385.LinearSieve

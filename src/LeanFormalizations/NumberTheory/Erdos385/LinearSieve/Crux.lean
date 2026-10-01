/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Leaves
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.UpperAt
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Comparison

/-!
# The crux of phase E5: `S⁻(N, N^{1/2−ε}) ≫_ε N / log N`

`siftMin_lower` is the whole linear-sieve content; `LinearSieve.lean` derives the frozen statement
from it by bookkeeping alone.  Status: reduced to the named leaves of `LinearSieve/Leaves.lean` (see `LinearSieve.lean`'s
header for the route).
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Filter

/-- **The crux, normalised**: a positive lower constant at every level `s > 2`.
Route: `LinearSieve.lean` header, steps 2–5 (`a ≥ α = λ(sω − m/2)`, and on `(2,3]`
`sω − m/2 = 2 log(s−1) > 0`; note only `λ > 0` matters for the sign, with `λ = e^{C₃}/ω_∞`). -/
theorem lowerAt_pos : ∀ s : ℝ, 2 < s → ∃ c : ℝ, 0 < c ∧ LowerAt s c := fun s hs =>
  lower_of_aLow_pos (by linarith) (aLow_pos_of_leaves s hs)

/-- **The linear-sieve lower bound for the extremal count** (Jurkat–Richert, `s > 2`). -/
theorem siftMin_lower : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ z : ℕ, (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - ε) → c * N / Real.log N ≤ siftMin N z := by
  intro ε hε
  set e := min ε (1 / 4) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have hee : e ≤ ε := min_le_left _ _
  have he4 : e ≤ 1 / 4 := min_le_right _ _
  obtain ⟨c, hc, N₀, hN⟩ := lowerAt_pos (1 / (1 / 2 - e)) (by
    rw [lt_div_iff₀ (by linarith)]; linarith)
  refine ⟨c, hc, max N₀ 1, fun N hN1 z hz => hN N (le_trans (le_max_left _ _) hN1) z ?_⟩
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN1)
  rw [one_div_one_div]
  exact hz.trans (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))

end LeanFormalizations.Erdos385.LinearSieve

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Pisot

/-!
# Control for the `5/9` wall: decay alone admits Pisot degree 4

For `θ ∈ [5/9, 2/3)` the E+ route only knows decay `‖β^n‖ ≪ β^(−μ n)` with `μ < 2 − 3θ ≤ 1/3`
along the orbit.  This file records that decay of that strength, even at **every** `n`, is
consistent with Pisot degree 4, so `SaitoTypeBTheta.ShiftPisotDegreeLeThree` cannot follow from
the decay hypothesis plus Pisot-ness alone; it needs an input beyond decay (the prime structure,
or the orbit `n ↦ 3n − d` used arithmetically).
-/

namespace LeanFormalizations.Mills.DecayDegreeFour

open LeanFormalizations.Literature

/-- **Decay of strength `μ < 1/3` admits quartic Pisot numbers** (believed, ~90%).

English proof: take `β` the real root `> 1` of `X⁴ − aX³ − 1`, `a` large.  The polynomial is
irreducible over `ℚ` (no rational root; a quadratic factorisation forces constant terms `±1`,
contradicted by comparing coefficients for `a ≥ 3`).  The other three roots satisfy
`γ³(γ − a) = 1`, so `|γ| = (a + O(1))^(−1/3)` and all lie in the unit disc: `β` is Pisot of
degree 4, with `β = a + O(a^(−3))`.  Since `Σ_i γ_i^n ∈ ℤ` (Newton), `‖β^n‖ ≤ 3 R^n` with
`R = max |γ_i| ≤ (a − 2)^(−1/3)`, and `R ≤ β^(−μ)` once `a` is large for fixed `μ < 1/3`.
Control: at `μ > 1/3` the statement is false (product of the small conjugates is `1/β`, so
`R ≥ β^(−1/3)`; with the dominant-pair lower bound the decay forces degree ≤ 3), matching the
proved `θ < 5/9` side. -/
theorem decay_admits_degree_four {μ : ℝ} (hμ : μ < 1 / 3) :
    ∃ β : ℝ, IsPisot β ∧ (minpoly ℚ β).natDegree = 4 ∧
      ∀ n : ℕ, 1 ≤ n → |β ^ n - round (β ^ n)| ≤ 3 * β ^ (-(μ * n)) := by
  sorry

end LeanFormalizations.Mills.DecayDegreeFour

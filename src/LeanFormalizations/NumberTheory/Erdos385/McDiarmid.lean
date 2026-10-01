/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional

/-!
# McDiarmid's inequality on a finite product (phase E4b)

One frozen statement, `mcDiarmidFinite_holds : McDiarmidFinite`.  It removes one of the three
literature inputs of the E4 exceptional-set bound (`Exceptional.lean`).

## Route (85%): exponential moment by induction over coordinates, then Chernoff

Everything is a finite average, so avoid filtrations; work with `Finset` sums over `∀ i, α i`.

1. **Hoeffding's lemma, finite form.**  For a function `Z` on a finite nonempty set with uniform
   weights, values in an interval of length `c`, and `λ : ℝ`:
   `avg exp(λ (Z − avg Z)) ≤ exp(λ² c² / 8)`.  Mathlib has it for measures as
   `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (`Mathlib/Probability/Moments/SubGaussian.lean`);
   instantiate with `PMF.uniformOfFintype`/`uniformOn`, or prove directly (convexity of `exp` plus
   the standard `log cosh`-type bound `p e^{λ(1−p)c} + (1−p) e^{−λpc} ≤ e^{λ²c²/8}`).
2. **Averaging out one coordinate at a time.**  For a finset `s ⊆ ι`, let `f_s(x)` be the average of
   `f` over the coordinates in `s` (others fixed).  `f_∅ = f`, `f_univ = avg f`.  For `i ∉ s`,
   `f_s − f_{s ∪ {i}}`, as a function of `x_i` with the rest fixed, has average `0` and range in an
   interval of length `≤ c i` (bounded differences survive averaging).  So
   `avg exp(λ(f_s − f_univ)) ≤ exp(λ² c_i² / 8) · avg exp(λ(f_{s∪{i}} − f_univ))` (Fubini over the
   product split `x_i` vs the rest; `Fintype.piFinset`/`Equiv.piSplitAt` help).
   Induction: `avg exp(λ(f − avg f)) ≤ exp(λ² Σ c_i² / 8)`.
3. **Chernoff** for the lower tail with `−λ`: `#{f ≤ avg f − t} ≤ card · exp(−λt + λ² Σc²/8)`;
   take `λ = 4t / Σc²` (if `Σc² = 0`, the inequality is trivial: `f` is constant, the set is empty
   since `t > 0`).

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: this statement and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **McDiarmid's inequality**, proved. -/
theorem mcDiarmidFinite_holds : McDiarmidFinite := by
  sorry

end LeanFormalizations.Erdos385

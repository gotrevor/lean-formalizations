/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.Endpoint

/-!
# Erdős #463 for almost all `n` (phase E6, new mathematics)

#463 (formal-conjectures `ErdosProblems/463.lean`) asks for `f → ∞` such that for all large `n` some
composite `m` has `n + f(n) < m < n + p(m)`, `p(m) = minFac m`.  It is the upward mirror of #385 and
meets the same parity obstruction for all `n`.  The frozen statement here, `almost_all_erdos463`,
proves it for almost all `n` with the large margin `f(n) = δ√n`, assuming only Richert's bound (the
same base as `Endpoint.lean`).

## Route (70%): E3 with the witness window shifted above `n`

E3's W2 (`card_badWindow_le`) bounds the `n` whose window `[n − h, n − 1]` (`h = paramH δ Z`)
contains no `m` with `coeffA δ g Z m ≠ 0`; its proof only uses that the window is an `h`-interval
inside `[Z, (1+δ/2) Z]`-ish where the variance bound holds.  Mirror it:
1. **W1↑.**  If `m ∈ [n + ⌈δ√n⌉ + 1, n + ⌈δ√n⌉ + h]` and `coeffA δ g Z m ≠ 0`, then `m = p q` with
   `p ∈ [(1−δ/2)√Z, (1−δ/4)√Z]`, `q ≥ √Z > p`, so `minFac m = p`, `m` is composite, and
   `m − n ≤ δ√n + δ√Z/4 + 2 < (1 − δ/2)√Z ≤ p` (as `δ < 1/4`; compare `witness_margin`).
2. **W2↑.**  Copy `card_badWindow_le` for the shifted window (the `x`-range moves by `≍ δ√Z`, which
   is `o(Z)`, so the variance integral over `[X, 2X]` still covers it; enlarge the range slightly if
   needed).
3. **Assemble** as in `almost_all_F385` / `tendsto_density_zero_of_windows`, feeding the proved
   inputs (`mr16Lemma14_holds`, `montgomeryVaughanMVT_holds`, `mediumPNTStatement_holds`,
   `vkZeroFreeLogDeriv_of_richert h`).

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: this statement, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Filter LeanFormalizations.Literature

/-- **Erdős #463 for almost all `n`**, with margin `δ√n`: the `n ≤ X` having no composite `m` with
`n + δ√n < m < n + minFac m` are `o(X)`. -/
theorem almost_all_erdos463 (h : RichertZetaGrowth) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    Tendsto (fun X : ℕ => ({n : ℕ | n ≤ X ∧ ¬ ∃ m : ℕ, Composite m ∧
        (n : ℝ) + δ * Real.sqrt n < m ∧ m < n + m.minFac}.ncard : ℝ) / X) atTop (nhds 0) := by
  sorry

end LeanFormalizations.Erdos385

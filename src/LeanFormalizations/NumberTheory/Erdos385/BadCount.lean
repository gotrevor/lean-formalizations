/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.ExceptionalWeak
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve

/-!
# Erdős #385: the bad set is exponentially thin, unconditionally

`#{n ≤ X : n bad} ≪_ε X exp(−(log X)^{1/2−ε})` for every `ε ∈ (0, 1/2)`, where `n` is bad iff
`F(n) ≤ n` (equivalently, #430 fails at `n`; `Rigidity.erdos430_iff_erdos385_i`).

Chain: `Exceptional.lean` (forbidden classes + large sieve + McDiarmid tail, `DOOR-EXCEPTIONAL` A2),
with the weak-constant large sieve (`LargeSieve.lean`, Gallagher + Montgomery), McDiarmid
(`McDiarmid.lean`) and the Jurkat–Richert linear-sieve lower bound (`LinearSieve.lean`) all proved.
-/

namespace LeanFormalizations.Erdos385

/-- **The bad set of Erdős #385 is exponentially thin**, with no hypotheses. -/
theorem badCountExpBound_holds : BadCountExpBound :=
  badCountExpBound_of_linearSieve linearSieveIntervalLower_holds

end LeanFormalizations.Erdos385

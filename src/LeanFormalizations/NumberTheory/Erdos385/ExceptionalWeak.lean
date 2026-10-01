/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Exceptional
import LeanFormalizations.NumberTheory.Erdos385.LargeSieve
import LeanFormalizations.NumberTheory.Erdos385.McDiarmid

/-!
# Erdős #385: the exceptional-set bound from the linear sieve alone (phase E4d)

Two frozen statements:
* `badCountExpBound_of_weak : ArithLargeSieveWeak → LinearSieveIntervalLower → BadCountExpBound`;
* `badCountExpBound_of_linearSieve : LinearSieveIntervalLower → BadCountExpBound` (one line from the
  first, `arithLargeSieveWeak_holds` (`LargeSieve.lean`) and nothing else).

## Route (90%)

E4's proof (`Exceptional/`) uses the sharp `ArithLargeSieve` only through `sieve_count`
(`Exceptional/Sieve.lean`), and through it `bad_count_le` and `eventually_bad_le`.  Add
constant-carrying copies `sieve_count_weak`, `bad_count_le_weak`, `eventually_bad_le_weak` taking
`ArithLargeSieveWeak` (constant `C`): the sieved term gains a factor `C`, which the final bound
absorbs because the large-sieve saving `L ≥ exp((log X)^{1/2})` beats any constant.  Feed
`mcDiarmidFinite_holds` for McDiarmid.  Do not edit E4's frozen statements; copy and generalise.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **The bad set is exponentially thin**, with the weak-constant large sieve. -/
theorem badCountExpBound_of_weak (h1 : ArithLargeSieveWeak) (h2 : LinearSieveIntervalLower) :
    BadCountExpBound := by
  sorry

/-- **The bad set is exponentially thin, assuming only the linear-sieve lower bound.** -/
theorem badCountExpBound_of_linearSieve (h : LinearSieveIntervalLower) : BadCountExpBound := by
  sorry

end LeanFormalizations.Erdos385

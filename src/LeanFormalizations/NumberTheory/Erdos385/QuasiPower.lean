/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.BadCount
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.ClassCount
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Esymm
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Window
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.MertensSums
import LeanFormalizations.NumberTheory.Erdos385.QuasiPower.Params

/-!
# Erdős #385: pushing the bad-`n` bound toward the framework ceiling (phase E8, moonshot)

`BadCount.badCountExpBound_holds` proves `#{bad n ≤ X} ≪_ε X exp(−(log X)^{1/2−ε})`
unconditionally (`Exceptional.lean` route, `DOOR-EXCEPTIONAL-ERDOS-385.md` §A2).  §A2 "What blocks"
names two bottlenecks and a ceiling `X^{1−o(1)}` (`L ≤ X^{o(1)}`).  This phase attacks both
bottlenecks.  Two frozen targets:

* `badCountExp_threeQuarters` (milestone, 35%): exponent `3/4 − ε`;
* `badCountQuasiPower_holds` (moonshot, 20%): `X exp(−c log X/(log log X)²)`, i.e. a saving
  `X^{o(1)}` that is a power of `log` away from the ceiling.

A lap that finds a gap has made progress: name the failing step as a sub-lemma, record why it fails
(a `¬` statement or a counterexample if the step is false), and say which weaker exponent survives.

## Route

Keep the dyadic block, `y ≍ log X`, `Q = X^{1/3}`, `s = n mod primorial y`, `U(s)` and the
forbidden-class step exactly as in `Exceptional.lean` (reuse `Exceptional/*`, `ExceptionalWeak/*`;
the weak large sieve `LSWith` suffices).  Change two steps.

1. **Large sieve with many primes** (step 2).  Take `d` = products of `j` distinct primes of
   `pool y R`, `R = ⌊Q^{1/j}⌋`, with `j ≍ (log X)^{θ}` (milestone `θ = 3/4`) or
   `j ≍ log X/(log log X)²` (moonshot), and `K ≍ y/log y` classes per prime.  `Exceptional/Analytic`
   (`pool_weight_ge`, `rho_bound`, `eventually_L_conditions`) is written for `j ≍ (log X)^{1/2}`;
   generalize it.  Need `R > y`, i.e. `j log y < (1/3) log X`; Mertens gives
   `Σ_{p ∈ pool} 1/p ≥ log(log R/log y) − O(1)`, and `L ≥ (K Σ 1/p/(e j))^j` once `K Σ 1/p ≥ e² j`.
   At the moonshot `j`, `K/j ≍ log log X` and `L ≥ exp(c log X · log log log X/(log log X)²)`.
2. **Tail of `u(s)` beyond McDiarmid** (step 3), the crux.  McDiarmid charges the worst-case
   influence `y/q` of a prime `q` near `z = y^{1/2}`, so the tail is `exp(−c y^{1/2−ε})`; to beat
   `1/2` the tail must be `≤ exp(−y^{θ})`.  Plan: a Bernstein/Freedman martingale over the primes
   `q ∈ (z, y]` revealed in increasing order, with the increment at `q` = the number of surviving
   positions in the class `s mod q`.  Its conditional variance is `≤ (max class count)·|U|/q`, and
   on a **good event** where the survivors are equidistributed mod each `q` (class counts
   `≤ 2|U|/q + y^{1/4}`), the increments are `≤ 2y/(q log y) + y^{1/4}`.  Freedman then gives
   `exp(−c y^{3/4}/log y)` for the deviation `≍ y/log y`, provided the good event fails with
   probability `≤ exp(−y^{3/4})`.  The good event is itself a tail bound for sifted counts in
   progressions of length `y/q` (a smaller copy of the same problem: recurse, or bound it with the
   fundamental lemma plus McDiarmid on the primes `≤ q`).  For the moonshot, iterate scales.
   Finite-average Freedman/Bernstein is not in mathlib: prove it as a named theorem by the same
   finite-average induction as `McDiarmid/Core.lean` (Bernstein's mgf lemma
   `E e^{λD} ≤ exp(λ² v (e^{λb} − 1 − λb)/(λb)²)` in place of Hoeffding's lemma).
3. **Sum** as in `Exceptional/Main`, `Terms`.

Sub-lemmas worth naming early: `freedmanFinite` (2), `goodEvent_tail` (2), `pool_weight_ge_general`
(1).  If `goodEvent_tail` is false at the claimed strength, record the counterexample and the
exponent it permits.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

/-- Milestone: the bad set has size `≪_ε X exp(−(log X)^{3/4−ε})`. -/
def BadCountExpThreeQuarters : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 3 / 4 → ∃ C : ℝ, ∀ X : ℕ, 3 ≤ X →
    ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ)
      ≤ C * X * Real.exp (-(Real.log X) ^ ((3 : ℝ) / 4 - ε))

/-- Moonshot: the bad set has size `≪ X exp(−c log X/(log log X)²)`. -/
def BadCountQuasiPower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℕ, 16 ≤ X →
    ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ Bad n}.ncard : ℝ)
      ≤ C * X * Real.exp (-(c * Real.log X / Real.log (Real.log X) ^ 2))

theorem badCountExp_threeQuarters : BadCountExpThreeQuarters := by
  sorry

theorem badCountQuasiPower_holds : BadCountQuasiPower := by
  sorry

end LeanFormalizations.Erdos385

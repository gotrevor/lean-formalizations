/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Consequences of the known exponentials theorems (phase 17, queued)

The six exponentials theorem is **unconditional**, so everything here is a real theorem, modulo
cited literature.

* **`2^t, 3^t, 5^t`** (Trevor, 2026-09-29): for irrational `t`, one of them is transcendental.
  Take `x = (1, t)` and `y = (log 2, log 3, log 5)`, with independence from
  `linearIndependent_log_primes`; the exponentials are `2, 3, 5, 2^t, 3^t, 5^t`.  Any three
  distinct primes work.  `4` does not help, since `log 4 = 2 log 2`.  This is the unconditional
  cousin of phase 16's `two_rpow_or_three_rpow_transcendental`, which needs four exponentials.
* **Consistency edges**: `SixExponentialsShifted ⇒ SixExponentials` and
  `SixExponentialsShifted ⇒ FiveExponentials` (Waldschmidt says it covers both), and
  `StrongSixExponentials ⇒ SixExponentials` (if every `e^{xᵢyⱼ}` were algebraic, every `xᵢyⱼ`
  would be a logarithm, hence in `LogAlgSpan`).
* **Five exponentials ⇒** `e^{π²}` or `2^{√2}`-style corollaries: left to the lap to choose one
  (Waldschmidt 2023 §6 lists them); add as a new theorem.

Frozen: the statements below, every earlier name, all of `Literature/`.
-/
import LeanFormalizations.Literature.ExponentialsKnown
import LeanFormalizations.Literature.Exponentials
import LeanFormalizations.NumberTheory.Transcendence.Schanuel

namespace LeanFormalizations.ExponentialsKnown

open LeanFormalizations.Literature

/-- **Unconditional** (six exponentials): for irrational `t`, one of `2^t, 3^t, 5^t` is
transcendental. -/
theorem two_three_five_rpow_transcendental (h6 : SixExponentials) {t : ℝ} (ht : Irrational t) :
    Transcendental ℚ ((2 : ℝ) ^ t) ∨ Transcendental ℚ ((3 : ℝ) ^ t) ∨
      Transcendental ℚ ((5 : ℝ) ^ t) := by
  sorry

theorem sixExponentials_of_shifted (h : SixExponentialsShifted) : SixExponentials := by
  sorry

theorem fiveExponentials_of_shifted (h : SixExponentialsShifted) : FiveExponentials := by
  sorry

theorem sixExponentials_of_strong (h : StrongSixExponentials) : SixExponentials := by
  sorry

end LeanFormalizations.ExponentialsKnown

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385AlmostAll
import LeanFormalizations.NumberTheory.Erdos385.Count
import LeanFormalizations.NumberTheory.Erdos385.BrunPairs

/-!
# Erdős #385: discharging literature Props (phase E2c)

Three frozen statements.  Each removes one hypothesis from a downstream theorem.

1. `card_bad_le_unconditional`: `Count.card_bad_le` applied to `Erdos385.brunUniformGap_holds`
   (`BrunPairs.lean`).  One line.

2. `mediumPNTStatement_holds : MediumPNTStatement`.  `Literature.MediumPNTStatement` is PNT+
   `MediumPNT` verbatim (PrimeNumberTheoremAnd, `PrimeNumberTheoremAnd/MediumPNT.lean`, at the rev
   pinned in `lakefile.toml`).  Route: add `import PrimeNumberTheoremAnd.MediumPNT` here (its
   first build is long; that is expected), then `exact MediumPNT`, bridging `ψ` if PNT+'s
   `ChebyshevPsi` and mathlib's `Chebyshev.psi` (`open scoped Chebyshev`) differ syntactically.
   Check `#print axioms` stays `[propext, Classical.choice, Quot.sound]`: the MediumPNT import
   chain (MellinCalculus, ZetaBounds, ZetaConj, SmoothExistence) greps clean of `sorry` at this
   pin, but the kernel is the judge.  If a transitive `sorryAx` shows up, keep the theorem, leave
   it `sorry`, and write which PNT+ declaration carries it.

3. `montgomeryVaughanMVT_holds : MontgomeryVaughanMVT`, the mean value theorem
   `∫_{-T}^{T} |Σ_{n ≤ N} a_n n^{-it}|² dt ≤ C (T + N) Σ |a_n|²`.  Elementary route, no Fourier
   library (85% it closes as stated):
   * Majorant: on `|t| ≤ T`, `1 ≤ 2 (1 − |t|/(2T))`, so the left side is at most
     `2 ∫_{-2T}^{2T} (1 − |t|/(2T)) |S(t)|² dt` (`S(t) = Σ a_n n^{-it}`).
   * Expand `|S|² = Σ_{m,n} a_m conj(a_n) (n/m)^{it}`; the Fejér integral is explicit:
     `∫_{-2T}^{2T} (1 − |t|/(2T)) e^{iλt} dt = (1 − cos(2Tλ)) / (Tλ²)` for `λ ≠ 0` (`= 2T` at
     `λ = 0`), real, nonnegative, and `≤ min(2T, 2/(Tλ²))`.
   * Schur / `|a_m a_n| ≤ (|a_m|² + |a_n|²)/2`: it suffices that for each `m ≤ N`,
     `Σ_{n ≤ N} min(2T, 2/(T λ_{mn}²)) ≤ C' (T + N)` with `λ_{mn} = log(n/m)`.
   * `|log(n/m)| ≥ |n − m| / N` for `1 ≤ m, n ≤ N`.  Split `k = |n − m|`: for `k ≤ N/T` each
     term is `≤ 2T`, total `≤ 2T(2N/T + 1)`; for `k > N/T`, `Σ 2N²/(T k²) ≤ 4N²/(T · N/T) = 4N`.
     So the row sum is `≤ 2T + 8N + …`, i.e. `O(T + N)`.
   The positivity of the Fejér transform is what makes the weighted expansion an upper bound for
   the absolute values; the sharp cutoff `1_{[-T,T]}` alone gives only `T + N log N`.
   If the bookkeeping stalls, leave a NAMED sub-lemma with a disclosed hole plus an English
   paragraph and a confidence; that is an acceptable finish.

Frozen: these three statements, and everything in `Literature/` (do not edit any Prop).
-/

namespace Erdos385

open Real Finset Filter Asymptotics LeanFormalizations.Literature

/-- **Unconditional bad-`n` count**: `#{bad n ≤ X} ≪ X log log X / log² X`. -/
theorem card_bad_le_unconditional :
    ∃ C : ℝ, ∀ X : ℕ, 16 ≤ X →
      ({n : ℕ | n ≤ X ∧ 5 ≤ n ∧ LeanFormalizations.Erdos385.Bad n}.ncard : ℝ)
        ≤ C * X * Real.log (Real.log X) / Real.log X ^ 2 := by
  sorry

/-- PNT+ `MediumPNT` discharges `Literature.MediumPNTStatement`. -/
theorem mediumPNTStatement_holds : MediumPNTStatement := by
  sorry

/-- The Montgomery–Vaughan mean value theorem (upper half, unspecified constant). -/
theorem montgomeryVaughanMVT_holds : MontgomeryVaughanMVT := by
  sorry

end Erdos385

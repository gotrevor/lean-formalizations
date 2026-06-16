/-
# `(π : ℂ)` is algebraic over `ℚ` whenever real `π` is (the iπ-conjugate input)

A small transport helper used by the π-Lindemann assembly (`MonicRootSums.lean`,
`transcendental_pi_of_subsetSumEsymm`). It lifts algebraicity of `π` along the tower
`ℚ → ℝ → ℂ`, the first step in showing `iπ` is algebraic.

**History.** This file formerly cited Hermite–Lindemann (`axiom hermite_lindemann`) and
derived a conditional `transcendental_pi` from it. That axiom is now **fully discharged**:
`Transcendence.transcendental_pi_axiomClean` (in `PiTranscendental.lean`) proves
`Transcendental ℚ Real.pi` from first principles — analytic part (`exp_polynomial_approx`
assembly) + the algebraic part (symmetric functions over the Galois conjugates of `iπ`,
`SubsetSumEsymm.subsetSum_esymm_rational`). The axiom and its dependent theorem have been
deleted; the repo carries **no math axiom**.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.RingTheory.Algebraic.Integral

open Complex

namespace LeanFormalizations.Transcendence

/-- `(π : ℂ)` is algebraic over `ℚ` whenever the real `π` is — transport along the
tower `ℚ → ℝ → ℂ`. -/
theorem isAlgebraic_pi_complex_of_real (hpi : IsAlgebraic ℚ Real.pi) :
    IsAlgebraic ℚ (Real.pi : ℂ) := by
  have h := hpi.algebraMap (A := ℂ)
  simpa using h

end LeanFormalizations.Transcendence

/-
# Hermite–Lindemann ⟹ transcendence of `π` (the squaring-the-circle input)

mathlib (v4.29.1) provides only the **analytic** part of the Lindemann–Weierstrass
theorem (`LindemannWeierstrass.exp_polynomial_approx`,
`Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`), not the
transcendence conclusion. To make `squaring_the_circle_impossible` *unconditional*
we cite **Hermite–Lindemann** (a.k.a. Lindemann's theorem, 1882) as a single
disclosed `axiom` and **machine-check the reduction** `Transcendental ℚ Real.pi`
from it.

This is a genuine *narrowing*, not an assertion of the conclusion:

* the cited axiom `hermite_lindemann` is strictly **more general** than
  π-transcendence (it also yields the transcendence of `e`, of `log 2`, of
  `cos 1`, …); and
* the contrapositive Euler-identity argument — `π` algebraic ⟹ `iπ` algebraic ⟹
  `exp (iπ)` transcendental, contradicting `exp (iπ) = -1` — is **fully verified
  by the kernel** (`#print axioms transcendental_pi` shows the trust base plus the
  one cited axiom, nothing more).

Discharging `hermite_lindemann` itself is the genuine multi-year wall: the
"algebraic part" of Lindemann–Weierstrass (symmetric functions over the Galois
conjugates of the algebraic exponents, forcing a nonzero integer of absolute value
`< 1` against the analytic bound). The accessible entry point — transcendence of
`e` from `exp_polynomial_approx`, no symmetric functions needed — is tracked
separately in `PENDING_WORK.md`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.RingTheory.Algebraic.Integral

open Complex

namespace LeanFormalizations.Transcendence

/-- **Hermite–Lindemann theorem** (Lindemann, 1882), cited as a single disclosed
`axiom`. If `α` is a nonzero algebraic number over `ℚ`, then `exp α` is
transcendental over `ℚ`.

This is the `n = 1` case of the Lindemann–Weierstrass theorem (linear independence
of `exp` at distinct algebraic exponents). mathlib has only the analytic part
(`LindemannWeierstrass.exp_polynomial_approx`); the algebraic-part assembly is not
yet formalized, so we cite this one statement and derive everything we need from
it with machine-checked proofs.

The `α = 1` (real) instance is *independently discharged* in `ETranscendental.lean`
(`e_transcendental`, axiom-clean). **Replacement path:** mathlib PR #28013
("feat: Lindemann-Weierstrass Theorem") proves `transcendental_exp`
(`a ≠ 0 → IsAlgebraic ℤ a → Transcendental ℤ (Complex.exp a)`), i.e. this statement
over `ℤ`. On a mathlib bump past its merge, delete this axiom, import
`Mathlib.NumberTheory.Transcendental.Lindemann.Basic`, and bridge ℤ↔ℚ via
`isAlgebraic_algebraMap_iff` / `transcendental_algebraMap_iff`. See
`archive/findings/ON-LINE-FINDINGS-2026-06-15-pi-transcendence.md`. -/
axiom hermite_lindemann {α : ℂ} (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) :
    Transcendental ℚ (Complex.exp α)

/-- `(π : ℂ)` is algebraic over `ℚ` whenever the real `π` is — transport along the
tower `ℚ → ℝ → ℂ`. -/
theorem isAlgebraic_pi_complex_of_real (hpi : IsAlgebraic ℚ Real.pi) :
    IsAlgebraic ℚ (Real.pi : ℂ) := by
  have h := hpi.algebraMap (A := ℂ)
  simpa using h

/-- **Transcendence of `π`** over `ℚ`, derived from `hermite_lindemann` via the
Euler identity `exp (π·i) = -1`.

Suppose `π` were algebraic. Then so is `i·π` (a product of algebraic numbers,
`i` being a root of `X² + 1`), and `i·π ≠ 0`, so by Hermite–Lindemann `exp (i·π)`
would be transcendental. But `exp (i·π) = -1` is rational, a contradiction. -/
theorem transcendental_pi : Transcendental ℚ Real.pi := by
  intro hpi
  -- lift `π` to `ℂ`
  have hpiC : IsAlgebraic ℚ (Real.pi : ℂ) := isAlgebraic_pi_complex_of_real hpi
  -- `i` is algebraic over `ℚ`
  have hI : IsAlgebraic ℚ (Complex.I) := isAlgebraic_iff_isIntegral.mpr isIntegral_rat_I
  -- the product `i·π` is algebraic over `ℚ`
  have hIpi : IsAlgebraic ℚ (Complex.I * (Real.pi : ℂ)) := by
    rw [isAlgebraic_iff_isIntegral] at hI hpiC ⊢
    exact hI.mul hpiC
  -- and nonzero
  have hne : Complex.I * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  -- Hermite–Lindemann ⟹ `exp (i·π)` is transcendental
  have htr : Transcendental ℚ (Complex.exp (Complex.I * (Real.pi : ℂ))) :=
    hermite_lindemann hIpi hne
  -- but `exp (i·π) = -1` is algebraic — contradiction
  apply htr
  rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
  simpa using isAlgebraic_int (R := ℚ) (A := ℂ) (-1)

end LeanFormalizations.Transcendence

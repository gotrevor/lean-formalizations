/-
# Toward the sharp Mertens constant `C₃ = −γ`

`Mertens.lean` proves `∏_{p≤N}(1−1/p)·log N → e^{C₃}` (`mertens_third_tendsto_exp`) with
`C₃ = mertensThirdConst`, and reduces the classical `e^{−γ}` headline to the single deep equation
`mertensThirdConst = −γ` (`mertens_third_classical`).  This file collects the first **provable**
scaffolding bricks toward that equation, via the real prime-zeta function and mathlib's complex ζ
Euler product.

**The classical route** (still multi-lap): for `s > 1`,
`log ζ(s) = ∑_p ∑_{k≥1} p^{−ks}/k = P(s) + ∑_{k≥2} P(ks)/k` where `P(s) = ∑_p p^{−s}` is the prime
zeta; as `s → 1⁺`, `ζ(s) − 1/(s−1) → γ` (`tendsto_riemannZeta_sub_one_div`) gives the `γ`, and an
Abel/Tauberian transfer connects `P(s)` to the partial sums `∑_{p≤x} 1/p = log log x + M + o(1)`
(`mertens_second_tendsto`), yielding `M = γ + ∑'_p (log(1−1/p)+1/p)`, i.e. `C₃ = −γ`.

This file currently establishes: the real prime zeta `primeZeta` is well-defined (summable for `s>1`)
and the real specialisation of mathlib's `riemannZeta_eulerProduct_exp_log`.  Both are axiom-clean.
-/
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Mertens
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace LeanFormalizations.Mertens

open Filter Topology

/-- **Real prime zeta** `P(s) = ∑'_{p prime} p^{−s}` (the Dirichlet series over primes). -/
noncomputable def primeZeta (s : ℝ) : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-s)

/-- The prime-zeta summand is summable for `s > 1` — a subseries of the convergent `p`-series
`∑_n n^{−s}` (`s > 1 ⇒ −s < −1`), restricted along the injection `Nat.Primes ↪ ℕ`. -/
lemma summable_primeZeta_term {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s)) := by
  have hN : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  exact hN.comp_injective Nat.Primes.coe_nat_injective

/-- The prime zeta is nonnegative. -/
lemma primeZeta_nonneg {s : ℝ} : 0 ≤ primeZeta s := by
  apply tsum_nonneg
  intro p
  positivity

/-- **Real specialisation of the ζ Euler product** (`riemannZeta_eulerProduct_exp_log`): for real
`s > 1`, `exp(∑'_p −log(1 − p^{−s})) = ζ(s)` in `ℂ`.  The starting point for taking real logarithms and
extracting the prime zeta. -/
lemma riemannZeta_eulerProduct_ofReal {s : ℝ} (hs : 1 < s) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))) = riemannZeta (s : ℂ) := by
  apply riemannZeta_eulerProduct_exp_log
  simpa using hs

end LeanFormalizations.Mertens

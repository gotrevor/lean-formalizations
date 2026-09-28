/-
# Dubickas (2022), monic quadratics, without Lemma 6 (phase 9 probe)

After phase 8, Theorem 1 (`Dubickas.lean`) rests on `Dubickas2022` alone: Dubickas's Lemma 6,
from Corvaja–Zannier's `p`-adic subspace theorem.  It is consumed exactly once, in
`exists_pisot_pow` (`DubickasPisot.lean`), with `q = 2` and `s_k = 2^k`, to get some `α^(2^m)`
Pisot.  Here we need only a narrow special case, and we have more structure than Lemma 6 assumes:

* the approximation is **reciprocal-rate**: `|2α^(2ⁿ) − k_n| ≤ 2C α^(−2ⁿ)` with `k_n = 2y_n ∈ ℤ`;
* the integers come from an **exact recursion** `y_{n+1} = y_n² − c`, so
  `δ_{n+1} = δ_n (4α^(2ⁿ) − δ_n)/2 + 2c` for `δ_n := 2α^(2ⁿ) − k_n`.  That is an identity in
  `ℚ(α)`, so it holds for every embedding `σ` too.

Target: `exists_pisot_pow_noD`, the same conclusion as `exists_pisot_pow` without `hD`.  Any
route that gets `c ∈ {0, 2}` directly without `hD` is equally good: prove `c_eq_zero_or_two_uncond`
instead and leave the Pisot lemma as a `sorry`d side leaf.

## Leads (Ren, 2026-09-28; unverified, may be wrong)

* A plain Liouville/norm bound on `δ_n` (`D^(d 2ⁿ) N(δ_n) ∈ ℤ ∖ {0}`) does NOT close it by
  itself: both sides are `exp(Θ(2ⁿ))`.  Work out whether the conjugate recursion for `σ(δ_n)`
  improves the upper bound on `|N(δ_n)|` enough.
* `α^(2ⁿ) = Φ(y_n)`, where `Φ(z) = z ∏_{k≥0} (1 − c / f^k(z)²)^(1/2^(k+1))` is the Böttcher
  coordinate of `f(z) = z² − c` at `∞`, with `Φ ∘ f = Φ²`.  That is a Mahler-type functional
  equation; Mahler's method is where to look for an elementary (subspace-free) transcendence
  argument at rational points `y_0`.
* This case may genuinely need subspace-theorem strength.  Dubickas's own paper reaches for
  Corvaja–Zannier, which is evidence that it does.

A written obstruction in `PROBE-DUBICKAS-NOSUBSPACE.md` is a valid outcome: say which step needs
what strength, and name the smallest literature statement that would close it.
-/
import LeanFormalizations.NumberTheory.Transcendence.DubickasPisot

namespace LeanFormalizations.Transcendence.Dubickas

open Filter Topology LeanFormalizations.Literature LeanFormalizations.Mills

/-- **`exists_pisot_pow` without Lemma 6**, for the growth constant of an exact quadratic
recursion: some `α^(2^m)` is a Pisot number. -/
theorem exists_pisot_pow_noD
    {c α : ℝ} {y : ℕ → ℝ} (hrec : ∀ n, y (n + 1) = y n ^ 2 - c)
    (halg : IsAlgebraic ℚ α) (hα : 1 < α) {C : ℝ} (hC : 0 < C) {n₀ : ℕ}
    (hyint : ∀ n, ∃ k : ℤ, 2 * y n = (k : ℝ))
    (hbnd : ∀ n ≥ n₀, |y n - α ^ 2 ^ n| ≤ C / α ^ 2 ^ n) :
    ∃ m : ℕ, IsPisot (α ^ 2 ^ m) := by
  sorry

end LeanFormalizations.Transcendence.Dubickas

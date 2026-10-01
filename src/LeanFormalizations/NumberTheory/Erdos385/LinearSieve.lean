/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional

/-!
# The linear-sieve lower bound on an interval (phase E5)

One frozen statement, `linearSieveIntervalLower_holds : LinearSieveIntervalLower`: for `ε > 0`, an
interval `(Y/2, Y]` with one excluded class per prime `q ≤ Y^{1/2−ε}` keeps `≥ c Y/log Y` points.
With E4d this makes the exceptional-set bound `#{bad n ≤ X} ≪ X exp(−(log X)^{1/2−ε})`
unconditional.

The content is the Jurkat–Richert theorem in the one case we need: sieve dimension 1, remainders
`|r_d| ≤ 1` (an interval, one class per prime), sieving level `s = log D / log z > 2` where
`f(s) = 2e^γ log(s−1)/s > 0`.  The slack is `s − 2 ≍ ε`, so every constant must be asymptotically
sharp: a crude bound that loses a constant factor in `F` makes the lower bound negative.

## Route (35% within budget; a NAMED partial result is progress)

Sources: Halberstam–Richert, *Sieve Methods*, the linear-sieve chapter (Jurkat–Richert's method);
Friedlander–Iwaniec, *Opera de Cribro*, the linear-sieve chapters (β-sieve with `β = 2`).
⚠️ Chapter/theorem numbers not re-opened; read the method, not a citation.

1. **Selberg's upper bound, sharp for `s ≤ 2`.**  `S(A_d, w) ≤ X ω(d)/d / G_w(√(D/d)) + Σ_{e ≤ D/d}
   |r|` with `G_w(x) = Σ_{e ≤ x, e ∣ P(w)} μ²(e)/φ(e)` (one class per prime: `g(p) = 1/p`).  When
   `x ≤ w`, `G_w(x) = Σ_{e ≤ x} μ²(e)/φ(e) ≥ log x` (classical, elementary).  Mathlib:
   `Mathlib/NumberTheory/SelbergSieve.lean` (`siftedSum_le_mainSum_errSum_of_upperMoebius`,
   `upperMoebius_lambdaSquared`); our `Erdos385/Brun/` did the dimension-2 analogue and is a
   template.
2. **Buchstab identity**: `S(A, z) = S(A, z₀) − Σ_{z₀ ≤ p < z} S(A_p, p)`.
3. **Fundamental lemma at `z₀ = Y^{η}`** (`η → 0` slowly): `S(A, z₀) ≥ X V(z₀)(1 − o(1)) − D₀`, e.g.
   by Brun's pure sieve / Bonferroni with `D₀ = z₀^{O(1/η)}` small.
4. **Assemble**: subtract step 1's upper bounds for `S(A_p, p)` at level `D/p` (sharp when
   `√(D/p) ≤ p`, i.e. `p ≥ D^{1/3}`; for smaller `p` use monotonicity in the sifting limit to stay
   in the sharp range).  Mertens with an explicit error (`V(z) ≍ e^{−γ}/log z`; mathlib or PNT+ has
   `∏(1 − 1/p)` asymptotics, else prove the version you need) turns the prime sum into the integral
   giving `f(s) = 2e^γ log(s − 1)/s` on `2 < s ≤ 3`.  Then `X = Y/2`, `D = Y^{1−ε/4}`,
   `z = Y^{1/2−ε}`: `s ≥ 2 + ε` and the count is `≥ (Y/2) V(z) f(s)/2 ≫_ε Y/log Y`.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: this statement and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **The linear-sieve lower bound** (Jurkat–Richert, interval case), proved. -/
theorem linearSieveIntervalLower_holds : LinearSieveIntervalLower := by
  sorry

end LeanFormalizations.Erdos385

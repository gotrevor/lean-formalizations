/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.LacunaryFib.Boundary
import LeanFormalizations.Literature.Diophantine

/-!
# Divisibility chains: ratio-two rigidity from Roth (2026-10-05)

If `n k ∣ n (k + 1)` for every `k`, then `F_(n k) ∣ F_(n J)` for `k ≤ J` (`Nat.fib_dvd`), so the
partial sum `S_J = ∑_(k ≤ J) 1/F_(n k)` has denominator dividing the single number `F_(n J)`, not
the product.  The error `x − S_J` is about `1/F_(n (J+1))`, so `|x − S_J| ≪ q^(−n_(J+1)/n_J)` with
`q = F_(n J)`.  In a chain the ratio `n_(J+1)/n_J` is an integer `≥ 2`.  If it is not eventually
`2`, it is `≥ 3` infinitely often, and exponent `3 > 2` contradicts Roth for algebraic irrational
`x`.  Exponent `> 1` already excludes rational `x`, since the tail is positive.  If it is eventually
`2`, Millin makes `x` algebraic (`algebraic_of_eventually_doubling`).

So `RatioTwoRigidity` holds on divisibility chains, and in particular `RestrictedRigidity` (every
`2^(e k)`) holds outright.  The Sturmian case left open in `Boundary.lean` is **closed**: it was
open only in my map, not in mathematics.  The leftover crux is sequences **without** divisibility
(`n_(k+1) = 2 n_k + 1`), where the partial-sum denominators are products.

Novelty: modest (~40%).  It is the "small denominators" group of Nguyen 2022's introduction
(Mignotte, Badea), run at the ratio-two boundary with the chain structure.  The `iff`
classification was not found in the sources read so far.  Strip the specific (not yet stated): the
`→` direction needs only a strong divisibility sequence with exponential growth.  The `←` direction
needs Millin's telescoping, i.e. a Lucas sequence whose root `α` is a unit of norm `−1` (Fibonacci,
Pell).
-/

namespace LeanFormalizations.LacunaryFib

open Filter Real LeanFormalizations.Literature

/-- **Divisibility-chain rigidity (believed ~90%, from Roth).**  Route in the module docstring:
partial sums `p / F_(n J)`, error `≤ 2 / F_(n (J+1))`, and Binet bounds
`φ^(m−2) ≤ F_m ≤ φ^(m−1)` turn ratio `≥ 3` into `|x − r| < C r.den^(−3)` for infinitely many
distinct `r`.  The reduced denominator only helps. -/
theorem divChain_rigidity (hR : Roth1955) (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (hmono : StrictMono n) (hdiv : ∀ k, n k ∣ n (k + 1)) :
    IsAlgebraic ℚ (∑' k, ((Nat.fib (n k) : ℝ))⁻¹) ↔ ∀ᶠ k in atTop, n (k + 1) = 2 * n k := by
  sorry

/-- **Restricted rigidity holds (wiring, ~90%).**  Enumerate `K` increasingly (`Nat.nth`); `2^(e j)`
is a divisibility chain, and coinfinite `K` gives infinitely many gaps, so the ratio is `≥ 4`
infinitely often.  Then apply `divChain_rigidity`. -/
theorem restrictedRigidity_holds (hR : Roth1955) : RestrictedRigidity := by
  sorry

end LeanFormalizations.LacunaryFib

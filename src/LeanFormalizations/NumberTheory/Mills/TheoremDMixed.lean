/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.TheoremDGeneral

/-!
# Phase 57: Theorem D in full (`PROOF-THEOREM-D.md` draft 2) — some root a `c`-unit suffices

Phase 56 proved Theorem D when **every** root of `f` is a `c`-unit (`c ∤ f(0)`).  The paper proof
needs only that **some** root is (`f ≢ X^d (mod c)`).  The excluded class `f ≡ X^d (mod c)` is
provably invisible to the method (Proposition D′), so this is the method's full reach.

## Route (extend phase 56)
1. **Limit matrix with non-unit roots.**  `T := C^(c^n)` (for `n` large, along a class) satisfies
   `T^(Q+1) ≡ T (mod c^k)` instead of `T^Q ≡ I`: on unit eigen-directions it is Teichmüller
   (`u^Q = 1`), on non-unit ones it tends to `0`.  Also `tr(T^Q) ≡ m (mod c^k)`, where
   `1 ≤ m ≤ d` is the number of unit roots (the rank of the idempotent `T^Q`; `m ≥ 1` exactly because
   `f ≢ X^d (mod c)`; `m` = degree of the largest factor of `f mod c` coprime to `X`, i.e.
   `d − (multiplicity of X in f mod c)`).  Encode both, plus the window equation, as the integer
   system at level `k`, exactly as phase 56 does.
2. **Transfer** (phase 55/56 Nullstellensatz): a complex solution `(x_j, w)`, `T = P(C)`, with
   eigenvalues `u_k = P(α_k) ∈ {0} ∪ μ_Q` and exactly `m ≥ 1` of them nonzero (`Σ u_k^Q = m`).
3. **One automorphism** (the new step): pick `k*` with `u_(k*) ≠ 0` and `σ ∈ Aut(ℂ)` with
   `σ(α_(k*)) = α` (`f` irreducible over `ℚ`, so `Gal` is transitive on the roots; extend to `ℂ`
   via `IsAlgClosed` lifting, e.g. `IsAlgClosed.lift` / `AlgEquiv` extension of the splitting field,
   or `Polynomial.Gal` + `Complex` automorphism extension).  `σ` applied to the complex solution
   is again a solution of the same *integer* system (`MvPolynomial.eval` commutes with ring homs:
   phase 55's `torsionPair_map` pattern), now with a nonzero eigenvalue at `α`.
4. **Size:** `α^s ≤ |w − ε| + Σ_(k≥2) |α_k|^s < d + 1`, contradiction (phase 56's final step).

Frozen: the statement below; all earlier statements; `Literature/`.  No `private`.
Decomposing into named sub-lemmas is progress.
-/

namespace LeanFormalizations.Mills.TheoremDMixed

open Filter Polynomial

/-- **Theorem D (full):** some root of `f` is a `c`-unit, i.e. `f ≢ X^d (mod c)`. -/
theorem floor_pow_prime_pow_add_not_prime_full (f : ℤ[X]) (hmon : f.Monic)
    (hirr : Irreducible f) (hdeg : 2 ≤ f.natDegree) {α : ℝ} (hroot : aeval α f = 0)
    (hα : 1 < α)
    (hpisot : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z ≠ (α : ℂ) → ‖z‖ < 1)
    {c : ℕ} (hc : c.Prime) (hunit : f.map (Int.castRingHom (ZMod c)) ≠ X ^ f.natDegree)
    {s : ℕ} (hs : (f.natDegree : ℝ) + 1 < α ^ s) :
    ∃ᶠ n in atTop, ¬ (⌊α ^ (c ^ n + s)⌋₊).Prime := by
  sorry

end LeanFormalizations.Mills.TheoremDMixed

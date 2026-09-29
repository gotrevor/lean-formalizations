/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Gauss congruence for traces of integer matrices

A cited theorem, entered as a hypothesis `Prop` (never an axiom).
-/

namespace LeanFormalizations.Literature

/-- **Gauss (Euler) congruence for matrix traces, prime-power case.**  For every square integer
matrix `C`, prime `p` and `k : ℕ`, `tr C^(p^(k+1)) ≡ tr C^(p^k) (mod p^(k+1))`.

This is the case `n = p^(k+1)` of the Dold/Gauss congruence `∑_{d ∣ n} μ(n/d) tr C^d ≡ 0 (mod n)`:
for a prime power only `d = p^(k+1)` and `d = p^k` have `μ(n/d) ≠ 0`.

H. Steinlein, *Fermat's little theorem and Gauss congruence: matrix versions and cyclic
permutations*, Amer. Math. Monthly **124** (2017), no. 6, 548–, doi:10.4169/amer.math.monthly.124.6.548. -/
def GaussCongruenceTrace : Prop :=
  ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (p k : ℕ), p.Prime →
    ((p : ℤ) ^ (k + 1)) ∣ (C ^ (p ^ (k + 1))).trace - (C ^ (p ^ k)).trace

end LeanFormalizations.Literature

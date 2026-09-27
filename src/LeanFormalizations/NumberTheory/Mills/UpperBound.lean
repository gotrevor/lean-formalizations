/-
# An explicit upper bound on Mills' constant, without RH

`lower_bound` gives `1.3063778838 < ξ` unconditionally; the matching `< 1.3063778839` needs RH
(`lower_bound_of_RH`).  Without RH the best available is astronomically weak but explicit,
from Dudek's explicit cube-gap theorem (`Literature.Dudek2016`, a hypothesis like the others).

## Proof plan

Let `E = exp(exp 33.3)` and `N₀ = ⌈E⌉₊`.

1. Bertrand (`Nat.exists_prime_lt_and_le_two_mul`) gives a prime `p` with `N₀ ≤ p ≤ 2 N₀`.
2. Every link of a Mills chain started at `p` is `≥ p ≥ E`, so Dudek extends it forever:
   the construction in `Basic.lean` / `Chain.lean`, but started at a *chosen* prime `p`
   instead of `Nat.exists_infinite_primes`.  It gives a Mills `A > 1` with `⌊A³⌋₊ = p`, so
   `A³ < p + 1`.
3. `p + 1 ≤ 2 N₀ + 1 ≤ 2 E + 3 ≤ 3 E`, and `3^(1/3) < 2`, so `A < 2 · exp(exp(33.3) / 3)`.
4. A least Mills number `ξ` exists (`exists_least_of_exists`) and `ξ ≤ A`.
-/
import LeanFormalizations.NumberTheory.Mills.LowerBound
import LeanFormalizations.Literature.Primes

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- **The least Mills number exists and is below `2 · exp(exp(33.3) / 3)`**, from Dudek's
explicit cube-gap theorem.  No RH. -/
theorem exists_minMills_lt_of_dudek (h : Dudek2016) :
    ∃ A, IsMinMills A ∧ A < 2 * Real.exp (Real.exp 33.3 / 3) := by
  sorry

/-- The same bound for any least Mills number (the least element is unique). -/
theorem minMills_lt_of_dudek (h : Dudek2016) {A : ℝ} (hA : IsMinMills A) :
    A < 2 * Real.exp (Real.exp 33.3 / 3) := by
  obtain ⟨B, hB, hlt⟩ := exists_minMills_lt_of_dudek h
  rw [hA.unique hB]
  exact hlt

end LeanFormalizations.Mills

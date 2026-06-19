import Mathlib

open Finset

/-- **Dirichlet hyperbola identity** (pure ℕ). For every `N`, with `K = Nat.sqrt N`,
`∑_{a=1}^{N} ⌊N/a⌋ + K^2 = 2·∑_{a=1}^{K} ⌊N/a⌋`.

Mathematical content: the number of lattice points `(a,b)` with `a,b ≥ 1` and `a·b ≤ N`
equals `∑_{a=1}^{N} ⌊N/a⌋` (count `b` for each `a`). Every such pair has `a ≤ K` or `b ≤ K`
(else `a,b ≥ K+1` forces `a·b ≥ (K+1)^2 > N`). Inclusion–exclusion over `{a ≤ K}` and
`{b ≤ K}`, noting `a,b ≤ K ⟹ a·b ≤ K^2 ≤ N` (so all `K^2` such pairs are counted), gives
`D(N) = 2·∑_{a=1}^{K} ⌊N/a⌋ − K^2`. Verified numerically at N = 1,2,4,10. -/
theorem hyperbola_identity (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, N / a) + (Nat.sqrt N) ^ 2
      = 2 * ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), N / a := by
  sorry

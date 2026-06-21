/-
Boundary term of an Abel-summation argument for the prime zeta function.
With f(t)=t^(1-s), s>1, and a(n) the partial sum of prime reciprocals up to n
(0 ≤ a n ≤ 1 + log n by the harmonic bound), the boundary f(n)·a(n) → 0 because
polynomial decay n^(1-s)=n^(-(s-1)) (s-1>0) beats logarithmic growth of a(n).

Strategy: squeeze 0 ≤ n^(1-s)*a n ≤ n^(1-s)*(1+log n); show the upper bound → 0 by
splitting n^(1-s) → 0 and n^(1-s)*log n → 0 ("polynomial beats log"; e.g.
Real.tendsto_log_div_rpow_nhds_zero / Real.isLittleO_log_rpow_atTop, or log n ≤ (1/ε)n^ε).
Replace the sorry with a complete proof. Keep the statement exactly as given.
-/
import Mathlib
open Filter Topology

theorem boundary_decay (s : ℝ) (hs : 1 < s) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (haC : ∀ n, a n ≤ 1 + Real.log n) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s) * a n) atTop (nhds 0) := by
  sorry

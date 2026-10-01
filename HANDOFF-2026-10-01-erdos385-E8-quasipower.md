# HANDOFF — Erdős #385 phase E8 (QuasiPower), branch erdos-385-b

## Status
Target: `src/LeanFormalizations/NumberTheory/Erdos385/QuasiPower.lean` (frozen `badCountQuasiPower_holds`,
`badCountExp_threeQuarters`, both still `sorry`).  Everything below is sorry-free and committed.

## NEW ROUTE (replaces the header's Freedman plan — no tail estimate for u(s) needed)
For each class s mod y#: take a window of k positions a ∈ (Y/2, Y], Y = y^{9/4}, diameter < y,
all coprime (vs s) to primes ≤ y (linear sieve + pigeonhole).  For bad n, n−a is prime or has
minFac ∈ (y, a].  Expand ∏_a(Σ_{p∈(y,a]} 1_{p|n−a} + 1_{n−a avoids pool}); each term is a large-sieve
count; diameter < y ⇒ chosen primes distinct.  Per-position factor ρ + Σ 1/(p−1) ≤ 1/20 + 0.87.
(Header's Freedman good-event route caps at exponent 1/2: one class can deviate by ≍y^{1/2}/log y with
prob ≥ exp(−c y^{1/2}). Not yet a Lean statement.)

## Done (QuasiPower/)
- Sieve.lean `sieve_count_gen`, `poolWeight`
- ClassCount.lean `bad_dichotomy`, `prod_expand`, `class_count`
- Esymm.lean `esymm_lower`, `poolWeight_ge`
- Window.lean `exists_window`
- MertensSums.lean `sum_inv_sub_one_le` (≤0.87), `sum_inv_ge`
- Total.lean `total_count`
- Params.lean `bound_m`: ∃ m₀, ∀ X m, m₀ ≤ m → 2^(8m⁴) ≤ X →
  #bad ≤ 2^{t²} + m⁹ + m⁴·C·(X+X)·(23/25)^{m⁴/(16t²)}, t = log₂ m + 1.

## NEXT (final step, pure real analysis)
New file QuasiPower/Final.lean: get C from `exists_lsWith arithLargeSieveWeak_holds`,
h2 := `linearSieveIntervalLower_holds`.  Set ℓ = Nat.log 2 X, m = Nat.sqrt (Nat.sqrt (ℓ/8)) so
2^{8m⁴} ≤ X.  Show for m ≥ m₀': RHS ≤ C'·X·exp(−c log X/(log log X)²) (log X ≤ C1 m⁴,
loglog X ≥ log m, k ≥ m⁴/(144 log²m) − 1, R+Y ≤ 2^{m⁴+…} ≪ X).  Small X (m < m₀'): X bounded,
use (loglog X)² ≥ 1 for X ≥ 16 so exp factor ≥ X₁^{−c}.  Then milestone from moonshot.
Gotcha: use `obtain ⟨t, ht⟩ : ∃ t, t = … := ⟨_, rfl⟩` not `set` (whnf timeouts on 2^(t^2)),
and never let opaque locals be unified with powers (pass `show 1 ≤ R by rw [hR]; …`).

# Is Mills' constant transcendental? (probe, 2026-09-29)

**Status: open unconditionally; YES under RH (and under the Density Hypothesis).**
K. Saito, *Transcendency of variants of Mills' constant*, arXiv:2508.16068 (v3 2025-12-07),
Ramanujan J. (2026), doi:10.1007/s11139-026-01443-0 — local `papers/saito-2025-transcendency-variants-mills.txt`.

## What Saito 2025 proves (Theorem 1.7, 1.8)

If ξ = Mills' constant is algebraic, then some β = ξ^(3^m) is a **totally real** cubic Pisot number
with conjugates β > 1 > |β₂| > |β₃| and `|β₃| < −β₂ ≤ min(|β₃|^(17/23), β^(−17/40))`.  If for every
θ > 1/2 intervals `[x, x + x^θ]` eventually contain `≫ x^θ / log x` primes (true under DH, hence RH),
ξ is transcendental.  Infinitely many totally real cubic Pisot numbers satisfy (1.3) (Dubickas 2004),
so (1.3) alone does not close it.

## Independent re-derivation (Ren, before finding the paper)

Write `N = 3^(k−m)`, `xᵢ = βᵢ^N`, `s = x₂ + x₃`.  For large k, `p_k = Tr β^N` (Saito 2024, Lemma 4.2),
and Newton's identity for cubes gives the exact gap formula
`g_k := p_(k+1) − p_k³ = −3 s (x₁² + x₁ s + x₂x₃)`.  Since `p_(k+1)` is a prime and not a cube,
`g_k > 0`, so **`s < 0` for every large k**.

* **Complex conjugates die unconditionally.**  `s = 2|x₂| cos ψ_k` and `ψ_(k+1) = 3ψ_k (mod 2π)`.  The
  only ×3-orbit staying in the open left half-circle `cos < 0` is the fixed point `ψ = π`, by nested
  thirds around 1/2.  Then `β₂^N = β₃^N`, so `β^N` would have a conjugate of multiplicity 2 in a cubic
  field, which is impossible.  (Saito does this with "symbolic dynamics".)
* **Totally real, under RH.**  `|s| ≥ |β₂|^N / 2` and `|β₂|² = ρ |β₂β₃| ≥ ρ/β` with `ρ = |β₂/β₃| > 1`, so
  `g_k ≥ ρ^(N/2) √x` at `x = p_k³`.  Carneiro–Milinovich–Soundararajan give `g_k ≤ (22/25) √x log x`,
  and `log x` is only linear in N.  Contradiction.

So the derivation lands exactly on Saito's Theorem 1.7 / 1.8: a sanity check, not a new result.

## What is left, and why it is hard

Unconditionally: exclude a totally real cubic Pisot β with (1.3).  The algebraic side forces a
prime-free stretch after `p_k³` of length `≥ x^(1/2 + η)`, `η = log ρ / (6 log β) > 0`, for *every*
large k.  Unconditional prime-gap bounds (BHP, `x^(21/40)`) only kill `η > 1/40`.  Exceptional-set
results (Matomäki) say such long gaps are rare, but the Mills sequence is one point per k, far too
sparse for a density statement to exclude.  Closing it needs a new idea tying the arithmetic of
`Tr β^(3^k)` to primality, not better analytic gap bounds.  Estimate: < 5% for a probe.

Lean: `NumberTheory/Mills/Transcendental.lean` has Saito 2024 Thm 1.2 (`transcendental_or_pisot`).
Saito 2025 is not formalized here, and per the 2026-09-29 direction it would enter only as a
hypothesis `Prop` when something consumes it.

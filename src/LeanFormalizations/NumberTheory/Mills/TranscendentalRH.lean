/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Mills' constant is transcendental, assuming RH (Saito 2025, Theorems 1.7–1.8)

K. Saito, *Transcendency of variants of Mills' constant*, arXiv:2508.16068 (v3, 2025-12-07),
Ramanujan J. (2026); local `papers/saito-2025-transcendency-variants-mills.txt`.  Our route is the
elementary one in `PROBE-MILLS-TRANSCENDENCE.md` (re-derived independently, it lands on Saito's
Theorem 1.7), with RH entering only through `Schoenfeld1976` (already in `RH.lean`).

## Setting

`transcendental_or_pisot` (`Transcendental.lean`, Saito 2024 Thm 1.2): if `A` (least Mills) is
algebraic, some `β = A^(3^m)`, `m ≥ 1`, is a Pisot number of degree 3.  Let `β₂, β₃` be its other
conjugates (`otherConj β`), `N = N_k = 3^(k−m)` (odd), `xᵢ = βᵢ^N`, `s_k = x₂ + x₃ ∈ ℝ`,
`p_k = ⌊A^(3^k)⌋` (the Mills primes; under RH they are `gseq`, `RH.lean`).

## Steps

1. **Traces are the primes** (Saito 2024, Lemma 4.2): `Tr β^N = p_k` for all large `k`.  (Uses
   `ξ^(3^k) − p_k → 0` fast; the degree-2 proof in `SaitoDegreeTwo.lean` may already have it.)
2. **Exact gap identity** (Newton's identities for cubes, pure algebra):
   `p_(k+1) − p_k³ = −3 s_k (x₁² + x₁ s_k + x₂x₃)`.
3. **Sign**: `p_(k+1) > p_k³` (prime, not a cube), and `x₁² + x₁ s + x₂x₃ > 0` for large `k`,
   so `s_k < 0` for all large `k`.
4. **Complex case dies (unconditional).**  If `β₂ = β̄₃ ∉ ℝ`: `s_k = 2|x₂| cos ψ_k`,
   `ψ_(k+1) = 3 ψ_k (mod 2π)`.  Circle lemma (`times_three_orbit`): if `x, 3x, 9x, … (mod 1)`
   all lie in the open interval `(1/4, 3/4)` then `x = 1/2` (by induction `|3ʲx mod 1 − 1/2| =
   3ʲ|x − 1/2| < 1/4`).  So `β₂^N` is real and `β₂^N = β₃^N`; then `β^N ∈ ℚ(β)` has a conjugate of
   multiplicity 2 while its degree is 1 or 3 — impossible (`|β₂| < 1 < β`).
5. **Real case under RH.**  `|β₂| ≠ |β₃|` (else `β₃ = −β₂` and `s_k = 0` for odd `N`); say
   `ρ = |β₂/β₃| > 1`.  Then `|s_k| ≥ |β₂|^N / 2`, `|β₂|² = ρ |β₂β₃| ≥ ρ / β` (norm is a nonzero
   integer), so `p_(k+1) − p_k³ ≥ ρ^(N/2) · √(p_k³)` for large `k`.  Under RH (Schoenfeld) the
   least prime above `x` is `< x + C √x log x`, and `p_(k+1)` is the least prime above `p_k³`
   (greedy chain, `RH.lean`).  `log (p_k³) ≤ 3N log β + O(1)` is linear in `N`, `ρ^(N/2)` is
   exponential: contradiction.

Numbers are Saito's where they match; split into named leaves freely.  Frozen: the two theorems
below (names and statements), every earlier name, all of `Literature/`.
-/
import LeanFormalizations.NumberTheory.Mills.Transcendental
import LeanFormalizations.NumberTheory.Mills.RH

namespace LeanFormalizations.Mills

open LeanFormalizations.Literature

/-- **Saito (2025), Theorem 1.7, first half**: in the Pisot branch of Mills' constant, the two
other conjugates of the cubic Pisot number are real (no complex pair).  Unconditional beyond the
hypotheses of Saito 2024 Thm 1.2. -/
theorem pisot_branch_otherConj_real (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    {A : ℝ} (hA : IsMinMills A) {m : ℕ} (hm : 1 ≤ m) (hP : IsPisot (A ^ (3 ^ m)))
    (h3 : (minpoly ℚ (A ^ (3 ^ m))).natDegree = 3) :
    ∀ z ∈ otherConj (A ^ (3 ^ m)), z.im = 0 := by
  sorry

/-- **Mills' constant is transcendental, assuming the Riemann Hypothesis** (Saito 2025,
Theorem 1.8; RH via Schoenfeld's explicit prime-counting bound). -/
theorem transcendental_of_RH (hS : Schoenfeld1976) (hRH : RiemannHypothesis)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) : Transcendental ℚ A := by
  sorry

end LeanFormalizations.Mills

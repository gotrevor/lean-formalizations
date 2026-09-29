/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.ThreeAdic

/-!
# One conjecture behind Fermat and Mills (phase 30)

Fermat numbers `F_k = 2^(2^k) + 1 = tr diag(2,1)^(2^k)`.  Mills primes, if Mills' constant `A` is
algebraic, are `⌊A^(3^(m+k))⌋ = tr C^(3^k)` for the companion matrix `C` of a cubic Pisot number
(phase 29, inside `mills_threeAdic`).  Both are **double-exponential trace sequences**
`tr C^(c^k) + h`.  Neither question is known to imply the other: the bases (2 vs 3) and the
eigenvalue structures differ, and no transfer is known.  But one conjecture implies both.

`DoubleExpTraceComposite` (Ren, 2026-09-29, stated here; not from the literature):
for every square integer matrix `C`, base `c ≥ 2` and shift `h`, if `|tr C^(c^k) + h| → ∞` then
`tr C^(c^k) + h` is composite (not prime) for infinitely many `k`.  The growth hypothesis is
needed: eigenvalues `λ, −λ` with `c` odd make the trace `0`, so the sequence is `h`, possibly a
constant prime.  The standard heuristic (a number of size `X` is prime with probability about
`1/log X`, and `Σ 1/c^k` converges) predicts even that only finitely many terms are prime.

Phase 29 proves the conjecture's `c = 3`, `h = 0` case whenever the `3`-adic limit is not `±1`.
`lt_padicValNat_glCard_prime_base` below generalizes phase 29's unconditional step to any prime
base `c` and shift `h`.

## Route
- `fermat_of_doubleExpTraceComposite`: `C = diag(2,1)`, `c = 2`, `h = 0`; `tr C^(2^k) = F_k → ∞`.
- `mills_transcendental_of_doubleExpTraceComposite`: by contradiction, assume `A` is algebraic.
  Reuse the glue inside `mills_threeAdic` (Saito's Pisot branch, `companion3`, `hfloor`: eventually
  `tr C^(3^i) = ⌊A^(3^(m+i))⌋`, which is prime by `IsMills`).  Factor it out as a lemma first.
  Then the conjecture with `c = 3`, `h = 0` gives a composite floor.
- `lt_padicValNat_glCard_prime_base`: copy `dvd_trace_pow_three_of_glCard` and
  `lt_padicValNat_glCard` with `3` replaced by a prime `c` and the trace shifted by `h`.  The
  argument is unchanged: `c^j ≡ 1 (mod M)` for `j = φ(M)` when `c ∤ M`.

Frozen: every statement below, everything in `ThreeAdic.lean`, all of `Literature/`.
-/

namespace LeanFormalizations.Mills.SharedConjecture

open LeanFormalizations.Literature LeanFormalizations.Mills.ThreeAdic Matrix Filter

/-- **Conjecture (Ren, 2026-09-29).**  Double-exponential trace sequences are composite infinitely
often, once they grow. -/
def DoubleExpTraceComposite : Prop :=
  ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (c : ℕ) (h : ℤ), 2 ≤ c →
    Tendsto (fun k : ℕ => |(C ^ (c ^ k)).trace + h|) atTop atTop →
    ∃ᶠ k in atTop, ¬ Prime ((C ^ (c ^ k)).trace + h)

/-- The conjecture implies infinitely many composite Fermat numbers. -/
theorem fermat_of_doubleExpTraceComposite (hC : DoubleExpTraceComposite) :
    ∃ᶠ k in atTop, ¬ (Nat.fermatNumber k).Prime := by
  sorry

/-- The conjecture implies that the least Mills constant is transcendental. -/
theorem mills_transcendental_of_doubleExpTraceComposite (hC : DoubleExpTraceComposite)
    (hB : BakerHarmanPintz2001) (hM : Matomaki2007) (hD : Dubickas2022)
    (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A) : Transcendental ℚ A := by
  sorry

/-- Phase 29's unconditional step for any prime base `c` and shift `h`: if `tr C^(c^k) + h` is
prime and strictly increasing from some point on, then `v_c |GL_n(𝔽_{t_k})| > k` for all large
`k`. -/
theorem lt_padicValNat_glCard_prime_base {n c : ℕ} (hc : c.Prime) (C : Matrix (Fin n) (Fin n) ℤ)
    (hdet : C.det ≠ 0) (h : ℤ) {k₀ : ℕ}
    (hprime : ∀ k ≥ k₀, Prime ((C ^ (c ^ k)).trace + h))
    (hmono : ∀ k ≥ k₀, (C ^ (c ^ k)).trace + h < (C ^ (c ^ (k + 1))).trace + h) :
    ∃ K, ∀ k ≥ K, k < padicValNat c (glCard n ((C ^ (c ^ k)).trace + h).toNat) := by
  sorry

end LeanFormalizations.Mills.SharedConjecture

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SharedConjecture

/-!
# The projective-order lemma (phase 31; Astra's extension of phase 29)

Write-up: `FINDING-MILLS-3ADIC.md` § Extension; numerics: `scripts/mills-3adic-probe.py projective`.

If the characteristic polynomial of `C : Matrix (Fin 3) (Fin 3) ℤ` is irreducible mod a prime
`p ≠ 3`, then `𝔽_p[C̄] ≅ 𝔽_(p³)`.  The image of `C̄` in `𝔽_(p³)^× / 𝔽_p^×` has order dividing
`p² + p + 1`, whose 3-adic valuation is at most `1`.  So for `m ≥ 1` the class of `g = C̄^(3^m)`
has order `d` prime to 3.  Take `j = φ(d)`: then `g^(3^j) = λ g` for a scalar `λ`, hence
`tr C^(3^(m+j)) ≡ λ · tr C^(3^m) (mod p)`.  This works even when `p` is 3-adically close to `1`,
exactly where phase 29's `GL₃` bound fails.

## Route
- `dvd_trace_of_irreducible_mod`: a Lean-friendly version of the projective argument.  Work in
  `K = AdjoinRoot f̄`, a field of size `p³` (or with the subalgebra `𝔽_p[C̄]`, via Cayley–Hamilton).
  Use `x^(p³−1) = 1` and `x^(p²+p+1) ∈ 𝔽_p` (the norm: `x^(1+p+p²) = x · x^p · x^(p²)` is Frobenius
  invariant).  Also `v₃(p²+p+1) ≤ 1` for `p ≠ 3` (check residues mod 9).  Trace mod `p` becomes
  scalar-times-trace.
- `not_irreducible_mod_eventually`: combine with eventual primality and monotonicity, as in
  `lt_padicValNat_glCard`.
- `composite_of_irreducible_divisor`: once `q ∣ t_m`, the lemma gives `q ∣ t_(m+j)`; iterating
  gives infinitely many; for large `k`, `t_k > q`.
- `mills_reducible_mod_primes`: `exists_companion_of_algebraic_mills` plus the previous item.  The
  companion matrix's charpoly is the minimal polynomial of `A^(3^m)`, so record that
  `A^(3^m)` is a root.

Frozen: every statement below, everything in `ThreeAdic.lean` and `SharedConjecture.lean`, all
of `Literature/`.
-/

namespace LeanFormalizations.Mills.Projective

open LeanFormalizations.Literature LeanFormalizations.Mills.ThreeAdic Matrix Filter Polynomial

/-- **Astra's lemma.**  Irreducible reduction mod `p ≠ 3` plus `p ∣ tr C^(3^m)` with `m ≥ 1`
forces `p ∣ tr C^(3^(m+j))` for some `j ≥ 1`. -/
theorem dvd_trace_of_irreducible_mod (C : Matrix (Fin 3) (Fin 3) ℤ) {p m : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hirr : Irreducible (C.map (Int.castRingHom (ZMod p))).charpoly)
    (hm : 1 ≤ m) (hdiv : (p : ℤ) ∣ (C ^ (3 ^ m)).trace) (hdet : ¬ (p : ℤ) ∣ C.det) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (C ^ (3 ^ (m + j))).trace := by
  sorry

/-- If `t_k = tr C^(3^k)` is eventually prime and increasing, the charpoly is eventually
reducible mod `t_k`. -/
theorem not_irreducible_mod_eventually (C : Matrix (Fin 3) (Fin 3) ℤ) (hdet : C.det ≠ 0)
    {k₀ : ℕ} (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∀ᶠ k in atTop,
      ¬ Irreducible (C.map (Int.castRingHom (ZMod (C ^ (3 ^ k)).trace.toNat))).charpoly := by
  sorry

/-- **A one-prime certificate.**  If some prime `q ≠ 3` at which the charpoly stays irreducible
divides a single `t_m` with `m ≥ 1`, then `t_k` is not prime for infinitely many `k`. -/
theorem composite_of_irreducible_divisor (C : Matrix (Fin 3) (Fin 3) ℤ) {q m : ℕ}
    (hq : q.Prime) (hq3 : q ≠ 3) (hirr : Irreducible (C.map (Int.castRingHom (ZMod q))).charpoly)
    (hm : 1 ≤ m) (hdiv : (q : ℤ) ∣ (C ^ (3 ^ m)).trace) (hdet : ¬ (q : ℤ) ∣ C.det)
    (hgrow : Tendsto (fun k : ℕ => (C ^ (3 ^ k)).trace) atTop atTop) :
    ∃ᶠ k in atTop, ¬ Prime (C ^ (3 ^ k)).trace := by
  sorry

/-- **Mills.**  If the least Mills constant `A` is algebraic, then (for the integer matrix whose
charpoly has `A^(3^m)` as a root and whose `3^i`-th power traces are the Mills primes) the
charpoly has a root mod every sufficiently late Mills prime. -/
theorem mills_reducible_mod_primes (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A)
    (halg : IsAlgebraic ℚ A) :
    ∃ (C : Matrix (Fin 3) (Fin 3) ℤ) (m : ℕ),
      (C.charpoly.map (Int.castRingHom ℝ)).IsRoot (A ^ ((3:ℕ) ^ m)) ∧
      (∀ᶠ i in atTop, (C ^ ((3:ℕ) ^ i)).trace = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ)) ∧
      ∀ᶠ i in atTop,
        ¬ Irreducible (C.map (Int.castRingHom (ZMod ⌊A ^ ((3:ℕ) ^ (m + i))⌋₊))).charpoly := by
  sorry

end LeanFormalizations.Mills.Projective

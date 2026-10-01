/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.Projective
import LeanFormalizations.NumberTheory.Mills.GaussCongruenceProof
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Kronecker lemma (phase 60)

Write-up: `PROBE-MILLS-RESIDUAL.md` §3; numerics: `scripts/mills-residual-probe.py`
(`kron-control`, `filter`, `saito`, `tau-minus`).

Phase 31 excluded primes at which the charpoly stays irreducible.  This phase excludes the other
Frobenius type that `p ≡ 2 (mod 3)` makes recurrent: complete splitting.  The sharpened core is
that a split charpoly forces the reduced matrix to have order dividing `p^n (p − 1)`, which is
prime to `c` whenever `c` is coprime to `p (p − 1)`.  So the trace sequence `tr C^(c^m) mod p`
is purely periodic, with no projective step and no hypothesis on multiplicities.

For a cubic, "neither split nor irreducible" means type (1)(2), which forces the discriminant to
be a non-square mod `p`.  So in the residual classes with `Tr β ≡ 2 (mod 3)`, every late Mills
prime `p` has `(disc / p) = −1`.  Since `tr C^(3^k) mod 4|disc|` is eventually periodic, this is
a finite certificate on `C` (`composite_of_jacobi_hit`).

## Route

- `trace_pow_periodic_of_splits`.
  - Over `ZMod p`, `D = C̄` has a split charpoly `χ` with nonzero roots (since `p ∤ det`).
  - Every root `λ` satisfies `λ^(p−1) = 1`.  So `(X − λ) ∣ X^(p−1) − 1`, and each root's
    multiplicity is at most `n`, which gives `χ ∣ (X^(p−1) − 1)^n`.  Use `Splits` to write `χ`
    as a product over its roots.
  - Cayley–Hamilton (`Matrix.aeval_self_charpoly`) gives `(D^(p−1) − 1)^n = 0`.  So
    `U = D^(p−1)` is unipotent, and `U^(p^n) = 1` by `add_pow_char_pow` (`1` and `U − 1`
    commute, and `(U − 1)^(p^n) = 0` since `n ≤ p^n`).  Hence `D^(p^n (p−1)) = 1`.
  - Take `J = φ(p^n (p−1))`.  Then `c^J ≡ 1 (mod p^n (p−1))` (Euler; `hc`), so
    `D^(c^(m+J)) = D^(c^m)` for every `m`.  Take traces.
- `dvd_trace_of_splits_mod`: the `c = 3`, `p ≡ 2 (mod 3)` instance, in phase 31's
  divisibility form.  Coprimality: `3 ∤ p` and `3 ∤ p − 1`.
- `not_splits_mod_eventually`: copy the skeleton of `Projective.not_irreducible_mod_eventually`,
  calling `trace_pow_periodic_of_splits` in place of `dvd_trace_of_irreducible_mod`.  With
  `p = t_k` prime and `p ∣ t_k`, periodicity gives `p ∣ t_(k+J)`, a larger prime.
  `Nat.Coprime c (p (p − 1))` is the hypothesis in the conclusion.
- `splits_of_isSquare_disc`.  Factor out the root `r`: `f = (X − r)(X² + uX + v)` with
  `u = a + r` and `v = b + r u`.  The identity `disc f = (u² − 4v) · (r² + ur + v)²` holds by
  `ring` after substituting `c = −r v`.  `disc f ≠ 0` gives `r² + ur + v ≠ 0`.  So `u² − 4v` is a
  square (`p` odd, so 2 is a unit), and `exists_quadratic_eq_zero` /
  `quadratic_eq_zero_iff` split the quadratic.  A product of linear factors `Splits`.
- `not_isSquare_charDisc_mod_eventually`.
  - Combine phase 31 (not irreducible, hence a root, since the degree is 3) with
    `not_splits_mod_eventually` (`c = 3`; `t_k % 3 = 2` gives the coprimality) and
    `splits_of_isSquare_disc`.
  - Glue: the charpoly of a `3 × 3` matrix is `X³ + C(coeff 2) X² + C(coeff 1) X + C(coeff 0)`
    (`Matrix.charpoly_monic`, `charpoly_natDegree_eq_dim`), and the coefficients commute with
    `map`.
  - `charDisc C ≠ 0` and `t_k > |charDisc C|` give `charDisc ≢ 0 mod t_k`.
- `composite_of_jacobi_hit`.
  - By contradiction, assume `t_k` is prime for all large `k`.
  - Pick `i` with `k = k₁ + iJ` large.  Then `p = t_k ≡ t_(k₁) (mod 4|disc|)`.  Both are odd, so
    `jacobiSym.mod_right` gives `J(disc | p) = 1`.  Hence `disc` is a nonzero square mod `p`
    (`legendreSym.eq_one_iff`).
  - Also `p ≡ tr C ≡ 2 (mod 3)`, by `gaussCongruence_mul` with `m = 1`, `p = 3`, iterated.
  - By `splits_of_isSquare_disc`, `f mod p` is split or has no root (irreducible, since the
    degree is 3).
    - Split: `trace_pow_periodic_of_splits` gives `p ∣ t_(k+J')`, a larger prime.
    - Irreducible: `Projective.composite_of_irreducible_divisor` concludes directly.
- `mills_kronecker`.
  - `Projective.exists_companion_root` (made public for this phase) supplies `C`, `m`, `i₀`.
  - `charDisc C ≠ 0`: the charpoly is the minimal polynomial of the cubic `A^(3^m)`, so it is
    irreducible over ℚ, hence separable, so its roots are distinct.  Use `Cubic.disc_ne_zero_iff_roots_nodup`
    or the product formula over ℂ.
  - Then `not_isSquare_charDisc_mod_eventually` with `t_k % 3 = tr C % 3` (Gauss congruence).
  - If `charDisc C = s²` in ℤ, it is a square mod every Mills prime, which contradicts the
    eventual statement (atTop is nontrivial).

Frozen: every statement below and `charDisc`; all earlier statements; all of `Literature/`.
-/

namespace LeanFormalizations.Mills.Kronecker

open LeanFormalizations.Literature LeanFormalizations.Mills Matrix Filter Polynomial

/-- The discriminant of the characteristic polynomial of a `3 × 3` integer matrix, written in
the charpoly's coefficients `X³ + aX² + bX + c`. -/
noncomputable def charDisc (C : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  let a := C.charpoly.coeff 2
  let b := C.charpoly.coeff 1
  let c := C.charpoly.coeff 0
  a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c

/-- **Split charpoly ⇒ periodic power traces.**  If the charpoly of `C` splits mod `p` and `c`
is coprime to `p (p − 1)`, then `tr C^(c^m) mod p` is purely periodic in `m`. -/
theorem trace_pow_periodic_of_splits {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p c : ℕ}
    (hp : p.Prime) (hc : Nat.Coprime c (p * (p - 1)))
    (hsplit : (C.map (Int.castRingHom (ZMod p))).charpoly.Splits)
    (hdet : ¬ (p : ℤ) ∣ C.det) :
    ∃ J, 1 ≤ J ∧ ∀ m, (C ^ (c ^ (m + J))).trace ≡ (C ^ (c ^ m)).trace [ZMOD p] := by
  sorry

/-- **The Kronecker lemma, divisibility form.**  A split prime `p ≡ 2 (mod 3)` that divides one
`tr C^(3^m)` divides a later one. -/
theorem dvd_trace_of_splits_mod {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p m : ℕ}
    (hp : p.Prime) (hp3 : p % 3 = 2)
    (hsplit : (C.map (Int.castRingHom (ZMod p))).charpoly.Splits)
    (hdiv : (p : ℤ) ∣ (C ^ (3 ^ m)).trace) (hdet : ¬ (p : ℤ) ∣ C.det) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (C ^ (3 ^ (m + j))).trace := by
  sorry

/-- If `t_k = tr C^(c^k)` is eventually prime and increasing, the charpoly eventually does not
split mod any `t_k` with `c` coprime to `t_k (t_k − 1)`. -/
theorem not_splits_mod_eventually {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (hdet : C.det ≠ 0)
    {c k₀ : ℕ} (hc : 2 ≤ c) (hprime : ∀ k ≥ k₀, Prime (C ^ (c ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (c ^ k)).trace < (C ^ (c ^ (k + 1))).trace) :
    ∀ᶠ k in atTop,
      Nat.Coprime c ((C ^ (c ^ k)).trace.toNat * ((C ^ (c ^ k)).trace.toNat - 1)) →
      ¬ (C.map (Int.castRingHom (ZMod (C ^ (c ^ k)).trace.toNat))).charpoly.Splits := by
  sorry

/-- **A cubic with a root and a square discriminant splits** (odd characteristic). -/
theorem splits_of_isSquare_disc {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b c : ZMod p}
    (hdisc : a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c ≠ 0)
    (hsq : IsSquare (a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c))
    (hroot : ∃ r : ZMod p, r ^ 3 + a * r ^ 2 + b * r + c = 0) :
    (X ^ 3 + Polynomial.C a * X ^ 2 + Polynomial.C b * X + Polynomial.C c : (ZMod p)[X]).Splits := by
  sorry

/-- **The Kronecker lemma.**  If `t_k = tr C^(3^k)` is eventually prime and increasing, then
the discriminant is a non-square mod every late `t_k ≡ 2 (mod 3)`: those primes have type
(1)(2). -/
theorem not_isSquare_charDisc_mod_eventually (C : Matrix (Fin 3) (Fin 3) ℤ) (hdet : C.det ≠ 0)
    (hD : charDisc C ≠ 0) {k₀ : ℕ} (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∀ᶠ k in atTop, (C ^ (3 ^ k)).trace % 3 = 2 →
      ¬ IsSquare ((charDisc C : ZMod (C ^ (3 ^ k)).trace.toNat)) := by
  sorry

/-- **The finite Kronecker certificate.**  If `tr C ≡ 2 (mod 3)` and the trace sequence revisits,
modulo `4 |disc|`, a positive odd value at which the Jacobi symbol `(disc / ·)` is `1`, then
`tr C^(3^k)` is composite infinitely often. -/
theorem composite_of_jacobi_hit (C : Matrix (Fin 3) (Fin 3) ℤ) (hdet : C.det ≠ 0)
    (hD : charDisc C ≠ 0) (htr : C.trace % 3 = 2)
    (hgrow : Tendsto (fun k : ℕ => (C ^ (3 ^ k)).trace) atTop atTop)
    {k₁ J : ℕ} (hJ : 1 ≤ J)
    (hper : ∀ i, (C ^ (3 ^ (k₁ + i * J))).trace ≡ (C ^ (3 ^ k₁)).trace [ZMOD 4 * charDisc C])
    (hpos : 0 < (C ^ (3 ^ k₁)).trace) (hodd : Odd (C ^ (3 ^ k₁)).trace.toNat)
    (hjac : jacobiSym (charDisc C) (C ^ (3 ^ k₁)).trace.toNat = 1) :
    ∃ᶠ k in atTop, ¬ Prime (C ^ (3 ^ k)).trace := by
  sorry

/-- **Mills.**  If the least Mills constant is algebraic and its cubic `A^(3^m)` has trace
`≡ 2 (mod 3)`, then the field is not cyclic (the discriminant is not a square) and every late
Mills prime has type (1)(2): the discriminant is a non-square mod it. -/
theorem mills_kronecker (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A)
    (halg : IsAlgebraic ℚ A) :
    ∃ (C : Matrix (Fin 3) (Fin 3) ℤ) (m : ℕ),
      (C.charpoly.map (Int.castRingHom ℝ)).IsRoot (A ^ ((3:ℕ) ^ m)) ∧
      (∀ᶠ i in atTop, (C ^ ((3:ℕ) ^ i)).trace = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ)) ∧
      (C.trace % 3 = 2 →
        ¬ IsSquare (charDisc C) ∧
        ∀ᶠ i in atTop, ¬ IsSquare ((charDisc C : ZMod ⌊A ^ ((3:ℕ) ^ (m + i))⌋₊))) := by
  sorry

end LeanFormalizations.Mills.Kronecker

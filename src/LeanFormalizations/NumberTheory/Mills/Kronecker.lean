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

/-- Over `ZMod p`, a split charpoly with nonzero determinant divides `(X^(p−1) − 1)^n`. -/
theorem splits_dvd_pow {p n : ℕ} [Fact p.Prime] (D : Matrix (Fin n) (Fin n) (ZMod p))
    (hsplit : D.charpoly.Splits) (hdet : D.det ≠ 0) :
    D.charpoly ∣ (X ^ (p - 1) - 1 : (ZMod p)[X]) ^ n := by
  have hm := D.charpoly_monic
  have hcard : Multiset.card D.charpoly.roots = n := by
    rw [← hsplit.natDegree_eq_card_roots, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hne : ∀ a ∈ D.charpoly.roots, a ≠ 0 := by
    intro a ha h0
    subst h0
    rw [mem_roots hm.ne_zero, IsRoot, ← coeff_zero_eq_eval_zero] at ha
    apply hdet
    rw [det_eq_sign_charpoly_coeff, ha, mul_zero]
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hm]
  have key : ∀ s : Multiset (ZMod p), (∀ a ∈ s, a ≠ 0) →
      (s.map (fun x => X - C x)).prod ∣ (X ^ (p - 1) - 1 : (ZMod p)[X]) ^ Multiset.card s := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
      refine mul_dvd_mul ?_ (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))
      rw [dvd_iff_isRoot]
      simp [ZMod.pow_card_sub_one_eq_one (hs a (Multiset.mem_cons_self _ _))]
  have := key _ hne
  rwa [hcard] at this

/-- A matrix over `ZMod p` with split charpoly and nonzero determinant has order dividing
`p^n (p − 1)`. -/
theorem pow_eq_one_of_splits {p n : ℕ} [Fact p.Prime] (D : Matrix (Fin n) (Fin n) (ZMod p))
    (hsplit : D.charpoly.Splits) (hdet : D.det ≠ 0) :
    D ^ (p ^ n * (p - 1)) = 1 := by
  have h1 := splits_dvd_pow D hsplit hdet
  have h2 : (X ^ (p - 1) - 1 : (ZMod p)[X]) ^ n ∣ X ^ (p ^ n * (p - 1)) - 1 := by
    have : (X ^ (p ^ n * (p - 1)) - 1 : (ZMod p)[X]) = (X ^ (p - 1) - 1) ^ (p ^ n) := by
      rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm]
    rw [this]
    exact pow_dvd_pow _ (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  obtain ⟨q, hq⟩ := h1.trans h2
  have := congrArg (aeval D) hq
  rw [map_mul, aeval_self_charpoly, zero_mul] at this
  simpa [sub_eq_zero] using this

/-- **Split charpoly ⇒ periodic power traces.**  If the charpoly of `C` splits mod `p` and `c`
is coprime to `p (p − 1)`, then `tr C^(c^m) mod p` is purely periodic in `m`. -/
theorem trace_pow_periodic_of_splits {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p c : ℕ}
    (hp : p.Prime) (hc : Nat.Coprime c (p * (p - 1)))
    (hsplit : (C.map (Int.castRingHom (ZMod p))).charpoly.Splits)
    (hdet : ¬ (p : ℤ) ∣ C.det) :
    ∃ J, 1 ≤ J ∧ ∀ m, (C ^ (c ^ (m + J))).trace ≡ (C ^ (c ^ m)).trace [ZMOD p] := by
  haveI := Fact.mk hp
  set D := C.map (Int.castRingHom (ZMod p)) with hD
  have hDdet : D.det ≠ 0 := by
    rw [hD, show (C.map (Int.castRingHom (ZMod p))).det = Int.castRingHom (ZMod p) C.det from
      (RingHom.map_det _ _).symm]
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hdet
  set N := p ^ n * (p - 1) with hN
  have hDN : D ^ N = 1 := pow_eq_one_of_splits D hsplit hDdet
  have hcN : Nat.Coprime c N := by
    rw [hN]
    have hc1 := Nat.Coprime.coprime_dvd_right (dvd_mul_right p (p - 1)) hc
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hc1)
      (Nat.Coprime.coprime_dvd_right (dvd_mul_left (p - 1) p) hc)
  have hNpos : 0 < N := Nat.mul_pos (pow_pos hp.pos _) (by have := hp.two_le; omega)
  refine ⟨N.totient, Nat.totient_pos.2 hNpos, fun m => ?_⟩
  have hmod : c ^ (m + N.totient) % N = c ^ m % N := by
    have := (Nat.ModEq.pow_totient hcN).mul_left (c ^ m)
    rw [mul_one, ← pow_add] at this
    exact this
  rw [← ZMod.intCast_eq_intCast_iff]
  have htr : ∀ k, ((C ^ k).trace : ZMod p) = (D ^ k).trace := by
    intro k
    rw [hD, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, ]
    simp [Matrix.trace]
  rw [htr, htr, pow_eq_pow_mod _ hDN, hmod, ← pow_eq_pow_mod _ hDN]

/-- **The Kronecker lemma, divisibility form.**  A split prime `p ≡ 2 (mod 3)` that divides one
`tr C^(3^m)` divides a later one. -/
theorem dvd_trace_of_splits_mod {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {p m : ℕ}
    (hp : p.Prime) (hp3 : p % 3 = 2)
    (hsplit : (C.map (Int.castRingHom (ZMod p))).charpoly.Splits)
    (hdiv : (p : ℤ) ∣ (C ^ (3 ^ m)).trace) (hdet : ¬ (p : ℤ) ∣ C.det) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (C ^ (3 ^ (m + j))).trace := by
  have hc : Nat.Coprime 3 (p * (p - 1)) := by
    have h2 := hp.two_le
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h <;> omega
  obtain ⟨J, hJ, hper⟩ := trace_pow_periodic_of_splits C hp hc hsplit hdet
  exact ⟨J, hJ, (Int.ModEq.dvd_iff (hper m) |>.2 hdiv)⟩

/-- If `t_k = tr C^(c^k)` is eventually prime and increasing, the charpoly eventually does not
split mod any `t_k` with `c` coprime to `t_k (t_k − 1)`. -/
theorem not_splits_mod_eventually {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (hdet : C.det ≠ 0)
    {c k₀ : ℕ} (hc : 2 ≤ c) (hprime : ∀ k ≥ k₀, Prime (C ^ (c ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (c ^ k)).trace < (C ^ (c ^ (k + 1))).trace) :
    ∀ᶠ k in atTop,
      Nat.Coprime c ((C ^ (c ^ k)).trace.toNat * ((C ^ (c ^ k)).trace.toNat - 1)) →
      ¬ (C.map (Int.castRingHom (ZMod (C ^ (c ^ k)).trace.toNat))).charpoly.Splits := by
  set t : ℕ → ℤ := fun k => (C ^ (c ^ k)).trace with ht
  have hmono' : ∀ k, k₀ ≤ k → t k < t (k + 1) := fun k hk => hmono k hk
  have growth : ∀ k, k₀ ≤ k → t k₀ + ((k : ℤ) - (k₀ : ℤ)) ≤ t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        have := hmono' k hk
        push_cast
        omega
  have hle : ∀ a, k₀ ≤ a → ∀ d, t a ≤ t (a + d) := by
    intro a ha d
    induction d with
    | zero => simp
    | succ d ih =>
        have := hmono' (a + d) (by omega)
        have he : a + (d + 1) = (a + d) + 1 := by omega
        rw [he]; omega
  rw [eventually_atTop]
  refine ⟨k₀ + (|C.det| + 3 - t k₀ + 1).toNat, ?_⟩
  intro k hk hcop hspl
  have hk0 : k₀ ≤ k := by omega
  have hbig : |C.det| + 3 < t k := by
    have := growth k hk0
    have h2 : ((k₀ + (|C.det| + 3 - t k₀ + 1).toNat : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    push_cast at h2
    omega
  have htpos : 0 < t k := by have := abs_nonneg C.det; omega
  have htprime : Prime (t k) := hprime k hk0
  obtain ⟨p, hpv⟩ : ∃ p : ℕ, (p : ℤ) = t k := ⟨(t k).toNat, Int.toNat_of_nonneg htpos.le⟩
  have hpnat : p.Prime := by
    rw [Int.prime_iff_natAbs_prime] at htprime
    simpa [← hpv] using htprime
  have hptoNat : (t k).toNat = p := by omega
  have hdvd : (p : ℤ) ∣ (C ^ (c ^ k)).trace := by rw [hpv]
  have hdetp : ¬ (p : ℤ) ∣ C.det := by
    intro h
    have h1 : (p : ℤ) ≤ |C.det| := Int.le_of_dvd (abs_pos.2 hdet) ((dvd_abs _ _).2 h)
    omega
  change Nat.Coprime c ((t k).toNat * ((t k).toNat - 1)) at hcop
  change (C.map (Int.castRingHom (ZMod (t k).toNat))).charpoly.Splits at hspl
  rw [hptoNat] at hcop hspl
  obtain ⟨J, hJ, hper⟩ := trace_pow_periodic_of_splits C hpnat hcop hspl hdetp
  have hjd : (p : ℤ) ∣ t (k + J) := (Int.ModEq.dvd_iff (hper k)).2 hdvd
  have hgt : t k < t (k + J) := by
    have h1 := hmono' k hk0
    have h2 := hle (k + 1) (by omega) (J - 1)
    have he : k + 1 + (J - 1) = k + J := by omega
    rw [he] at h2
    omega
  have hqpos : 0 < t (k + J) := lt_trans htpos hgt
  have hqprime : Prime (t (k + J)) := hprime (k + J) (by omega)
  obtain ⟨q, hqv⟩ : ∃ q : ℕ, (q : ℤ) = t (k + J) := ⟨(t (k+J)).toNat, Int.toNat_of_nonneg hqpos.le⟩
  have hqnat : q.Prime := by
    rw [Int.prime_iff_natAbs_prime] at hqprime
    simpa [← hqv] using hqprime
  have hdq : p ∣ q := by
    have : (p : ℤ) ∣ (q : ℤ) := by rw [hqv]; exact hjd
    exact_mod_cast this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hqnat p hdq) with h | h
  · exact hpnat.one_lt.ne' h
  · omega

/-- **A cubic with a root and a square discriminant splits** (odd characteristic). -/
theorem splits_of_isSquare_disc {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b c : ZMod p}
    (hdisc : a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c ≠ 0)
    (hsq : IsSquare (a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c))
    (hroot : ∃ r : ZMod p, r ^ 3 + a * r ^ 2 + b * r + c = 0) :
    (X ^ 3 + Polynomial.C a * X ^ 2 + Polynomial.C b * X + Polynomial.C c : (ZMod p)[X]).Splits := by
  obtain ⟨r, hr⟩ := hroot
  obtain ⟨s, hs⟩ := hsq
  set u := a + r
  set v := b + r * u
  have hc : c = -(r * v) := by simp only [v, u]; linear_combination hr
  have hid : a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c =
      (u ^ 2 - 4 * v) * (r ^ 2 + u * r + v) ^ 2 := by
    rw [hc]; simp only [v, u]; ring
  have he : r ^ 2 + u * r + v ≠ 0 := by
    intro h; apply hdisc; rw [hid, h]; ring
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  set w := s / (r ^ 2 + u * r + v)
  have hw : w ^ 2 = u ^ 2 - 4 * v := by
    simp only [w]; rw [div_pow, div_eq_iff (pow_ne_zero 2 he)]
    linear_combination hs.symm.trans hid
  set s1 := (-u + w) / 2
  set s2 := (-u - w) / 2
  have hsum : s1 + s2 = -u := by simp only [s1, s2]; field_simp; ring
  have hprod : s1 * s2 = v := by
    simp only [s1, s2]; field_simp; linear_combination (-1 : ZMod p) * hw
  have ha : a = -(r + s1 + s2) := by
    rw [add_assoc, hsum]; simp only [u]; ring
  have hb : b = r * (s1 + s2) + s1 * s2 := by rw [hsum, hprod]; simp only [v]; ring
  have hc' : c = -(r * (s1 * s2)) := by rw [hprod, hc]
  have : (X ^ 3 + Polynomial.C a * X ^ 2 + Polynomial.C b * X + Polynomial.C c : (ZMod p)[X]) =
      (X + Polynomial.C (-r)) * (X + Polynomial.C (-s1)) * (X + Polynomial.C (-s2)) := by
    rw [ha, hb, hc']; simp only [map_neg, map_add, map_mul]; ring
  rw [this]
  exact ((Splits.X_add_C _).mul (Splits.X_add_C _)).mul (Splits.X_add_C _)

open Filter in

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

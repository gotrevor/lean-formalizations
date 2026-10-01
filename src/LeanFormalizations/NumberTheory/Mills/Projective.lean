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

/-! ### Two arithmetic helpers -/

private lemma exists_algebraMap_eq_of_pow_eq {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]
    (z : K) (h : z ^ p = z) : ∃ a : ZMod p, algebraMap (ZMod p) K a = z := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set P : K[X] := X ^ p - X with hP
  have hPne : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp1
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq K hp1
  set T : Finset K := Finset.univ.image (algebraMap (ZMod p) K) with hT
  have hinj : Function.Injective (algebraMap (ZMod p) K) := (algebraMap (ZMod p) K).injective
  have hTcard : T.card = p := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hTsub : T ⊆ P.roots.toFinset := by
    intro x hx
    simp only [hT, Finset.mem_image] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots hPne]
    simp [hP, IsRoot, ← map_pow, ZMod.pow_card]
  have hz : z ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hPne]
    simp [hP, IsRoot, h]
  have hcard : P.roots.toFinset.card ≤ p := by
    calc P.roots.toFinset.card ≤ Multiset.card P.roots := P.roots.toFinset_card_le
      _ ≤ P.natDegree := P.card_roots'
      _ = p := hdeg
  have hTeq : T = P.roots.toFinset := Finset.eq_of_subset_of_card_le hTsub (by omega)
  rw [← hTeq, hT, Finset.mem_image] at hz
  obtain ⟨a, -, ha⟩ := hz
  exact ⟨a, ha⟩

private lemma not_nine_dvd (p : ℕ) : ¬ (9 ∣ p ^ 2 + p + 1) := by
  intro hdvd
  have h0 : ((p : ZMod 9) ^ 2 + (p : ZMod 9) + 1) = 0 := by
    have : ((p ^ 2 + p + 1 : ℕ) : ZMod 9) = 0 := (CharP.cast_eq_zero_iff (ZMod 9) 9 _).2 hdvd
    push_cast at this
    exact this
  revert h0
  generalize (p : ZMod 9) = z
  revert z
  decide


private lemma trace_gt_of_mono {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {k₀ : ℕ}
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) (B : ℤ) :
    ∃ K, k₀ ≤ K ∧ ∀ k ≥ K, B < (C ^ (3 ^ k)).trace := by
  set t : ℕ → ℤ := fun k => (C ^ (3 ^ k)).trace with ht
  have hmono' : ∀ k, k₀ ≤ k → t k < t (k + 1) := fun k hk => hmono k hk
  have growth : ∀ k, k₀ ≤ k → t k₀ + ((k : ℤ) - (k₀ : ℤ)) ≤ t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        have := hmono' k hk
        push_cast
        push_cast at ih
        omega
  refine ⟨k₀ + (B - t k₀ + 1).toNat, by omega, ?_⟩
  intro k hk
  show B < t k
  have := growth k (by omega)
  have h2 : ((k₀ + (B - t k₀ + 1).toNat : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  push_cast at h2
  omega

/-! ### The projective-order lemma -/

/-- **Astra's lemma.**  Irreducible reduction mod `p ≠ 3` plus `p ∣ tr C^(3^m)` with `m ≥ 1`
forces `p ∣ tr C^(3^(m+j))` for some `j ≥ 1`. -/
theorem dvd_trace_of_irreducible_mod (C : Matrix (Fin 3) (Fin 3) ℤ) {p m : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hirr : Irreducible (C.map (Int.castRingHom (ZMod p))).charpoly)
    (hm : 1 ≤ m) (hdiv : (p : ℤ) ∣ (C ^ (3 ^ m)).trace) (hdet : ¬ (p : ℤ) ∣ C.det) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (C ^ (3 ^ (m + j))).trace := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Matrix (Fin 3) (Fin 3) (ZMod p) := C.map (Int.castRingHom (ZMod p)) with hD
  set F : (ZMod p)[X] := D.charpoly with hF
  haveI : Fact (Irreducible F) := ⟨hirr⟩
  have hFdeg : F.natDegree = 3 := by
    rw [hF, Matrix.charpoly_natDegree_eq_dim]; simp
  have hFne : F ≠ 0 := (Matrix.charpoly_monic D).ne_zero
  set K := AdjoinRoot F with hK
  letI pb : PowerBasis (ZMod p) K := AdjoinRoot.powerBasis hFne
  haveI : Module.Finite (ZMod p) K := Module.Finite.of_basis pb.basis
  letI : Fintype K := Module.fintypeOfFintype pb.basis
  have hcard : Fintype.card K = p ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := K), ZMod.card, pb.finrank,
      AdjoinRoot.powerBasis_dim, hFdeg]
  have hx : (AdjoinRoot.root F) ≠ 0 := by
    intro h
    have : F ∣ (X : (ZMod p)[X]) := by
      rw [← AdjoinRoot.mk_eq_zero, AdjoinRoot.mk_X]; exact h
    have := Polynomial.natDegree_le_of_dvd this X_ne_zero
    rw [hFdeg, natDegree_X] at this
    omega
  set x : K := AdjoinRoot.root F with hxdef
  set X1 : Kˣ := Units.mk0 x hx with hX1
  set S : Subgroup Kˣ :=
    MonoidHom.range (Units.map (algebraMap (ZMod p) K : (ZMod p) →+* K).toMonoidHom) with hS
  set Q := p ^ 2 + p + 1 with hQdef
  -- scalars: any Q-th power is a scalar
  have hscal : ∀ u : Kˣ, u ^ Q ∈ S := by
    intro u
    obtain ⟨a, ha⟩ : ∃ a : ZMod p, algebraMap (ZMod p) K a = (u : K) ^ Q := by
      refine exists_algebraMap_eq_of_pow_eq _ ?_
      have hz : ((u : K)) ^ (p ^ 3) = (u : K) := by
        rw [← hcard]; exact FiniteField.pow_card _
      rw [← pow_mul]
      calc ((u : K)) ^ (Q * p) = ((u:K) ^ (p ^ 3)) * ((u:K) ^ (p ^ 2 + p)) := by
            rw [← pow_add]; congr 1; rw [hQdef]; ring
        _ = (u:K) ^ (p ^ 2 + p + 1) := by rw [hz, ← pow_succ']
        _ = (u:K) ^ Q := by rw [hQdef]
    have ha0 : a ≠ 0 := by
      intro h; rw [h, map_zero] at ha
      exact (pow_ne_zero Q u.ne_zero) ha.symm
    refine ⟨(Ne.isUnit ha0).unit, ?_⟩
    ext
    simpa [IsUnit.unit_spec] using ha
  set π := QuotientGroup.mk' S with hπ
  set e := orderOf (π X1) with he
  have heQ : e ∣ Q := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (hscal X1)
  have hnine : ¬ (9 ∣ e) := fun h => not_nine_dvd p (h.trans heQ)
  set d := orderOf ((π X1) ^ (3 ^ m)) with hd
  have hdvd_e : d ∣ e := orderOf_pow_dvd _
  have hgcd : d * Nat.gcd e (3 ^ m) = e := by
    rw [hd, orderOf_pow' _ (by positivity), ← he]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have h3d : ¬ (3 ∣ d) := by
    intro h3
    have h3e : (3:ℕ) ∣ e := h3.trans hdvd_e
    have h3g : (3:ℕ) ∣ Nat.gcd e (3 ^ m) :=
      Nat.dvd_gcd h3e (dvd_pow_self 3 (by omega))
    exact hnine (hgcd ▸ mul_dvd_mul h3 h3g)
  have hdpos : 0 < d := orderOf_pos _
  set j := Nat.totient d with hj
  have hjpos : 1 ≤ j := Nat.totient_pos.2 hdpos
  have hcop : Nat.Coprime 3 d := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h3d
  obtain ⟨s, hs⟩ : ∃ s, 3 ^ j = 1 + d * s := by
    have hmod : 3 ^ j ≡ 1 [MOD d] := Nat.ModEq.pow_totient hcop
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h1).1 hmod.symm
    exact ⟨t, by omega⟩
  have hfix : ((π X1) ^ (3 ^ m)) ^ (3 ^ j) = (π X1) ^ (3 ^ m) := by
    rw [hs, pow_add, pow_one, pow_mul, pow_orderOf_eq_one, one_pow, mul_one]
  have hmk : π (X1 ^ (3 ^ (m + j))) = π (X1 ^ (3 ^ m)) := by
    rw [map_pow, map_pow, pow_add, pow_mul, hfix]
  obtain ⟨z, hzS, hzeq⟩ := (QuotientGroup.mk'_eq_mk' (N := S)).1 hmk.symm
  obtain ⟨a, ha⟩ := hzS
  -- the scalar identity in K
  have hKey : x ^ (3 ^ (m + j)) = algebraMap (ZMod p) K (a : ZMod p) * x ^ (3 ^ m) := by
    have := congrArg (fun u : Kˣ => (u : K)) hzeq
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hX1, Units.val_mk0] at this
    rw [← this, ← ha]
    simp [mul_comm]
  set lam : ZMod p := (a : ZMod p) with hlam
  set P : (ZMod p)[X] := X ^ (3 ^ (m + j)) - Polynomial.C lam * X ^ (3 ^ m) with hP
  have hPdvd : F ∣ P := by
    rw [← AdjoinRoot.mk_eq_zero, hP]
    simp only [map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, ← hxdef]
    rw [hKey]
    rw [AdjoinRoot.algebraMap_eq]
    ring
  have haev : (Polynomial.aeval D) P = 0 := by
    obtain ⟨R, hR⟩ := hPdvd
    rw [hR, map_mul, hF, Matrix.aeval_self_charpoly, zero_mul]
  have hmat : D ^ (3 ^ (m + j)) = lam • D ^ (3 ^ m) := by
    have hexp : (Polynomial.aeval D) P = D ^ (3 ^ (m + j)) - lam • D ^ (3 ^ m) := by
      simp [hP, Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
    rw [hexp] at haev
    linear_combination (norm := module) haev
  -- traces
  have htr : ∀ N : ℕ, ((C ^ N).trace : ZMod p) = (D ^ N).trace := by
    intro N
    have hDp : D ^ N = ((Int.castRingHom (ZMod p)).mapMatrix) (C ^ N) := by
      rw [hD, ← RingHom.mapMatrix_apply, ← map_pow]
    rw [hDp]
    simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply, Matrix.map_apply]
  have h0 : (D ^ (3 ^ m)).trace = 0 := by
    rw [← htr]
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hdiv
  have hfin : (D ^ (3 ^ (m + j))).trace = 0 := by
    rw [hmat, Matrix.trace_smul, h0, smul_zero]
  have : ((C ^ (3 ^ (m + j))).trace : ZMod p) = 0 := by rw [htr]; exact hfin
  have hout : (p : ℤ) ∣ (C ^ (3 ^ (m + j))).trace :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  exact ⟨j, hjpos, hout⟩

/-- If `t_k = tr C^(3^k)` is eventually prime and increasing, the charpoly is eventually
reducible mod `t_k`. -/
theorem not_irreducible_mod_eventually (C : Matrix (Fin 3) (Fin 3) ℤ) (hdet : C.det ≠ 0)
    {k₀ : ℕ} (hprime : ∀ k ≥ k₀, Prime (C ^ (3 ^ k)).trace)
    (hmono : ∀ k ≥ k₀, (C ^ (3 ^ k)).trace < (C ^ (3 ^ (k + 1))).trace) :
    ∀ᶠ k in atTop,
      ¬ Irreducible (C.map (Int.castRingHom (ZMod (C ^ (3 ^ k)).trace.toNat))).charpoly := by
  set t : ℕ → ℤ := fun k => (C ^ (3 ^ k)).trace with ht
  have hmono' : ∀ k, k₀ ≤ k → t k < t (k + 1) := fun k hk => hmono k hk
  have hle : ∀ a, k₀ ≤ a → ∀ d, t a ≤ t (a + d) := by
    intro a ha d
    induction d with
    | zero => simp
    | succ d ih =>
        have := hmono' (a + d) (by omega)
        have he : a + (d + 1) = (a + d) + 1 := by omega
        rw [he]; omega
  obtain ⟨K, hK0, hKB⟩ := trace_gt_of_mono C hmono (|C.det| + 3)
  rw [eventually_atTop]
  refine ⟨max K 1, ?_⟩
  intro k hk hirr
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hk0 : k₀ ≤ k := le_trans hK0 hkK
  have hbig : |C.det| + 3 < t k := hKB k hkK
  have htpos : 0 < t k := by have := abs_nonneg C.det; omega
  have htprime : Prime (t k) := hprime k hk0
  obtain ⟨p, hpv⟩ : ∃ p : ℕ, (p : ℤ) = t k := ⟨(t k).toNat, Int.toNat_of_nonneg htpos.le⟩
  have hpnat : p.Prime := by
    rw [Int.prime_iff_natAbs_prime] at htprime
    simpa [← hpv] using htprime
  have hptoNat : (t k).toNat = p := by omega
  have hp3 : p ≠ 3 := by
    intro h; rw [h] at hpv; have := abs_nonneg C.det; omega
  have hdvd : (p : ℤ) ∣ (C ^ (3 ^ k)).trace := by rw [hpv]
  have hdetp : ¬ (p : ℤ) ∣ C.det := by
    intro h
    have h1 : (p : ℤ) ≤ |C.det| := Int.le_of_dvd (abs_pos.2 hdet) ((dvd_abs _ _).2 h)
    omega
  rw [hptoNat] at hirr
  obtain ⟨j, hj1, hjd⟩ := dvd_trace_of_irreducible_mod C hpnat hp3 hirr hk1 hdvd hdetp
  have hgt : t k < t (k + j) := by
    have h1 := hmono' k hk0
    have h2 := hle (k + 1) (by omega) (j - 1)
    have he : k + 1 + (j - 1) = k + j := by omega
    rw [he] at h2
    omega
  have hqpos : 0 < t (k + j) := lt_trans htpos hgt
  have hqprime : Prime (t (k + j)) := hprime (k + j) (by omega)
  obtain ⟨q, hqv⟩ : ∃ q : ℕ, (q : ℤ) = t (k + j) := ⟨(t (k+j)).toNat, Int.toNat_of_nonneg hqpos.le⟩
  have hqnat : q.Prime := by
    rw [Int.prime_iff_natAbs_prime] at hqprime
    simpa [← hqv] using hqprime
  have hdq : p ∣ q := by
    have : (p : ℤ) ∣ (q : ℤ) := by rw [hqv]; exact hjd
    exact_mod_cast this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hqnat p hdq) with h | h
  · exact hpnat.one_lt.ne' h
  · omega

/-- **A one-prime certificate.**  If some prime `q ≠ 3` at which the charpoly stays irreducible
divides a single `t_m` with `m ≥ 1`, then `t_k` is not prime for infinitely many `k`. -/
theorem composite_of_irreducible_divisor (C : Matrix (Fin 3) (Fin 3) ℤ) {q m : ℕ}
    (hq : q.Prime) (hq3 : q ≠ 3) (hirr : Irreducible (C.map (Int.castRingHom (ZMod q))).charpoly)
    (hm : 1 ≤ m) (hdiv : (q : ℤ) ∣ (C ^ (3 ^ m)).trace) (hdet : ¬ (q : ℤ) ∣ C.det)
    (hgrow : Tendsto (fun k : ℕ => (C ^ (3 ^ k)).trace) atTop atTop) :
    ∃ᶠ k in atTop, ¬ Prime (C ^ (3 ^ k)).trace := by
  set t : ℕ → ℤ := fun k => (C ^ (3 ^ k)).trace with ht
  -- `q` divides `t` at arbitrarily late indices
  have hrec : ∀ n : ℕ, ∃ k, n ≤ k ∧ 1 ≤ k ∧ (q : ℤ) ∣ t k := by
    intro n
    induction n with
    | zero => exact ⟨m, Nat.zero_le _, hm, hdiv⟩
    | succ n ih =>
        obtain ⟨k, hkn, hk1, hkd⟩ := ih
        obtain ⟨j, hj1, hjd⟩ := dvd_trace_of_irreducible_mod C hq hq3 hirr hk1 hkd hdet
        exact ⟨k + j, by omega, by omega, hjd⟩
  -- eventually the traces exceed `q`
  have hgt : ∀ᶠ k in atTop, (q : ℤ) < t k := hgrow.eventually_gt_atTop (q : ℤ)
  rw [eventually_atTop] at hgt
  obtain ⟨N₁, hN₁⟩ := hgt
  rw [frequently_atTop]
  intro N
  obtain ⟨k, hkN, hk1, hkd⟩ := hrec (max N N₁)
  refine ⟨k, le_trans (le_max_left _ _) hkN, ?_⟩
  intro hprime
  have hbig : (q : ℤ) < t k := hN₁ k (le_trans (le_max_right _ _) hkN)
  have hqpos : (0:ℤ) < q := by exact_mod_cast hq.pos
  have htp : (t k).natAbs.Prime := Int.prime_iff_natAbs_prime.1 hprime
  have hqd : q ∣ (t k).natAbs := by
    have : (q:ℤ) ∣ ((t k).natAbs : ℤ) := by
      rwa [Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ t k)]
    exact_mod_cast this
  have habs : ((t k).natAbs : ℤ) = t k := Int.natAbs_of_nonneg (by omega)
  rcases htp.eq_one_or_self_of_dvd q hqd with h | h
  · exact absurd h hq.one_lt.ne'
  · rw [← h] at habs; omega

/-! ### The Mills corollary -/

private lemma companion3_charpoly (a b c : ℤ) :
    (companion3 a b c).charpoly
      = X ^ 3 + Polynomial.C a * X ^ 2 + Polynomial.C b * X + Polynomial.C c := by
  simp [Matrix.charpoly, Matrix.charmatrix, companion3, Matrix.det_fin_three,
    Matrix.diagonal, Matrix.of_apply]
  ring

private lemma exists_vieta_of_cubic_pisot' {β : ℝ} (hP : IsPisot β)
    (h3 : (minpoly ℚ β).natDegree = 3) {u v : ℂ} (huv : otherConj β = {u, v}) :
    ∃ a b c : ℤ, c ≠ 0 ∧ (β : ℂ) + u + v = -(a : ℂ) ∧
      (β : ℂ) * u + (β : ℂ) * v + u * v = (b : ℂ) ∧ (β : ℂ) * u * v = -(c : ℂ) := by
  classical
  have hZ : IsIntegral ℤ β := hP.2.1
  have hQ : IsIntegral ℚ β := hZ.tower_top
  obtain ⟨g, hg⟩ : ∃ g, g = minpoly ℤ β := ⟨_, rfl⟩
  have hmap : minpoly ℚ β = g.map (algebraMap ℤ ℚ) := by
    rw [hg]; exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hZ
  -- the split form over `ℂ`
  have hmonic : ((minpoly ℚ β).map (algebraMap ℚ ℂ)).Monic := (minpoly.monic hQ).map _
  have hsplit : ((minpoly ℚ β).map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  have hroots : ((minpoly ℚ β).map (algebraMap ℚ ℂ)).roots = (β : ℂ) ::ₘ u ::ₘ {v} := by
    have hcons : (minpoly ℚ β).aroots ℂ = (β : ℂ) ::ₘ otherConj β :=
      (Multiset.cons_erase (beta_mem_aroots hQ)).symm
    have : (minpoly ℚ β).aroots ℂ = ((minpoly ℚ β).map (algebraMap ℚ ℂ)).roots := rfl
    rw [← this, hcons, huv]
    rfl
  have hfC : (minpoly ℚ β).map (algebraMap ℚ ℂ)
      = (X - C (β : ℂ)) * (X - C u) * (X - C v) := by
    rw [hsplit.eq_prod_roots_of_monic hmonic, hroots]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
      Multiset.prod_singleton]
    ring
  have hexp : ((X - C (β : ℂ)) * (X - C u) * (X - C v))
      = X ^ 3 - C ((β : ℂ) + u + v) * X ^ 2 + C ((β : ℂ) * u + (β : ℂ) * v + u * v) * X
        - C ((β : ℂ) * u * v) := by
    simp only [map_add, map_mul]
    ring
  have hcoeff : ∀ k, ((g.coeff k : ℤ) : ℂ) =
      (X ^ 3 - C ((β : ℂ) + u + v) * X ^ 2 + C ((β : ℂ) * u + (β : ℂ) * v + u * v) * X
        - C ((β : ℂ) * u * v)).coeff k := by
    intro k
    rw [← hexp, ← hfC, hmap, Polynomial.coeff_map, Polynomial.coeff_map]
    simp
  have c2 := hcoeff 2
  have c1 := hcoeff 1
  have c0 := hcoeff 0
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X] at c2 c1 c0
  norm_num at c2 c1 c0
  -- the constant term is nonzero
  have hc0 : g.coeff 0 ≠ 0 := by
    intro h0
    have hq0 : (minpoly ℚ β).coeff 0 = 0 := by rw [hmap, Polynomial.coeff_map, h0]; simp
    obtain ⟨q, hq⟩ : (X : ℚ[X]) ∣ minpoly ℚ β := Polynomial.X_dvd_iff.2 hq0
    have hirr := minpoly.irreducible hQ
    rcases hirr.isUnit_or_isUnit hq with hu' | hu'
    · exact Polynomial.not_isUnit_X hu'
    · have hqne : q ≠ 0 := by
        intro h; rw [h, mul_zero] at hq; exact minpoly.ne_zero hQ hq
      have hdeg : (minpoly ℚ β).natDegree = 1 := by
        rw [hq, Polynomial.natDegree_mul Polynomial.X_ne_zero hqne, Polynomial.natDegree_X,
          Polynomial.natDegree_eq_zero_of_isUnit hu']
      omega
  exact ⟨g.coeff 2, g.coeff 1, g.coeff 0, hc0, by linear_combination c2, by linear_combination -c1,
    by linear_combination c0⟩

/-- `exists_companion_root` together with the Vieta data of the charpoly: its three complex
roots `A^(3^m), u, v` are pairwise distinct (phase 60, for the discriminant). -/
theorem exists_companion_root_vieta (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A)
    (halg : IsAlgebraic ℚ A) :
    ∃ (C : Matrix (Fin 3) (Fin 3) ℤ) (m i₀ : ℕ), C.det ≠ 0 ∧
      (C.charpoly.map (Int.castRingHom ℝ)).IsRoot (A ^ ((3:ℕ) ^ m)) ∧
      (∀ i ≥ i₀, ((C ^ ((3:ℕ) ^ i)).trace) = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ)) ∧
      (∀ k ≥ i₀, Prime ((C ^ ((3:ℕ) ^ k)).trace)) ∧
      (∀ k ≥ i₀, (C ^ ((3:ℕ) ^ k)).trace < (C ^ ((3:ℕ) ^ (k + 1))).trace) ∧
      ∃ u v : ℂ, ((A ^ ((3:ℕ) ^ m) : ℝ) : ℂ) ≠ u ∧ ((A ^ ((3:ℕ) ^ m) : ℝ) : ℂ) ≠ v ∧ u ≠ v ∧
        ((C.charpoly.coeff 2 : ℤ) : ℂ) = -(((A ^ ((3:ℕ) ^ m) : ℝ) : ℂ) + u + v) ∧
        ((C.charpoly.coeff 1 : ℤ) : ℂ) = ((A ^ ((3:ℕ) ^ m) : ℝ) : ℂ) * u +
          ((A ^ ((3:ℕ) ^ m) : ℝ) : ℂ) * v + u * v ∧
        ((C.charpoly.coeff 0 : ℤ) : ℂ) = -(((A ^ ((3:ℕ) ^ m) : ℝ) : ℂ) * u * v) := by
  obtain ⟨⟨hA1, hAm⟩, hmin⟩ := hA
  have hA : IsMinMills A := ⟨⟨hA1, hAm⟩, hmin⟩
  -- Saito's dichotomy; the transcendental branch contradicts `halg`
  rcases transcendental_or_pisot hB hM hD hG hA with htr | ⟨m, hm, hP, h3⟩
  · exact absurd halg htr
  set β : ℝ := A ^ ((3:ℕ) ^ m) with hβdef
  have hint : IsIntegral ℚ β := hP.2.1.tower_top
  -- the two other conjugates
  have hc2 : Multiset.card (otherConj β) = 2 := by
    have := card_otherConj_add_one hint; omega
  obtain ⟨u, v, huv⟩ := Multiset.card_eq_two.1 hc2
  obtain ⟨a, b, c, hcne, hvi1, hvi2, hvi3⟩ := exists_vieta_of_cubic_pisot' hP h3 huv
  obtain ⟨C, hCdef⟩ : ∃ C, C = companion3 a b c := ⟨_, rfl⟩
  have hdet : C.det ≠ 0 := by rw [hCdef, companion3_det]; omega
  have htrace : ∀ N : ℕ, (((C ^ N).trace : ℤ) : ℂ) = (β : ℂ) ^ N + u ^ N + v ^ N := by
    intro N; rw [hCdef]; exact companion3_trace_pow hvi1 hvi2 hvi3 N
  -- the Mills digit facts
  have h36 := saito_lemma36C (c := 3) hB hM (by norm_num) hA
  have hμ0 : (0:ℝ) < (19 * ((3:ℕ):ℝ)) / 40 - 1 := by norm_num
  have hK0 : (0:ℝ) < (2:ℝ) ^ ((19 * ((3:ℕ):ℝ)) / 40) := Real.rpow_pos_of_pos (by norm_num) _
  have hfrac : ∀ᶠ k : ℕ in atTop, A ^ ((3:ℕ) ^ k) - (⌊A ^ ((3:ℕ) ^ k)⌋₊ : ℝ) < 1 / 2 := by
    filter_upwards [decay_of_lemma36C (c := 3) (by norm_num) hA1 hAm h36,
      eventually_rpow_neg_lt (c := 3) hA1 (by norm_num) hμ0 hK0 (by norm_num : (0:ℝ) < 1 / 2)]
      with k hk hk2
    exact lt_of_le_of_lt hk.2 hk2
  have hcube : ∀ k : ℕ, 1 ≤ k → (⌊A ^ ((3:ℕ) ^ k)⌋₊) ^ 3 < ⌊A ^ ((3:ℕ) ^ (k + 1))⌋₊ := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact mdigitC_pow_lt (c := 3) (by norm_num) hA1 hAm j
  -- the eventually negative conjugate power sum
  obtain ⟨i₀, hi₀⟩ := pair_pow_sum_re_neg hA1 hP huv hcube hfrac hm
  -- identify `tr C^(3^i)` with the Mills prime `⌊A^(3^(m+i))⌋₊`
  have hfloor : ∀ i ≥ i₀, ((C ^ ((3:ℕ) ^ i)).trace : ℤ) = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ) := by
    intro i hi
    obtain ⟨σ, hsu, hσneg, hσabs, hA2, -⟩ := hi₀ i hi
    have hbeta : (β : ℝ) ^ ((3:ℕ) ^ i) = A ^ ((3:ℕ) ^ (m + i)) := by
      rw [hβdef, ← pow_mul, ← pow_add]
    have hreal : (((C ^ ((3:ℕ) ^ i)).trace : ℤ) : ℝ) = A ^ ((3:ℕ) ^ (m + i)) + σ := by
      have h := htrace ((3:ℕ) ^ i)
      rw [add_assoc, hsu] at h
      have h2 : (((C ^ ((3:ℕ) ^ i)).trace : ℤ) : ℂ) =
          (((A ^ ((3:ℕ) ^ (m + i)) + σ : ℝ)) : ℂ) := by
        rw [h, ← hbeta]
        push_cast
        ring
      exact_mod_cast h2
    -- `σ ∈ (−1/2, 0)`, so the floor of `A^(3^(m+i))` is the trace
    have hTpos : (0:ℝ) < ((C ^ ((3:ℕ) ^ i)).trace : ℤ) := by
      rw [hreal]
      have : |σ| < 1 / 2 := hσabs
      have := abs_lt.1 this
      linarith
    obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℤ) = ((C ^ ((3:ℕ) ^ i)).trace : ℤ) :=
      ⟨((C ^ ((3:ℕ) ^ i)).trace).toNat, Int.toNat_of_nonneg (by exact_mod_cast hTpos.le)⟩
    have hTr : (T : ℝ) = A ^ ((3:ℕ) ^ (m + i)) + σ := by
      rw [← hreal]; exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hT
    have habs := abs_lt.1 hσabs
    have hfl : ⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ = T := by
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> [linarith; linarith]
    rw [hfl, ← hT]
  -- primality and monotonicity of the trace sequence
  have hprime : ∀ k ≥ i₀, Prime ((C ^ ((3:ℕ) ^ k)).trace) := by
    intro k hk
    rw [hfloor k hk]
    have : Prime ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ := hAm ⟨m + k, by omega⟩
    exact_mod_cast Nat.prime_iff_prime_int.1 (Nat.prime_iff.2 this)
  have hmono : ∀ k ≥ i₀, (C ^ ((3:ℕ) ^ k)).trace < (C ^ ((3:ℕ) ^ (k + 1))).trace := by
    intro k hk
    rw [hfloor k hk, hfloor (k + 1) (by omega)]
    have hcu := hcube (m + k) (by omega)
    have hk2 : 2 ≤ ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ := (Nat.prime_iff.2 (hAm ⟨m + k, by omega⟩)).two_le
    have hmk : m + (k + 1) = (m + k) + 1 := by omega
    rw [hmk]
    have : ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ < ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ ^ 3 := by
      calc ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ = ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ ^ 1 := (pow_one _).symm
        _ < ⌊A ^ ((3:ℕ) ^ (m + k))⌋₊ ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
    exact_mod_cast lt_trans this hcu
  have hrootC : (C.charpoly.map (Int.castRingHom ℝ)).IsRoot (A ^ ((3:ℕ) ^ m)) := by
    have hcx : ((β:ℂ)) ^ 3 + (a:ℂ) * (β:ℂ) ^ 2 + (b:ℂ) * (β:ℂ) + (c:ℂ) = 0 := by
      linear_combination (β:ℂ) ^ 2 * hvi1 - (β:ℂ) * hvi2 + hvi3
    have hrx : (β:ℝ) ^ 3 + (a:ℝ) * (β:ℝ) ^ 2 + (b:ℝ) * (β:ℝ) + (c:ℝ) = 0 := by
      exact_mod_cast hcx
    rw [hCdef, companion3_charpoly]
    simp only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [← hβdef]
    simpa using hrx
  have hnodup : ((β : ℂ) ::ₘ u ::ₘ {v}).Nodup := by
    have hsep : ((minpoly ℚ β).map (algebraMap ℚ ℂ)).Separable :=
      (Irreducible.separable (minpoly.irreducible hint)).map
    have hcons : (minpoly ℚ β).aroots ℂ = (β : ℂ) ::ₘ otherConj β :=
      (Multiset.cons_erase (beta_mem_aroots hint)).symm
    have h := nodup_roots hsep
    have : (minpoly ℚ β).aroots ℂ = ((minpoly ℚ β).map (algebraMap ℚ ℂ)).roots := rfl
    rw [← this, hcons, huv] at h
    exact h
  have hd : (β : ℂ) ≠ u ∧ (β : ℂ) ≠ v ∧ u ≠ v := by
    simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or,
      Multiset.nodup_singleton, and_true] at hnodup
    exact ⟨hnodup.1.1, hnodup.1.2, hnodup.2⟩
  have hcp : C.charpoly = X ^ 3 + Polynomial.C a * X ^ 2 + Polynomial.C b * X + Polynomial.C c := by
    rw [hCdef, companion3_charpoly]
  have hc2' : C.charpoly.coeff 2 = a := by rw [hcp]; simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]; norm_num
  have hc1' : C.charpoly.coeff 1 = b := by rw [hcp]; simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]; norm_num
  have hc0' : C.charpoly.coeff 0 = c := by rw [hcp]; simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]; norm_num
  refine ⟨C, m, i₀, hdet, hrootC, hfloor, hprime, hmono, u, v, hd.1, hd.2.1, hd.2.2, ?_, ?_, ?_⟩
  · rw [hc2']; linear_combination hvi1
  · rw [hc1']; linear_combination -hvi2
  · rw [hc0']; linear_combination hvi3

/-- **The companion-matrix glue for an algebraic Mills constant** (factored out of
`mills_threeAdic`, phase 30).  If the least Mills constant `A` is algebraic, there are a
nonsingular integer `3 x 3` matrix `C`, a shift `m` and a threshold `i₀` such that
`tr C^(3^i) = ⌊A^(3^(m+i))⌋` for all `i ≥ i₀`; in particular that trace sequence is prime and
strictly increasing from `i₀` on. -/
theorem exists_companion_root (hB : BakerHarmanPintz2001) (hM : Matomaki2007)
    (hD : Dubickas2022) (hG : Dubickas2022PisotGap) {A : ℝ} (hA : IsMinMills A)
    (halg : IsAlgebraic ℚ A) :
    ∃ (C : Matrix (Fin 3) (Fin 3) ℤ) (m i₀ : ℕ), C.det ≠ 0 ∧
      (C.charpoly.map (Int.castRingHom ℝ)).IsRoot (A ^ ((3:ℕ) ^ m)) ∧
      (∀ i ≥ i₀, ((C ^ ((3:ℕ) ^ i)).trace) = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ)) ∧
      (∀ k ≥ i₀, Prime ((C ^ ((3:ℕ) ^ k)).trace)) ∧
      (∀ k ≥ i₀, (C ^ ((3:ℕ) ^ k)).trace < (C ^ ((3:ℕ) ^ (k + 1))).trace) := by
  obtain ⟨C, m, i₀, h1, h2, h3, h4, h5, -⟩ := exists_companion_root_vieta hB hM hD hG hA halg
  exact ⟨C, m, i₀, h1, h2, h3, h4, h5⟩


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
  obtain ⟨C, m, i₀, hdet, hroot, hfloor, hprime, hmono⟩ :=
    exists_companion_root hB hM hD hG hA halg
  have hfl : ∀ᶠ i in atTop, ((C ^ ((3:ℕ) ^ i)).trace) = (⌊A ^ ((3:ℕ) ^ (m + i))⌋₊ : ℤ) :=
    eventually_atTop.2 ⟨i₀, hfloor⟩
  refine ⟨C, m, hroot, hfl, ?_⟩
  have h2 := not_irreducible_mod_eventually C hdet (k₀ := i₀) hprime hmono
  filter_upwards [h2, hfl] with k hk hfk
  rw [hfk, Int.toNat_natCast] at hk
  exact hk

end LeanFormalizations.Mills.Projective

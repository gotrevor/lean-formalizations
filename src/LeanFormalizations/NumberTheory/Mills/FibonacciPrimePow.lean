/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.LucasTwoPow

/-!
# Phase 34: `F(c^n) + h` is composite i.o. for every inert prime `c` and for `c = 5`

Generalizes phase 32 (Saito's Problem 1.8, `c = 2`) to the other primes `c`.  See
`SWEEP-PRIME-MODULUS.md`.

## Route (inert `c`, i.e. `c % 5 = 2 ∨ c % 5 = 3`; `c = 2` is included)
1. `fib_frobenius_inert`: `c ∣ F(c+1)` and `c ∣ F(c) + 1`.  These are the facts `A^(c+1) ≡ −I (mod c)`
   for `A = !![1,1;1,0]`.  Route: `X^2 − X − 1` is irreducible over `ZMod c` (5 is a non-residue:
   quadratic reciprocity, `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` or `legendreSym`
   lemmas; `c = 2` by `decide`), so in `K = AdjoinRoot` (a field with `c^2` elements) Frobenius
   sends the root `x` to the other root `1 − x = −x⁻¹`.  Hence `x^(c+1) = −1`, and the matrix
   statement follows through `F ∣` polynomial divisibility plus Cayley–Hamilton, as in phase 31
   `Projective.lean` (`dvd_trace_of_irreducible_mod`).  Any other correct route is fine.
2. `fib_prime_pow_succ_add`: `c^(n+1) ∣ F(c^(n+1)) + F(c^n)`.  Lift step 1:
   `A^(c+1) = −I + c·X` with `X` commuting with `A`, so `A^(c^n (c+1)) ≡ (−1)^(c^n) I (mod c^(n+1))`
   (binomial theorem, `c ∣ binom c i`).  Then take entry `(0,1)` and use
   `A^(−N)` entries (`F(−N) = (−1)^(N+1) F(N)`), or equivalently multiply through by `A^(c^n)`.
3. Filter: `SaitoFibonacci.exists_entry_pow_congr` with base `c`; the analogue of
   `two_pow_dvd_sub_or_add_of_lt_padicValNat` for an odd prime `c`:
   `v_c(p(p−1)^2(p+1)) = 2 v_c(p−1) + v_c(p+1)` and `c` divides at most one of `p ∓ 1`.
4. Contradiction as in phase 32: `s + s' ≡ 2h`; for odd `c` also `h = ±1` dies because
   `F(c^n) ≡ (−1)^n (mod c)` is a unit (from step 2 with `F(1) = 1`).  `h = 0`: `F(c^n) ∣ F(c^(n+1))`.

## Route (`c = 5`)
`5^n ∣ F(5^n)` (from `F(5m) = F(m)(25F(m)^4 ± 25F(m)^2 + 5)`, or any route), so the filter
leaves only `h = ±1`.  Those are killed by `F(4k+1) + 1 = F(2k+1) L(2k)` and
`F(4k+1) − 1 = F(2k) L(2k+1)` (`5^n ≡ 1 mod 4`), where both factors exceed 1 for large `k`.

Frozen: every statement below; statements of `SaitoFibonacci`, `LucasTwoPow`, `ThreeAdic`,
`SharedConjecture`, `Projective`, and `Literature/`.  Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.FibonacciPrimePow

open LeanFormalizations.Mills.ThreeAdic Filter Polynomial

/-! ### Step 1: Frobenius at an inert prime -/

/-- The Fibonacci recursion, read off any square root of `X^2 - X - 1`. -/
theorem pow_eq_fib {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = x + 1) (N : ℕ) :
    x ^ (N + 1) = (Nat.fib (N + 1) : R) * x + (Nat.fib N : R) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hf : (Nat.fib (N + 2) : R) = (Nat.fib N : R) + (Nat.fib (N + 1) : R) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) (Nat.fib_add_two (n := N))
      calc x ^ (N + 2) = x ^ (N + 1) * x := by ring
        _ = ((Nat.fib (N + 1) : R) * x + (Nat.fib N : R)) * x := by rw [ih]
        _ = (Nat.fib (N + 1) : R) * x ^ 2 + (Nat.fib N : R) * x := by ring
        _ = (Nat.fib (N + 2) : R) * x + (Nat.fib (N + 1) : R) := by rw [hx, hf]; ring

theorem two_not_isSquare_five : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by decide

theorem three_not_isSquare_five : ¬ IsSquare ((3 : ℕ) : ZMod 5) := by decide

/-- `5` is not a square mod an inert prime. -/
theorem five_not_isSquare {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (h5 : c % 5 = 2 ∨ c % 5 = 3) :
    ¬ IsSquare ((5 : ℕ) : ZMod c) := by
  haveI : Fact c.Prime := ⟨hc⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcast : ((c : ℕ) : ZMod 5) = ((c % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod c 5).symm
  have hns : ¬ IsSquare ((c : ℕ) : ZMod 5) := by
    rw [hcast]
    rcases h5 with h | h
    · rw [h]; exact two_not_isSquare_five
    · rw [h]; exact three_not_isSquare_five
  intro hsq
  exact hns ((ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := c)
    (by norm_num) hc2).mpr hsq)

/-- `X^2 - X - 1` has no root mod an inert prime. -/
theorem no_root_inert {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (h5 : c % 5 = 2 ∨ c % 5 = 3)
    (y : ZMod c) : y ^ 2 - y - 1 ≠ 0 := by
  haveI : Fact c.Prime := ⟨hc⟩
  intro hy
  refine five_not_isSquare hc hc2 h5 ⟨2 * y - 1, ?_⟩
  have h4 : ((5 : ℕ) : ZMod c) = 5 := by norm_cast
  rw [h4]
  linear_combination (-4 : ZMod c) * hy


/-- Every element fixed by the `p`-power map on a finite field is a scalar.  (Same proof as
`Projective.exists_algebraMap_eq_of_pow_eq`, which is private there.) -/
theorem exists_algebraMap_eq_of_pow_eq {p : ℕ} [Fact p.Prime]
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
    intro y hy
    simp only [hT, Finset.mem_image] at hy
    obtain ⟨a, -, rfl⟩ := hy
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

/-- Frobenius for Fibonacci at an inert prime: `A^(c+1) ≡ −I (mod c)`, entrywise. -/
theorem fib_frobenius_inert {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3) :
    (c : ℤ) ∣ Nat.fib (c + 1) ∧ (c : ℤ) ∣ (Nat.fib c : ℤ) + 1 := by
  rcases eq_or_ne c 2 with rfl | hc2
  · refine ⟨?_, ?_⟩ <;> decide
  haveI : Fact c.Prime := ⟨hc⟩
  have hnr := no_root_inert hc hc2 h5
  set f : (ZMod c)[X] := X ^ 2 - X - 1 with hf
  have hdeg : f.natDegree = 2 := by rw [hf]; compute_degree!
  have hirr : Irreducible f := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro y hy
    refine hnr y ?_
    have : f.eval y = 0 := hy
    rw [hf] at this
    simpa using this
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  have hfne : f ≠ 0 := hirr.ne_zero
  set K := AdjoinRoot f with hK
  letI pb : PowerBasis (ZMod c) K := AdjoinRoot.powerBasis hfne
  haveI : Module.Finite (ZMod c) K := Module.Finite.of_basis pb.basis
  letI : Fintype K := Module.fintypeOfFintype pb.basis
  set x : K := AdjoinRoot.root f with hxdef
  have hx2 : x ^ 2 = x + 1 := by
    have h0 : (AdjoinRoot.mk f) (X ^ 2 - X - 1 : (ZMod c)[X]) = 0 := by
      rw [← hf]; exact AdjoinRoot.mk_self
    simp only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, ← hxdef] at h0
    linear_combination h0
  -- linear independence of `1, x` over the prime field
  have hli : ∀ a b : ZMod c, (algebraMap (ZMod c) K a) * x + algebraMap (ZMod c) K b = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have hdvd : f ∣ (C a * X + C b : (ZMod c)[X]) := by
      rw [← AdjoinRoot.mk_eq_zero]
      simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← hxdef]
      exact hab
    by_cases ha : a = 0
    · subst ha
      simp only [map_zero, zero_mul, zero_add] at hab
      exact ⟨rfl, (map_eq_zero_iff _ (algebraMap (ZMod c) K).injective).1 hab⟩
    · exfalso
      have hne : (C a * X + C b : (ZMod c)[X]) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun q => Polynomial.coeff q 1) h0
        simp at h1
        exact ha h1
      have h2 := Polynomial.natDegree_le_of_dvd hdvd hne
      have hd1 : (C a * X + C b : (ZMod c)[X]).natDegree ≤ 1 := by compute_degree
      omega
  have hnox : ∀ a : ZMod c, algebraMap (ZMod c) K a ≠ x := by
    intro a ha
    have := hli 1 (-a) (by rw [map_one, one_mul, map_neg, ha]; ring)
    exact one_ne_zero this.1
  -- Frobenius sends `x` to the other root
  haveI : CharP K c := charP_of_injective_algebraMap (algebraMap (ZMod c) K).injective c
  haveI : ExpChar K c := ExpChar.prime hc
  have hy : (x ^ c) ^ 2 - (x ^ c) - 1 = 0 := by
    have h1 : (x ^ 2 - x - 1 : K) = 0 := by linear_combination hx2
    have h2 : ((x ^ 2 - x - 1 : K)) ^ c = 0 := by rw [h1, zero_pow hc.pos.ne']
    rw [sub_pow_char, sub_pow_char, one_pow] at h2
    have h3 : (x ^ 2 : K) ^ c = (x ^ c) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h3] at h2
    exact h2
  have hfact : (x ^ c - x) * (x ^ c - (1 - x)) = 0 := by linear_combination hy - hx2
  have hconj : x ^ c = 1 - x := by
    rcases mul_eq_zero.1 hfact with h | h
    · exfalso
      obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_pow_eq (p := c) x (by linear_combination h)
      exact hnox a ha
    · linear_combination h
  have hkey : x ^ (c + 1) = -1 := by
    have : x ^ (c + 1) = x * x ^ c := by ring
    rw [this, hconj]
    linear_combination -hx2
  -- read off the two coefficients
  have hfibeq : x ^ (c + 1) = (Nat.fib (c + 1) : K) * x + (Nat.fib c : K) := pow_eq_fib hx2 c
  have hzero : (algebraMap (ZMod c) K ((Nat.fib (c + 1) : ZMod c))) * x
      + algebraMap (ZMod c) K (((Nat.fib c : ZMod c)) + 1) = 0 := by
    rw [map_natCast, map_add, map_natCast, map_one]
    linear_combination hkey - hfibeq
  obtain ⟨h1, h2⟩ := hli _ _ hzero
  refine ⟨?_, ?_⟩
  · refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ?_
    push_cast
    exact h1
  · refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ?_
    push_cast
    exact h2

/-! ### Step 2: the sign flip, by lifting the exponent -/

/-- The Fibonacci companion matrix. -/
def fibM : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

theorem fibM_pow (N : ℕ) :
    fibM ^ N = !![(Nat.fib (N + 1) : ℤ), (Nat.fib N : ℤ);
                  (Nat.fib N : ℤ), (Nat.fib (N + 1) : ℤ) - (Nat.fib N : ℤ)] := by
  induction N with
  | zero =>
      norm_num
      exact Matrix.one_fin_two
  | succ N ih =>
      have hf : (Nat.fib (N + 2) : ℤ) = (Nat.fib N : ℤ) + (Nat.fib (N + 1) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := N))
      rw [pow_succ, ih, fibM, Matrix.mul_fin_two]
      rw [show N + 1 + 1 = N + 2 from rfl, hf]
      norm_num
      ring_nf

/-- Cassini's identity over `ℤ`. -/
theorem cassini_int (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := m))
      rw [h, pow_succ]
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- Binomial expansion to second order: `(1 − ε)^k = 1 − kε + ε²·D`, valid in any ring. -/
theorem one_sub_pow_expand {R : Type*} [Ring R] (ε : R) (k : ℕ) :
    ∃ D : R, (1 - ε) ^ k = 1 - (k : ℤ) • ε + ε ^ 2 * D := by
  have key : ∃ D : Polynomial ℤ,
      (1 - Polynomial.X : Polynomial ℤ) ^ k
        = 1 - (k : ℤ) • Polynomial.X + Polynomial.X ^ 2 * D := by
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
        obtain ⟨D, hD⟩ := ih
        refine ⟨(k : ℤ) • 1 + D - Polynomial.X * D, ?_⟩
        rw [pow_succ, hD]
        push_cast
        simp only [zsmul_eq_mul]
        push_cast
        ring
  obtain ⟨D, hD⟩ := key
  refine ⟨Polynomial.aeval ε D, ?_⟩
  have h := congrArg (Polynomial.aeval ε) hD
  simpa using h

/-- The inverse of `fibM ^ Q` for odd `Q`, written out in Fibonacci numbers. -/
def fibMinv (Q : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(Nat.fib Q : ℤ) - (Nat.fib (Q + 1) : ℤ), (Nat.fib Q : ℤ);
     (Nat.fib Q : ℤ), -(Nat.fib (Q + 1) : ℤ)]

theorem fibM_pow_mul_fibMinv {Q : ℕ} (hQ : Odd Q) : fibM ^ Q * fibMinv Q = 1 := by
  have hc := cassini_int Q
  have hneg : ((-1 : ℤ)) ^ Q = -1 := hQ.neg_one_pow
  rw [hneg] at hc
  rw [fibM_pow, fibMinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num <;> linarith [hc]

/-- **The inductive form of the sign flip**: `A^(c^n (c+1)) ≡ −I (mod c^(n+1))`. -/
theorem fibM_pow_eq_neg_one_add {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (h5 : c % 5 = 2 ∨ c % 5 = 3) (n : ℕ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
      fibM ^ (c ^ n * (c + 1)) = -1 + (c : ℤ) ^ (n + 1) • B := by
  have hodd : Odd c := hc.odd_of_ne_two hc2
  induction n with
  | zero =>
      obtain ⟨ha, hb⟩ := fib_frobenius_inert hc h5
      obtain ⟨a, ha'⟩ := ha
      obtain ⟨b, hb'⟩ := hb
      refine ⟨!![a + b, a; a, b], ?_⟩
      have hf2 : (Nat.fib (c + 2) : ℤ) = (Nat.fib c : ℤ) + (Nat.fib (c + 1) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := c))
      rw [show c ^ 0 * (c + 1) = c + 1 from by ring, fibM_pow]
      rw [show c + 1 + 1 = c + 2 from rfl, hf2]
      rw [Matrix.one_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply] <;> linarith [ha', hb']
  | succ n ih =>
      obtain ⟨B, hB⟩ := ih
      obtain ⟨D, hD⟩ := one_sub_pow_expand ((c : ℤ) ^ (n + 1) • B) c
      refine ⟨B - (c : ℤ) ^ n • (B ^ 2 * D), ?_⟩
      have hsplit : c ^ (n + 1) * (c + 1) = (c ^ n * (c + 1)) * c := by ring
      rw [hsplit, pow_mul, hB]
      have hneg : (-1 + (c : ℤ) ^ (n + 1) • B) = -(1 - (c : ℤ) ^ (n + 1) • B) := by abel
      rw [hneg, hodd.neg_pow, hD]
      have hsm : ((c : ℤ) • ((c : ℤ) ^ (n + 1) • B)) = (c : ℤ) ^ (n + 1 + 1) • B := by
        rw [smul_smul]; congr 1; ring
      have he2 : ((c : ℤ) ^ (n + 1) • B) ^ 2 * D
          = (c : ℤ) ^ (n + 1 + 1) • ((c : ℤ) ^ n • (B ^ 2 * D)) := by
        rw [_root_.smul_pow, smul_mul_assoc, smul_smul]
        congr 1
        ring
      rw [hsm, he2, smul_sub, smul_smul]
      abel

/-- **The sign flip at an inert prime.** -/
theorem fib_prime_pow_succ_add {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ (Nat.fib (c ^ (n + 1)) : ℤ) + Nat.fib (c ^ n) := by
  rcases eq_or_ne c 2 with rfl | hc2
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · exact SaitoFibonacci.two_pow_dvd_fib_two_pow_succ_add n hn
  have hodd : Odd c := hc.odd_of_ne_two hc2
  obtain ⟨B, hB⟩ := fibM_pow_eq_neg_one_add hc hc2 h5 n
  have hQodd : Odd (c ^ n) := hodd.pow
  have hinv := fibM_pow_mul_fibMinv hQodd
  have hpa : fibM ^ (c ^ n * (c + 1)) = fibM ^ (c ^ (n + 1)) * fibM ^ (c ^ n) := by
    rw [← pow_add]
    congr 1
  have hkey : fibM ^ (c ^ (n + 1)) = (-1 + (c : ℤ) ^ (n + 1) • B) * fibMinv (c ^ n) := by
    rw [← hB, hpa, mul_assoc, hinv, mul_one]
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin 2) (Fin 2) ℤ, W = B * fibMinv (c ^ n) := ⟨_, rfl⟩
  have hd : fibM ^ (c ^ (n + 1)) + fibMinv (c ^ n) = (c : ℤ) ^ (n + 1) • W := by
    rw [hW, hkey, Matrix.add_mul, neg_one_mul, Matrix.smul_mul]
    abel
  refine ⟨W 0 1, ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hd
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, fibM_pow, fibMinv] at h01
  simpa using h01

/-! ### Step 3: the `c`-adic part of `|GL₂(𝔽_p)|` for an odd prime `c` -/

theorem factorization_self_eq_zero {p c : ℕ} (hp : p.Prime) (hpc : p ≠ c) :
    p.factorization c = 0 := by
  rw [hp.factorization]
  simp [Finsupp.single_apply, hpc]

/-- `v_c|GL₂(𝔽_p)| = 2 v_c(p−1) + v_c(p+1)` for a prime `p ≠ c`. -/
theorem padicValNat_glCard_two {c p : ℕ} (hc : c.Prime) (hp : p.Prime) (hpc : p ≠ c) :
    padicValNat c (glCard 2 p) = 2 * (p - 1).factorization c + (p + 1).factorization c := by
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have hq1 : p - 1 = r := by omega
  have he1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h : p ^ 2 = (p - 1) * (p + 1) + 1 := by rw [hq1, hr]; ring
    omega
  have he2 : p ^ 2 - p = p * (p - 1) := by
    have h : p ^ 2 = p * (p - 1) + p := by rw [hq1, hr]; ring
    omega
  have hg : glCard 2 p = ((p - 1) * (p + 1)) * (p * (p - 1)) := by
    rw [glCard, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [he1, he2]
  have hne1 : p - 1 ≠ 0 := by omega
  have hne2 : p + 1 ≠ 0 := by omega
  have hnep : p ≠ 0 := by omega
  have hfp : p.factorization c = 0 := factorization_self_eq_zero hp hpc
  have hdef := Nat.factorization_def (glCard 2 p) hc
  rw [← hdef, hg]
  rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul hne1 hne2, Nat.factorization_mul hnep hne1]
  simp [hfp]
  omega

/-- The filter's `c`-adic output for an odd prime `c`. -/
theorem pow_dvd_sub_or_add_of_lt_padicValNat {c p k : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hp : p.Prime) (hpc : p ≠ c) (hk : k < padicValNat c (glCard 2 p)) :
    (c : ℤ) ^ (k / 2) ∣ (p : ℤ) - 1 ∨ (c : ℤ) ^ (k / 2) ∣ (p : ℤ) + 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hne1 : p - 1 ≠ 0 := by omega
  have hne2 : p + 1 ≠ 0 := by omega
  set a := (p - 1).factorization c with ha
  set b := (p + 1).factorization c with hb
  rw [padicValNat_glCard_two hc hp hpc] at hk
  -- `c` cannot divide both `p − 1` and `p + 1`
  have hmin : a = 0 ∨ b = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hb0⟩ := hcon
    have hd1 : c ∣ p - 1 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hc hne1).2 (show 1 ≤ a by omega)
      simpa using this
    have hd2 : c ∣ p + 1 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hc hne2).2 (show 1 ≤ b by omega)
      simpa using this
    have hd : c ∣ 2 := by
      have hsub := Nat.dvd_sub hd2 hd1
      rwa [show p + 1 - (p - 1) = 2 from by omega] at hsub
    have hle := Nat.le_of_dvd (by norm_num) hd
    have := hc.two_le
    omega
  have hcast1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have : (1 : ℕ) ≤ p := by omega
    push_cast [this]
    ring
  have hcast2 : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
  rcases hmin with h | h
  · right
    have hkb : k / 2 ≤ b := by omega
    have : (c : ℕ) ^ (k / 2) ∣ p + 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc hne2).2 (by rw [← hb]; exact hkb)
    rw [← hcast2]
    exact_mod_cast Int.natCast_dvd_natCast.2 this
  · left
    have hka : k / 2 ≤ a := by omega
    have : (c : ℕ) ^ (k / 2) ∣ p - 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc hne1).2 (by rw [← ha]; exact hka)
    rw [← hcast1]
    exact_mod_cast Int.natCast_dvd_natCast.2 this

/-! ### Step 4: the main theorem at an inert prime -/

theorem fibM_det : fibM.det = -1 := by
  simp [fibM, Matrix.det_fin_two_of]

/-- `F(c^n) ≡ (−1)^n (mod c)`: the sign flip read modulo `c` alone. -/
theorem fib_prime_pow_mod {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3) (n : ℕ) :
    (c : ℤ) ∣ (Nat.fib (c ^ n) : ℤ) - (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hstep := fib_prime_pow_succ_add hc h5 n
      have hc1 : (c : ℤ) ∣ (Nat.fib (c ^ (n + 1)) : ℤ) + Nat.fib (c ^ n) :=
        dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) hstep
      have hre : (Nat.fib (c ^ (n + 1)) : ℤ) - (-1) ^ (n + 1)
          = ((Nat.fib (c ^ (n + 1)) : ℤ) + Nat.fib (c ^ n))
            - ((Nat.fib (c ^ n) : ℤ) - (-1) ^ n) := by ring
      rw [hre]
      exact dvd_sub hc1 ih

theorem fib_prime_pow_lt {c m n : ℕ} (hc2 : 2 ≤ c) (hm : 1 ≤ m) (hmn : m < n) :
    Nat.fib (c ^ m) < Nat.fib (c ^ n) := by
  have h1 : 2 ≤ c ^ m := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ c ^ 1 := Nat.pow_le_pow_left hc2 1
    _ ≤ c ^ m := Nat.pow_le_pow_right (by omega) hm
  have h2 : 2 ≤ c ^ n := by
    refine le_trans h1 (Nat.pow_le_pow_right (by omega) (by omega))
  exact Nat.fib_strictMonoOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 h2)
    (Nat.pow_lt_pow_right (by omega) hmn)

theorem le_fib_prime_pow {c n : ℕ} (hc2 : 2 ≤ c) (hn : 5 ≤ n) : n ≤ Nat.fib (c ^ n) := by
  have h1 : n ≤ c ^ n := by
    calc n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ c ^ n := Nat.pow_le_pow_left hc2 n
  exact le_trans (Nat.le_fib_self hn) (Nat.fib_mono h1)

/-- **The mechanism** (prime as modulus), read off entry `(0,1)` of `fibM`. -/
theorem exists_fib_prime_pow_congr {c p m : ℕ} (hp : p.Prime) (hc : c.Prime)
    (hv : padicValNat c (glCard 2 p) ≤ m) :
    ∃ j, 1 ≤ j ∧ (p : ℤ) ∣ (Nat.fib (c ^ (m + j)) : ℤ) - Nat.fib (c ^ m) := by
  have hdet : ¬ (p : ℤ) ∣ fibM.det := by
    rw [fibM_det]
    intro hdd
    have h1 : (p : ℤ) ∣ 1 := (dvd_neg.mp hdd)
    have h2 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have := hp.two_le
    omega
  obtain ⟨j, hj1, hj⟩ := SaitoFibonacci.exists_entry_pow_congr fibM hp hc hdet hv
  refine ⟨j, hj1, ?_⟩
  have h := hj 0 1
  rw [fibM_pow, fibM_pow] at h
  simpa using h

theorem not_prime_of_prime_dvd {c : ℕ} (hc : c.Prime) {x : ℤ} (hd : (c : ℤ) ∣ x)
    (hx : (c : ℤ) < x) : ¬ Prime x := by
  intro hpx
  have hn : x.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hpx
  have hc2 := hc.two_le
  have hd' : c ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd
    simpa using this
  rcases hn.eq_one_or_self_of_dvd c hd' with hh | hh
  · omega
  · have := Int.natAbs_eq x
    omega

/-- **`F(c^n) + h` is composite infinitely often, for every inert prime `c` and every `h`.** -/
theorem fib_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3)
    (h : ℤ) : ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  rcases eq_or_ne c 2 with rfl | hc2
  · exact SaitoFibonacci.fib_two_pow_add_not_prime h
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with hlt | hge
    · interval_cases c <;> simp_all
    · exact hge
  have hcle : 2 ≤ c := by omega
  -- the three small shifts, handled by hand
  rcases eq_or_ne h 0 with rfl | h0
  · -- `h = 0`: `F(c) ∣ F(c^n)`, and both exceed 1
    refine Filter.Eventually.frequently ?_
    refine eventually_atTop.2 ⟨2, fun n hn => ?_⟩
    have hdvd : Nat.fib (c ^ 1) ∣ Nat.fib (c ^ n) :=
      Nat.fib_dvd _ _ (pow_dvd_pow c (by omega))
    have hlt : Nat.fib (c ^ 1) < Nat.fib (c ^ n) := fib_prime_pow_lt hcle (by omega) (by omega)
    have hone : 1 < Nat.fib (c ^ 1) := by
      have : Nat.fib 3 ≤ Nat.fib (c ^ 1) := Nat.fib_mono (by simpa using hc3)
      have h3 : Nat.fib 3 = 2 := by decide
      omega
    intro hpr
    rw [add_zero] at hpr
    have hnp : (Nat.fib (c ^ n)).Prime := Nat.prime_iff_prime_int.2 hpr
    rcases hnp.eq_one_or_self_of_dvd _ hdvd with hh | hh <;> omega
  rcases eq_or_ne h 1 with rfl | h1
  · -- `h = 1`: for odd `n`, `c ∣ F(c^n) + 1`
    rw [Filter.frequently_atTop]
    intro a
    refine ⟨2 * (a + c + 5) + 1, by omega, ?_⟩
    set n := 2 * (a + c + 5) + 1 with hn
    have hodd : Odd n := ⟨a + c + 5, by omega⟩
    have hgrow : n ≤ Nat.fib (c ^ n) := le_fib_prime_pow hcle (by omega)
    have hgrow' : (n : ℤ) ≤ (Nat.fib (c ^ n) : ℤ) := by exact_mod_cast hgrow
    have hcn : (c : ℤ) < (n : ℤ) := by
      have : (c : ℤ) < ((2 * (a + c + 5) + 1 : ℕ) : ℤ) := by push_cast; omega
      rwa [← hn] at this
    refine not_prime_of_prime_dvd hc ?_ (by omega)
    have := fib_prime_pow_mod hc h5 n
    rw [hodd.neg_one_pow] at this
    simpa using this
  rcases eq_or_ne h (-1) with rfl | hm1
  · -- `h = -1`: for even `n`, `c ∣ F(c^n) − 1`
    rw [Filter.frequently_atTop]
    intro a
    refine ⟨2 * (a + c + 5), by omega, ?_⟩
    set n := 2 * (a + c + 5) with hn
    have heven : Even n := ⟨a + c + 5, by omega⟩
    have hgrow : n ≤ Nat.fib (c ^ n) := le_fib_prime_pow hcle (by omega)
    have hgrow' : (n : ℤ) ≤ (Nat.fib (c ^ n) : ℤ) := by exact_mod_cast hgrow
    have hcn : (c : ℤ) + 2 < (n : ℤ) := by
      have : (c : ℤ) + 2 < ((2 * (a + c + 5) : ℕ) : ℤ) := by push_cast; omega
      rwa [← hn] at this
    refine not_prime_of_prime_dvd hc ?_ (by omega)
    have := fib_prime_pow_mod hc h5 n
    rw [heven.neg_one_pow] at this
    exact this
  -- `|h| ≥ 2`: the filter argument
  have hH2 : 2 ≤ h.natAbs := by omega
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_not] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  set t : ℕ → ℤ := fun n => (Nat.fib (c ^ n) : ℤ) + h with ht
  set H : ℕ := h.natAbs with hH
  set N : ℕ := max (max 5 n₀) (max (c + H + 5) (2 * H + 5)) with hNdef
  have hN5 : 5 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNn₀ : n₀ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNc : c + H + 5 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hbig : ∀ n ≥ N, (c : ℤ) < t n := by
    intro n hn
    have hn5 : 5 ≤ n := le_trans hN5 hn
    have hgrow : (n : ℤ) ≤ (Nat.fib (c ^ n) : ℤ) := by
      exact_mod_cast le_fib_prime_pow hcle hn5
    have hlow : (c : ℤ) + (H : ℤ) + 5 ≤ (n : ℤ) := by
      have h1 : ((c + H + 5 : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNc
      have h2 : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      push_cast at h1
      omega
    have habs : -(H : ℤ) ≤ h := by omega
    simp only [ht]
    omega
  have hprime : ∀ n ≥ N, Prime (t n) := fun n hn => hn₀ n (le_trans hNn₀ hn)
  have htmono : ∀ {m n : ℕ}, N ≤ m → m < n → t m < t n := by
    intro m n hm hmn
    have h1 := fib_prime_pow_lt hcle (show 1 ≤ m by omega) hmn
    have h2 : (Nat.fib (c ^ m) : ℤ) < (Nat.fib (c ^ n) : ℤ) := by exact_mod_cast h1
    simp only [ht]
    omega
  have hnat : ∀ n ≥ N, ∃ p : ℕ, p.Prime ∧ p ≠ c ∧ (p : ℤ) = t n := by
    intro n hn
    have hb := hbig n hn
    have hc0 : (0 : ℤ) < (c : ℤ) := by positivity
    refine ⟨(t n).toNat, ?_, ?_, by omega⟩
    · have := hprime n hn
      rw [Int.prime_iff_natAbs_prime] at this
      have hEq : (t n).natAbs = (t n).toNat := by omega
      rwa [hEq] at this
    · intro hEq
      have : (c : ℤ) = ((t n).toNat : ℤ) := by rw [← hEq]
      omega
  have hdetp : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ fibM.det := by
    intro p hp hdd
    rw [fibM_det] at hdd
    have h1 : (p : ℤ) ∣ 1 := (dvd_neg.mp hdd)
    have h2 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have := hp.two_le
    omega
  have hstep2 : ∀ n ≥ N, ∀ p : ℕ, p.Prime → (p : ℤ) = t n →
      ¬ (padicValNat c (glCard 2 p) ≤ n) := by
    intro n hn p hp hpv hv
    obtain ⟨j, hj1, hj01⟩ := exists_fib_prime_pow_congr hp hc hv
    have hdvd : (p : ℤ) ∣ t (n + j) := by
      have h1 : (p : ℤ) ∣ t n := by rw [hpv]
      have h2 : t (n + j) - t n = (Nat.fib (c ^ (n + j)) : ℤ) - Nat.fib (c ^ n) := by
        simp only [ht]; ring
      have h3 := dvd_add hj01 h1
      rw [← h2] at h3
      simpa using h3
    have hgt : t n < t (n + j) := htmono hn (by omega)
    have hq := hprime (n + j) (by omega)
    have hqpos : 0 < t (n + j) := by have := hbig n hn; have := hc.two_le; omega
    obtain ⟨q, hqv⟩ : ∃ q : ℕ, (q : ℤ) = t (n + j) := ⟨(t (n + j)).toNat, by omega⟩
    have hqnat : q.Prime := by
      rw [Int.prime_iff_natAbs_prime] at hq
      have hEq : (t (n + j)).natAbs = q := by omega
      rwa [hEq] at hq
    have hdq : p ∣ q := by
      have : (p : ℤ) ∣ (q : ℤ) := by rw [hqv]; exact hdvd
      exact_mod_cast this
    have hp1 : 1 < p := hp.one_lt
    rcases hqnat.eq_one_or_self_of_dvd p hdq with hh | hh <;> omega
  have hstep3 : ∀ n ≥ N, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (c : ℤ) ^ (n / 2) ∣ t n - s := by
    intro n hn
    obtain ⟨p, hp, hpc, hpv⟩ := hnat n hn
    have hlt : n < padicValNat c (glCard 2 p) := by
      by_contra hle
      exact hstep2 n hn p hp hpv (by omega)
    rcases pow_dvd_sub_or_add_of_lt_padicValNat hc hc2 hp hpc hlt with hd | hd
    · exact ⟨1, Or.inl rfl, by rw [← hpv]; exact hd⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [← hpv]
      simpa using hd
  -- pick `n` large and contradict `|h| ≥ 2`
  set n : ℕ := 2 * (2 * H + 3) + N with hn
  set e : ℕ := n / 2 with he
  have hnN : N ≤ n := by omega
  have hbnd : (2 * H + 2 : ℤ) < (c : ℤ) ^ e := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ e ≤ c ^ e := Nat.pow_le_pow_left hcle e
    have h3 : 2 * H + 2 < c ^ e := by omega
    exact_mod_cast h3
  obtain ⟨s, hs, hsd⟩ := hstep3 n hnN
  obtain ⟨s', hs', hsd'⟩ := hstep3 (n + 1) (by omega)
  have hdvd' : (c : ℤ) ^ e ∣ t (n + 1) - s' := by
    refine dvd_trans (pow_dvd_pow _ ?_) hsd'
    omega
  have hflip : (c : ℤ) ^ e ∣ (Nat.fib (c ^ (n + 1)) : ℤ) + Nat.fib (c ^ n) := by
    refine dvd_trans (pow_dvd_pow _ ?_) (fib_prime_pow_succ_add hc h5 n)
    omega
  have hsum : (c : ℤ) ^ e ∣ s + s' - 2 * h := by
    have h1 : (s + s' - 2 * h) =
        ((Nat.fib (c ^ (n + 1)) : ℤ) + Nat.fib (c ^ n)) - ((t n - s) + (t (n + 1) - s')) := by
      simp only [ht]; ring
    rw [h1]
    exact dvd_sub hflip (dvd_add hsd hdvd')
  have hzero : s + s' - 2 * h = 0 := by
    by_contra hne
    have hle := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hsum)
    have hb : |s + s' - 2 * h| ≤ 2 * (H : ℤ) + 2 := by
      rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> rw [abs_le] <;> omega
    omega
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> omega
/-! ### Step 5: the ramified prime `c = 5` -/

theorem matrix_pow_five (A : Matrix (Fin 2) (Fin 2) ℤ) : A ^ 5 = A * A * A * A * A := by
  rw [show (5 : ℕ) = 1 + 1 + 1 + 1 + 1 from by norm_num,
    pow_add, pow_add, pow_add, pow_add, pow_one]

/-- The quintuplication formula `F(5m) = F(m)(25F(m)^4 + 25(−1)^m F(m)^2 + 5)`. -/
theorem fib_five_mul (m : ℕ) : (Nat.fib (5 * m) : ℤ)
    = Nat.fib m * (25 * (Nat.fib m : ℤ) ^ 4 + 25 * (-1) ^ m * (Nat.fib m : ℤ) ^ 2 + 5) := by
  have hmat : fibM ^ (5 * m) = (fibM ^ m) ^ 5 := by rw [← pow_mul, Nat.mul_comm]
  have h01 : (fibM ^ (5 * m)) 0 1 = ((fibM ^ m) ^ 5) 0 1 := by rw [hmat]
  rw [fibM_pow (5 * m), matrix_pow_five, fibM_pow m] at h01
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two] at h01
  norm_num at h01
  have hc := cassini_int m
  have hu : ((-1 : ℤ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  linear_combination h01
    + (25 * (Nat.fib m : ℤ) ^ 3
        + 5 * (Nat.fib m : ℤ) * (((Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib (m + 1) : ℤ) * Nat.fib m
            - (Nat.fib m : ℤ) ^ 2) + (-1) ^ m)) * hc
    + 5 * (Nat.fib m : ℤ) * hu

/-- `5^n ∣ F(5^n)`. -/
theorem five_pow_dvd_fib_five_pow (n : ℕ) : (5 : ℤ) ^ n ∣ Nat.fib (5 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := fib_five_mul (5 ^ n)
      rw [show (5 : ℕ) * 5 ^ n = 5 ^ (n + 1) from by ring] at h
      rw [h, pow_succ]
      refine mul_dvd_mul ih ⟨5 * (Nat.fib (5 ^ n) : ℤ) ^ 4
        + 5 * (-1) ^ (5 ^ n) * (Nat.fib (5 ^ n) : ℤ) ^ 2 + 1, by ring⟩

/-- **`F(5^n) + h` is composite infinitely often, for every `h`.** -/
theorem fib_five_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.FibonacciPrimePow

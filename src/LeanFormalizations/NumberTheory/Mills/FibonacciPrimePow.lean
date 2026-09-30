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

/-- **The sign flip at an inert prime.** -/
theorem fib_prime_pow_succ_add {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3) (n : ℕ) :
    (c : ℤ) ^ (n + 1) ∣ (Nat.fib (c ^ (n + 1)) : ℤ) + Nat.fib (c ^ n) := by
  sorry

/-- The filter's `c`-adic output for an odd prime `c`. -/
theorem pow_dvd_sub_or_add_of_lt_padicValNat {c p k : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hp : p.Prime) (hpc : p ≠ c) (hk : k < padicValNat c (glCard 2 p)) :
    (c : ℤ) ^ (k / 2) ∣ (p : ℤ) - 1 ∨ (c : ℤ) ^ (k / 2) ∣ (p : ℤ) + 1 := by
  sorry

/-- **`F(c^n) + h` is composite infinitely often, for every inert prime `c` and every `h`.** -/
theorem fib_prime_pow_add_not_prime {c : ℕ} (hc : c.Prime) (h5 : c % 5 = 2 ∨ c % 5 = 3)
    (h : ℤ) : ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  sorry

/-- `5^n ∣ F(5^n)`. -/
theorem five_pow_dvd_fib_five_pow (n : ℕ) : (5 : ℤ) ^ n ∣ Nat.fib (5 ^ n) := by
  sorry

/-- **`F(5^n) + h` is composite infinitely often, for every `h`.** -/
theorem fib_five_pow_add_not_prime (h : ℤ) :
    ∃ᶠ n in atTop, ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + h) := by
  sorry

end LeanFormalizations.Mills.FibonacciPrimePow

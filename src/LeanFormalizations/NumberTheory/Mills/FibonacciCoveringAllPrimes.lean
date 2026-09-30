/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciCovering

/-!
# Phase 41 groundwork: Theorem C at an ODD prime `c`

Phase 40 (`FibonacciCovering.lean`) proved Dubickas's (D1) and prime-free intervals for
`F(2^n)`.  Roadmap item §1 Theorem C asks for every prime `c ≠ 5`.  This file collects the pieces
of the phase-40 route that generalize **with no new idea**, so that a later lap faces only the one
genuine obstruction (recorded in `ROADMAP-PRIME-TOWERS.md`, and restated below).

## What generalizes freely
* the mechanism: `FibonacciCovering.exists_entry_pow_congr_mul` is already stated for a general
  `n × n` integer matrix and a general prime `c`;
* the "product of `≡ ±1` primes is `≡ ±1`" step, once `PmOne` is taken modulo an arbitrary
  `M` (`PmOneMod` below, of which phase 40's `PmOne e` is the case `M = 2^e`);
* the `GL₂` valuation bound (`pow_dvd_sub_or_add_of_lt_padicValNat_odd` below), which is in fact
  *easier* at odd `c` than at `c = 2`: an odd `c` divides at most one of `p ∓ 1`, so one of the two
  valuations is `0`, whereas at `c = 2` both are positive and one has to be exactly `1`;
* `c` itself is always a good prime (`padicValNat_glCard_two_self`: `v_c|GL₂(𝔽_c)| = 1`).

## What does NOT generalize — the phase-41 crux
Phase 40's certificate `2^(n+1) ∣ 5F(2^n)² + 3` is a **single-index** statement, and that is
exactly what makes `exists_good_prime_factor` an `∀ᶠ n` statement there.  At odd `c` the roadmap's
certificate is the fixed-point obstruction `Φ_J(x) − x ∉ {0, ±2}` for `x ≠ 0`
(`FibonacciAllPrimes.fibOddPoly_far`), which is a **two-index** statement: from
`c^e ∣ F(c^n) − x` and `c^e ∣ F(c^(n+d)) − x'` one gets `c^e ∣ Φ_J(x) − x'` with
`2J + 1 = c^d`, and only then `Φ_J(x) = x'` — provided `c^e` exceeds `|Φ_J(x)| + |x'|`.

That proviso is the wall.  `|Φ_J(x)|` grows like `φ^(c^d)`, so the threshold on `n` needed to
compare indices `n` and `n + d` grows like `c^d`.  Two-index comparison therefore only shows that
bad indices are **exponentially sparse**, not that they are finitely many — so it does not yield
`∀ᶠ n, ∃ good p`, and it does not even yield one index good for all `|h| ≤ H` at once (different
shifts may stay bad at different indices).

To recover phase 40's shape one needs the fixed distance `d = 2`, i.e. a **`c`-adic convergence**
statement
  `c^(n + 1) ∣ F(c^(n+2)) − F(c^n)`   (or any `c^(κ n)` with `κ > 0`),
which is the quantitative form of "Frobenius permutes the Teichmüller lifts of `α, β`, and its
square fixes them".  With it the argument collapses to a single index: `c^e ∣ F(c^n) − x` gives
`c^e ∣ Φ_J(x) − Φ_J(F(c^n)) = Φ_J(x) − F(c^(n+2))`, hence `c^e ∣ Φ_J(x) − x` for `e ≤ n + 1`, and
`fibOddPoly_far` finishes (with `x ≠ 0` from `FibonacciAllPrimes.not_dvd_fib_prime_pow`).

So the phase-41 crux is exactly:

> `c^(n+1) ∣ F(c^(n+2)) − F(c^n)` for every odd prime `c ≠ 5`.

Base case `n = 0`: `F(c²) ≡ F(1) (mod c)`, which is `F(cM) ≡ (5|c) F(M) (mod c)` applied twice.
It is deliberately **not** stated as a `sorry` here: nothing below depends on it, and the lap that
attacks it should choose its own exponent.  Everything in this file is proved.
-/

namespace LeanFormalizations.Mills.FibonacciCoveringAllPrimes

open LeanFormalizations.Mills.ThreeAdic Filter

/-! ### The `±1` residues modulo an arbitrary modulus -/

/-- `x ≡ ±1 (mod M)`.  Phase 40's `FibonacciCovering.PmOne e` is the case `M = 2^e`. -/
def PmOneMod (M : ℤ) (x : ℤ) : Prop := M ∣ x - 1 ∨ M ∣ x + 1

lemma PmOneMod.one (M : ℤ) : PmOneMod M 1 := Or.inl (by simp)

lemma PmOneMod.exists_sign {M x : ℤ} (hx : PmOneMod M x) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ M ∣ x - s := by
  rcases hx with h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩

lemma PmOneMod.mul {M x y : ℤ} (hx : PmOneMod M x) (hy : PmOneMod M y) : PmOneMod M (x * y) := by
  obtain ⟨s, hs, hsd⟩ := hx.exists_sign
  obtain ⟨t, ht, htd⟩ := hy.exists_sign
  have hkey : M ∣ x * y - s * t := by
    have h : x * y - s * t = y * (x - s) + s * (y - t) := by ring
    rw [h]
    exact dvd_add (hsd.mul_left _) (htd.mul_left _)
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact Or.inl (by simpa using hkey)
  · exact Or.inr (by simpa using hkey)
  · exact Or.inr (by simpa using hkey)
  · exact Or.inl (by simpa using hkey)

/-- A natural number all of whose prime factors are `≡ ±1 (mod M)` is itself `≡ ±1 (mod M)`. -/
lemma PmOneMod.of_prime_factors (M : ℤ) :
    ∀ N : ℕ, 1 ≤ N → (∀ q : ℕ, q.Prime → q ∣ N → PmOneMod M (q : ℤ)) → PmOneMod M (N : ℤ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      intro hN hfac
      rcases eq_or_lt_of_le hN with h1 | h1
      · rw [← h1]; simpa using PmOneMod.one M
      · have hN1 : N ≠ 1 := by omega
        have hmf : (N.minFac).Prime := Nat.minFac_prime hN1
        obtain ⟨K, hK⟩ := N.minFac_dvd
        have hKpos : 1 ≤ K := by
          rcases Nat.eq_zero_or_pos K with h | h
          · rw [h, Nat.mul_zero] at hK; omega
          · exact h
        have hKlt : K < N := by
          have h2 : 2 ≤ N.minFac := hmf.two_le
          have h3 : 2 * K ≤ N := by rw [hK]; exact Nat.mul_le_mul_right K h2
          exact lt_of_lt_of_le (show K < 2 * K by omega) h3
        have hrec : PmOneMod M (K : ℤ) :=
          ih K hKlt hKpos (fun q hq hqd => hfac q hq (hK ▸ Dvd.dvd.mul_left hqd _))
        have hcast : ((N : ℤ)) = (N.minFac : ℤ) * (K : ℤ) := by rw [← Nat.cast_mul, ← hK]
        rw [hcast]
        exact (hfac _ hmf N.minFac_dvd).mul hrec

/-! ### The `GL₂` valuation at an odd prime -/

/-- `glCard 2 p = ((p−1)(p+1)) * (p(p−1))`, as naturals. -/
lemma glCard_two_eq {p : ℕ} (hp : 2 ≤ p) :
    glCard 2 p = ((p - 1) * (p + 1)) * (p * (p - 1)) := by
  obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have hr1 : p - 1 = r := by omega
  have he1 : p ^ 2 - 1 = (p - 1) * (p + 1) :=
    Nat.sub_eq_of_eq_add (by rw [hr1, hr]; ring)
  have he2 : p ^ 2 - p = p * (p - 1) :=
    Nat.sub_eq_of_eq_add (by rw [hr1, hr]; ring)
  rw [glCard, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [he1, he2]

/-- `v_c |GL₂(𝔽_c)| = 1`: the base prime is always a *good* prime, for every `c`.  (Phase 40's
`padicValNat_glCard_two_two` is the case `c = 2`.) -/
lemma padicValNat_glCard_two_self {c : ℕ} (hc : c.Prime) :
    padicValNat c (glCard 2 c) = 1 := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hc2 := hc.two_le
  have hne1 : c - 1 ≠ 0 := by omega
  have hne2 : c + 1 ≠ 0 := by omega
  have hnec : c ≠ 0 := by omega
  have hnd1 : ¬ (c ∣ c - 1) := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hnd2 : ¬ (c ∣ c + 1) := by
    intro hd
    have : c ∣ 1 := (Nat.dvd_add_right dvd_rfl).mp hd
    have := Nat.le_of_dvd one_pos this
    omega
  have hf1 : (c - 1).factorization c = 0 := by
    simp [Nat.factorization_eq_zero_iff, hnd1]
  have hf2 : (c + 1).factorization c = 0 := by
    simp [Nat.factorization_eq_zero_iff, hnd2]
  have hfc : c.factorization c = 1 := by
    rw [Nat.Prime.factorization hc]; simp
  have hcard := glCard_two_eq hc2
  have hpos : glCard 2 c ≠ 0 := by
    rw [hcard]
    have : 0 < (c - 1) * (c + 1) := by positivity
    have : 0 < c * (c - 1) := by positivity
    positivity
  rw [← Nat.factorization_def _ hc, hcard,
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul hne1 hne2, Nat.factorization_mul hnec hne1]
  simp [hf1, hf2, hfc]

/-- **The `GL₂` bound at an odd prime.**  If `v_c |GL₂(𝔽_p)| > n` then `p ≡ ±1 (mod c^(n/2))`.

This is the odd-`c` analogue of `SaitoFibonacci.two_pow_dvd_sub_or_add_of_lt_padicValNat`, and it
is *easier*: since `c` is odd it cannot divide both `p − 1` and `p + 1` (their difference is `2`),
so one of the two valuations vanishes and `v_c|GL₂(𝔽_p)| = 2 v_c(p−1) + v_c(p+1)` degenerates to a
single term. -/
theorem pow_dvd_sub_or_add_of_lt_padicValNat_odd {c p n : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hp : p.Prime) (hpc : p ≠ c) (hn : n < padicValNat c (glCard 2 p)) :
    (c : ℤ) ^ (n / 2) ∣ (p : ℤ) - 1 ∨ (c : ℤ) ^ (n / 2) ∣ (p : ℤ) + 1 := by
  haveI : Fact c.Prime := ⟨hc⟩
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with h | h
    · interval_cases c <;> simp_all
    · exact h
  have hp2 := hp.two_le
  have hne1 : p - 1 ≠ 0 := by omega
  have hne2 : p + 1 ≠ 0 := by omega
  have hnep : p ≠ 0 := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = (p - 1).factorization c := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (p + 1).factorization c := ⟨_, rfl⟩
  have hfp : p.factorization c = 0 := by
    have : ¬ (c ∣ p) := by
      intro hd
      exact hpc ((Nat.prime_dvd_prime_iff_eq hc hp).1 hd).symm
    simp [Nat.factorization_eq_zero_iff, this]
  have hval : padicValNat c (glCard 2 p) = 2 * a + b := by
    rw [← Nat.factorization_def _ hc, glCard_two_eq hp2,
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul hne1 hne2, Nat.factorization_mul hnep hne1]
    simp only [Finsupp.add_apply]
    rw [← ha, ← hb, hfp]
    omega
  -- `c` odd divides at most one of `p ∓ 1`
  have hzero : a = 0 ∨ b = 0 := by
    by_contra hcon
    push_neg at hcon
    have hd1 : c ∣ p - 1 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hc hne1).2
        (show 1 ≤ (p - 1).factorization c by rw [← ha]; omega)
      simpa using this
    have hd2 : c ∣ p + 1 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hc hne2).2
        (show 1 ≤ (p + 1).factorization c by rw [← hb]; omega)
      simpa using this
    have hd : c ∣ 2 := by
      have hsub := Nat.dvd_sub hd2 hd1
      rwa [show p + 1 - (p - 1) = 2 by omega] at hsub
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hcast1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have h1 : (1 : ℕ) ≤ p := by omega
    push_cast [h1]; ring
  have hcast2 : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
  rw [hval] at hn
  rcases hzero with h | h
  · -- `a = 0`, so `n < b` and certainly `n / 2 ≤ b`
    right
    have hnb : n / 2 ≤ b := by omega
    have hd : (c : ℕ) ^ (n / 2) ∣ p + 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc hne2).2 (by rw [← hb]; exact hnb)
    rw [← hcast2]
    exact_mod_cast Int.natCast_dvd_natCast.2 hd
  · -- `b = 0`, so `n < 2a`, i.e. `n / 2 ≤ a`
    left
    have hna : n / 2 ≤ a := by omega
    have hd : (c : ℕ) ^ (n / 2) ∣ p - 1 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc hne1).2 (by rw [← ha]; exact hna)
    rw [← hcast1]
    exact_mod_cast Int.natCast_dvd_natCast.2 hd

/-! ### `c`-adic convergence of `A^(c^n)` — the phase-41 crux, via group theory only

The route.  Let `T = ord(A mod c)` in `GLₙ(𝔽_c)` and write `T = c^s e` with `c ∤ e`.
1. `A^T = 1 + c • B` (definition of `T`).
2. **Raising to the `c`-th power gains one factor of `c`**: if `Z − 1 = c^k • B` with `k ≥ 1`, then
   `Z^c − 1 = c^(k+1) • B'`.  No binomial coefficients are needed: `Z^c − 1 = S · (Z − 1)` with
   `S = ∑_{i<c} Z^i`, and `S ≡ c · 1 (mod c^k)`, so `S = c • U`.
3. Hence `A^(T c^m) − 1 = c^(m+1) • B_m`, and multiplying the exponent by anything preserves that.
4. `e ∣ c^d − 1` for `d = φ(e)`, so `T c^(n−s) ∣ c^n (c^d − 1) = c^(n+d) − c^n` whenever `s ≤ n`;
   and `s ≤ v_c|GLₙ(𝔽_c)|`, which is `1` for `n = 2`.

Conclusion: `c^n ∣ (A^(c^(n+d)) − A^(c^n)) a b`, with `d` depending only on `c` and `A`.  At
`A = !![1,1;1,0]` and entry `(0,1)` this is `c^n ∣ F(c^(n+d)) − F(c^n)`, and `c^d` is odd, so
`FibonacciAllPrimes.fib_odd_mul` applies with `2J + 1 = c^d`.  That is exactly the single-index
certificate phase 41 needs. -/

section MatrixCong

variable {N : ℕ}

/-- `a` divides `M` entrywise, packaged so ring manipulations are easy. -/
def SmulDvd (a : ℤ) (M : Matrix (Fin N) (Fin N) ℤ) : Prop := ∃ B, M = a • B

lemma SmulDvd.mul_left {a : ℤ} {M : Matrix (Fin N) (Fin N) ℤ} (h : SmulDvd a M)
    (X : Matrix (Fin N) (Fin N) ℤ) : SmulDvd a (X * M) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨X * B, by rw [hB, Matrix.mul_smul]⟩

lemma SmulDvd.mul_right {a : ℤ} {M : Matrix (Fin N) (Fin N) ℤ} (h : SmulDvd a M)
    (X : Matrix (Fin N) (Fin N) ℤ) : SmulDvd a (M * X) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B * X, by rw [hB, Matrix.smul_mul]⟩

lemma SmulDvd.of_dvd {a b : ℤ} {M : Matrix (Fin N) (Fin N) ℤ} (hab : a ∣ b)
    (h : SmulDvd b M) : SmulDvd a M := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨t, ht⟩ := hab
  exact ⟨t • B, by rw [hB, ht, smul_smul]⟩

lemma SmulDvd.entry {a : ℤ} {M : Matrix (Fin N) (Fin N) ℤ} (h : SmulDvd a M) (i j : Fin N) :
    a ∣ M i j := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B i j, by rw [hB]; simp⟩

/-- `Z^m − 1` inherits any entrywise divisor of `Z − 1`. -/
lemma SmulDvd.pow_sub_one {a : ℤ} {Z : Matrix (Fin N) (Fin N) ℤ} (h : SmulDvd a (Z - 1))
    (m : ℕ) : SmulDvd a (Z ^ m - 1) := by
  have hg : (∑ i ∈ Finset.range m, Z ^ i) * (Z - 1) = Z ^ m - 1 := geom_sum_mul Z m
  rw [← hg]
  exact h.mul_left _

/-- **The gain step.**  If `Z ≡ 1 (mod c^k)` with `k ≥ 1`, then `Z^c ≡ 1 (mod c^(k+1))`. -/
lemma SmulDvd.pow_prime_gain {c : ℕ} {k : ℕ} (hk : 1 ≤ k) {Z : Matrix (Fin N) (Fin N) ℤ}
    (h : SmulDvd ((c : ℤ) ^ k) (Z - 1)) :
    SmulDvd ((c : ℤ) ^ (k + 1)) (Z ^ c - 1) := by
  obtain ⟨B, hB⟩ := h
  -- `S = ∑_{i<c} Z^i` is `≡ c · 1 (mod c^k)`, hence `≡ 0 (mod c)`
  obtain ⟨C, hC⟩ : SmulDvd ((c : ℤ) ^ k)
      ((∑ i ∈ Finset.range c, Z ^ i) - (c : ℤ) • (1 : Matrix (Fin N) (Fin N) ℤ)) := by
    have hrw : (∑ i ∈ Finset.range c, Z ^ i) - (c : ℤ) • (1 : Matrix (Fin N) (Fin N) ℤ)
        = ∑ i ∈ Finset.range c, (Z ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      simp [Finset.sum_const, Finset.card_range]
    rw [hrw]
    refine ⟨∑ i ∈ Finset.range c, (Classical.choose (SmulDvd.pow_sub_one ⟨B, hB⟩ i)), ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Classical.choose_spec (SmulDvd.pow_sub_one (a := (c : ℤ) ^ k) ⟨B, hB⟩ i)
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hS : (∑ i ∈ Finset.range c, Z ^ i)
      = (c : ℤ) • ((1 : Matrix (Fin N) (Fin N) ℤ) + (c : ℤ) ^ k' • C) := by
    have h1 : (∑ i ∈ Finset.range c, Z ^ i)
        = (c : ℤ) • (1 : Matrix (Fin N) (Fin N) ℤ) + (c : ℤ) ^ k • C := by
      rw [← hC]; abel
    rw [h1, hk', smul_add, smul_smul, pow_succ']
  have hg : (∑ i ∈ Finset.range c, Z ^ i) * (Z - 1) = Z ^ c - 1 := geom_sum_mul Z c
  refine ⟨((1 : Matrix (Fin N) (Fin N) ℤ) + (c : ℤ) ^ k' • C) * B, ?_⟩
  rw [← hg, hS, hB, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [hk']
  ring

/-- `Z ≡ 1 (mod c)` ⟹ `Z^(c^m) ≡ 1 (mod c^(m+1))`. -/
lemma SmulDvd.pow_prime_pow {c : ℕ} {Z : Matrix (Fin N) (Fin N) ℤ}
    (h : SmulDvd ((c : ℤ) ^ 1) (Z - 1)) (m : ℕ) :
    SmulDvd ((c : ℤ) ^ (m + 1)) (Z ^ c ^ m - 1) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      have hpow : Z ^ c ^ (m + 1) = (Z ^ c ^ m) ^ c := by
        rw [← pow_mul, ← pow_succ]
      rw [hpow]
      exact SmulDvd.pow_prime_gain (by omega) ih

lemma SmulDvd.of_entries (a : ℤ) (M : Matrix (Fin N) (Fin N) ℤ) (h : ∀ i j, a ∣ M i j) :
    SmulDvd a M := by
  classical
  refine ⟨Matrix.of fun i j => (h i j).choose, ?_⟩
  ext i j
  simpa using (h i j).choose_spec

end MatrixCong

/-! ### The `c`-adic convergence theorem -/

/-- **`c`-adic convergence of `A^(c^n)` along a residue class.**  For any integer matrix `A` with
`c ∤ det A` there are a *shift* `d ≥ 1` and a constant `s` — both depending only on `A`, `c` and
the size — with

  `c^(n − s + 1) ∣ (A^(c^(n+d)))ᵢⱼ − (A^(c^n))ᵢⱼ`  for every `n ≥ s`.

This is the quantitative form of "Frobenius permutes the Teichmüller lifts of the eigenvalues, and
a power of it fixes them", proved with no lifting machinery at all: `A^T ≡ 1 (mod c)` for
`T = |GLₙ(𝔽_c)|`, raising to the `c`-th power gains a factor of `c`
(`SmulDvd.pow_prime_pow`), and `c^d ≡ 1 (mod e)` for `d = φ(e)`, `e` the `c`-free part of `T`. -/
theorem exists_shift_pow_congr {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) {c : ℕ} (hc : c.Prime)
    (hdet : ¬ (c : ℤ) ∣ A.det) :
    ∃ d s : ℕ, 1 ≤ d ∧ s ≤ padicValNat c (glCard N c) ∧ ∀ n : ℕ, s ≤ n → ∀ i j : Fin N,
      (c : ℤ) ^ (n - s + 1) ∣ (A ^ c ^ (n + d)) i j - (A ^ c ^ n) i j := by
  haveI : Fact c.Prime := ⟨hc⟩
  set f : ℤ →+* ZMod c := Int.castRingHom (ZMod c) with hf
  set D : Matrix (Fin N) (Fin N) (ZMod c) := f.mapMatrix A with hD
  have hent : ∀ (M : ℕ) (i j : Fin N), (((A ^ M) i j : ℤ) : ZMod c) = (D ^ M) i j := by
    intro M i j
    rw [hD, ← map_pow]
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, hf]
  have hdetD : IsUnit D.det := by
    have hmd : D.det = f A.det := by rw [hD]; exact (RingHom.map_det f A).symm
    rw [hmd]
    refine Ne.isUnit ?_
    simpa [hf, ZMod.intCast_zmod_eq_zero_iff_dvd] using hdet
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det D).2 hdetD
  have hcard : Nat.card (GL (Fin N) (ZMod c)) = glCard N c := by
    rw [Matrix.card_GL_field]
    simp [glCard, ZMod.card]
  obtain ⟨T, hT⟩ : ∃ T, T = glCard N c := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT, ← hcard]; exact Nat.card_pos
  have hTne : T ≠ 0 := hTpos.ne'
  have huT : u ^ T = 1 := by rw [hT, ← hcard]; exact pow_card_eq_one'
  -- `A^T ≡ 1 (mod c)`
  have hDT : D ^ T = 1 := by
    have h : ((u ^ T : (Matrix (Fin N) (Fin N) (ZMod c))ˣ) :
        Matrix (Fin N) (Fin N) (ZMod c)) = ((1 : (Matrix (Fin N) (Fin N) (ZMod c))ˣ) :
        Matrix (Fin N) (Fin N) (ZMod c)) := by rw [huT]
    rw [Units.val_pow_eq_pow_val, hu] at h
    simpa using h
  have hAT : SmulDvd ((c : ℤ) ^ 1) (A ^ T - 1) := by
    refine SmulDvd.of_entries _ _ (fun i j => ?_)
    have hz : ((((A ^ T) i j - (1 : Matrix (Fin N) (Fin N) ℤ) i j : ℤ)) : ZMod c) = 0 := by
      push_cast
      rw [hent, hDT]
      have h1 : ∀ k l : Fin N, (((1 : Matrix (Fin N) (Fin N) ℤ) k l : ℤ) : ZMod c)
          = (1 : Matrix (Fin N) (Fin N) (ZMod c)) k l := by
        intro k l
        by_cases hkl : k = l <;> simp [Matrix.one_apply, hkl]
      rw [h1]
      ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
    simpa using this
  -- split `T = c^s · e` with `c ∤ e`
  obtain ⟨s, hs⟩ : ∃ s, s = padicValNat c T := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = T / c ^ s := ⟨_, rfl⟩
  have hfac : T.factorization c = s := by rw [hs, Nat.factorization_def _ hc]
  have hsplit : c ^ s * e = T := by
    have hx := Nat.ordProj_mul_ordCompl_eq_self T c
    rw [hfac] at hx
    rw [he, hfac] at *
    exact hx
  have hedvd : ¬ (c ∣ e) := by
    have hx := Nat.not_dvd_ordCompl hc hTne
    rw [hfac] at hx
    rwa [he]
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, mul_zero] at hsplit; exact absurd hsplit.symm hTne
    · exact h
  -- `e ∣ c^d − 1` for `d = φ(e)`
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.totient e := ⟨_, rfl⟩
  have hdpos : 1 ≤ d := by rw [hd]; exact Nat.totient_pos.2 hepos
  have hcop : Nat.Coprime c e := (Nat.Prime.coprime_iff_not_dvd hc).2 hedvd
  have hmod : c ^ d ≡ 1 [MOD e] := by rw [hd]; exact Nat.ModEq.pow_totient hcop
  obtain ⟨t, ht⟩ : ∃ t, c ^ d = 1 + e * t := by
    have h1 : 1 ≤ c ^ d := Nat.one_le_pow _ _ hc.pos
    obtain ⟨w, hw⟩ := (Nat.modEq_iff_dvd' h1).1 hmod.symm
    exact ⟨w, by omega⟩
  refine ⟨d, s, hdpos, le_of_eq (by rw [hs, hT]), fun n hn i j => ?_⟩
  -- the exponent gap is `T · c^(n−s) · t`
  obtain ⟨m, hm⟩ : ∃ m, n = s + m := ⟨n - s, by omega⟩
  have hgap : c ^ (n + d) = c ^ n + T * c ^ m * t := by
    have h1 : c ^ (n + d) = c ^ n * c ^ d := by rw [pow_add]
    have h2 : T * c ^ m = c ^ n * e := by rw [← hsplit, hm]; ring
    rw [h1, ht, h2]
    ring
  have hns : n - s + 1 = m + 1 := by omega
  -- `A^(T c^m) ≡ 1 (mod c^(m+1))`, hence so is any power of it
  have hstep : SmulDvd ((c : ℤ) ^ (m + 1)) (A ^ (T * c ^ m) - 1) := by
    have hZ : A ^ (T * c ^ m) = (A ^ T) ^ c ^ m := by rw [← pow_mul]
    rw [hZ]
    exact SmulDvd.pow_prime_pow hAT m
  have hall : SmulDvd ((c : ℤ) ^ (m + 1)) (A ^ (T * c ^ m * t) - 1) := by
    have hZ : A ^ (T * c ^ m * t) = (A ^ (T * c ^ m)) ^ t := by rw [← pow_mul]
    rw [hZ]
    exact SmulDvd.pow_sub_one hstep t
  have hdiff : SmulDvd ((c : ℤ) ^ (m + 1)) (A ^ c ^ (n + d) - A ^ c ^ n) := by
    have hZ : A ^ c ^ (n + d) - A ^ c ^ n
        = A ^ c ^ n * (A ^ (T * c ^ m * t) - 1) := by
      rw [hgap, pow_add, Matrix.mul_sub, mul_one]
    rw [hZ]
    exact hall.mul_left _
  rw [hns]
  have := hdiff.entry i j
  simpa using this


/-! ### The phase-41 certificate, at last: `c`-adic convergence of `F(c^n)` -/

/-- **The phase-41 crux, PROVED.**  For every prime `c` there is a shift `d ≥ 1` with
`c^n ∣ F(c^(n+d)) − F(c^n)` for every `n ≥ 1`.

Together with `FibonacciAllPrimes.fib_odd_mul` (`F((2J+1)M) = Φ_J(F M)` for odd `M`, applied with
`2J + 1 = c^d`, which is odd for odd `c`) this turns the roadmap's two-index `Φ_J` fixed-point
obstruction into the **single-index** certificate that phase 40's `exists_good_prime_factor`
argument needs at odd `c`: from `c^e ∣ F(c^n) − x` one gets
`c^e ∣ Φ_J(x) − Φ_J(F(c^n)) = Φ_J(x) − F(c^(n+d))`, hence `c^e ∣ Φ_J(x) − x` for `e ≤ n`, and
`FibonacciAllPrimes.fibOddPoly_far` rules that out for `x ≠ 0` (with `x ≠ 0` supplied by
`FibonacciAllPrimes.not_dvd_fib_prime_pow`). -/
theorem exists_shift_fib_prime_pow_congr {c : ℕ} (hc : c.Prime) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ n : ℕ, 1 ≤ n →
      (c : ℤ) ^ n ∣ (Nat.fib (c ^ (n + d)) : ℤ) - (Nat.fib (c ^ n) : ℤ) := by
  have hdet : ¬ (c : ℤ) ∣ FibonacciCovering.fibMat.det := by
    rw [FibonacciCovering.fibMat_det]
    intro hdd
    have h1 : (c : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdd)
    have h2 : (2 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc.two_le
    omega
  obtain ⟨d, s, hd, hsle, hmain⟩ := exists_shift_pow_congr FibonacciCovering.fibMat hc hdet
  have hs1 : s ≤ 1 := by rwa [padicValNat_glCard_two_self hc] at hsle
  refine ⟨d, hd, fun n hn => ?_⟩
  have hkey := hmain n (by omega) 0 1
  rw [FibonacciCovering.fibMat_pow, FibonacciCovering.fibMat_pow] at hkey
  have hkey' : (c : ℤ) ^ (n - s + 1) ∣
      (Nat.fib (c ^ (n + d)) : ℤ) - (Nat.fib (c ^ n) : ℤ) := by simpa using hkey
  exact dvd_trans (pow_dvd_pow _ (by omega)) hkey'

end LeanFormalizations.Mills.FibonacciCoveringAllPrimes

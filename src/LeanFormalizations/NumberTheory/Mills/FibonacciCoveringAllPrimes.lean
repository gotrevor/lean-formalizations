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

/-! ### Step 2 at an odd prime: every value near `F(c^n)` has a good prime factor -/

open LeanFormalizations.Mills.FibonacciAllPrimes in
/-- **Phase 40's step 2, at every odd prime `c ≠ 5`.**  For `n` large relative to `|h|`, some prime
factor `p` of `F(c^n) + h` has `v_c|GL₂(𝔽_p)| ≤ n`.

The certificate is the single-index one built above: if every prime factor had a large `c`-part
then `F(c^n) ≡ s − h (mod c^(n/2))` with `s = ±1`, and writing `x = s − h`,
`c^(n/2) ∣ Φ_J(x) − x` with `2J + 1 = c^d` — impossible, since `Φ_J(x) − x` is a fixed nonzero
integer (`fibOddPoly_far`, with `x ≠ 0` because `c ∤ F(c^n)`). -/
theorem exists_good_prime_factor_odd {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hc5 : c ≠ 5) (h : ℤ) :
    ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (Nat.fib (c ^ n) : ℤ) + h ∧
      padicValNat c (glCard 2 p) ≤ n := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with hx | hx
    · interval_cases c <;> simp_all
    · exact hx
  obtain ⟨d, hd1, hconv⟩ := exists_shift_fib_prime_pow_congr hc
  -- `2J + 1 = c^d`
  obtain ⟨J, hJ⟩ : ∃ J, 2 * J + 1 = c ^ d := by
    obtain ⟨k, hk⟩ := hcodd.pow (n := d)
    exact ⟨k, by omega⟩
  have hJ1 : 1 ≤ J := by
    have h1 : 3 ≤ c ^ d := by
      calc 3 ≤ c := hc3
      _ = c ^ 1 := (pow_one c).symm
      _ ≤ c ^ d := Nat.pow_le_pow_right (by omega) hd1
    omega
  -- the finitely many values `Φ_J(x) − x`, `x ∈ {1−h, −1−h}`, are bounded
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ s : ℤ, (s = 1 ∨ s = -1) →
      |fibOddPoly (s - h) J - (s - h)| ≤ (B : ℤ) := by
    refine ⟨(max |fibOddPoly (1 - h) J - (1 - h)| |fibOddPoly (-1 - h) J - (-1 - h)|).toNat,
      fun s hs => ?_⟩
    have hnn : (0 : ℤ) ≤ max |fibOddPoly (1 - h) J - (1 - h)| |fibOddPoly (-1 - h) J - (-1 - h)| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    rw [Int.toNat_of_nonneg hnn]
    rcases hs with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine eventually_atTop.2 ⟨max 5 (2 * B + 2 * h.natAbs + 8), fun n hn => ?_⟩
  have hn5 : 5 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : 2 * B + 2 * h.natAbs + 8 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨e, hedef⟩ : ∃ e, e = n / 2 := ⟨_, rfl⟩
  have he1 : 1 ≤ e := by omega
  have hen : e ≤ n := by omega
  have heB : (B : ℤ) < (c : ℤ) ^ e := by
    have h1 : B + 2 ≤ e := by omega
    have h2 : e < 2 ^ e := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ e ≤ c ^ e := Nat.pow_le_pow_left (by omega) e
    have : B < c ^ e := by omega
    exact_mod_cast this
  by_contra hcon
  -- `c` is a good prime, so every prime factor is `≠ c` and hence `≡ ±1 (mod c^e)`
  have hfac : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (Nat.fib (c ^ n) : ℤ) + h →
      PmOneMod ((c : ℤ) ^ e) (q : ℤ) := by
    intro q hq hqd
    have hvq : ¬ (padicValNat c (glCard 2 q) ≤ n) := fun hv => hcon ⟨q, hq, hqd, hv⟩
    have hqc : q ≠ c := by
      intro hx
      rw [hx, padicValNat_glCard_two_self hc] at hvq
      omega
    have := pow_dvd_sub_or_add_of_lt_padicValNat_odd hc hc2 hq hqc (n := n) (by omega)
    rw [← hedef] at this
    exact this
  -- so `F(c^n) + h ≡ ±1 (mod c^e)`
  have hfibbig : (h.natAbs : ℤ) < (Nat.fib (c ^ n) : ℤ) := by
    have h1 : (n : ℤ) ≤ (Nat.fib (c ^ n) : ℤ) := by
      have hle : n ≤ Nat.fib (c ^ n) := by
        refine le_trans (Nat.le_fib_self hn5) (Nat.fib_mono ?_)
        calc n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ c ^ n := Nat.pow_le_pow_left (by omega) n
      exact_mod_cast hle
    have h2 : ((2 * B + 2 * h.natAbs + 8 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnB
    push_cast at h2
    omega
  have hval : (0 : ℤ) < (Nat.fib (c ^ n) : ℤ) + h := by
    have h4 : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
    have h5 : -|h| ≤ h := neg_abs_le h
    omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = (Nat.fib (c ^ n) : ℤ) + h :=
    ⟨((Nat.fib (c ^ n) : ℤ) + h).toNat, by omega⟩
  have hM1 : 1 ≤ M := by
    have : (0 : ℤ) < (M : ℤ) := by rw [hM]; exact hval
    exact_mod_cast this
  have hpm : PmOneMod ((c : ℤ) ^ e) ((Nat.fib (c ^ n) : ℤ) + h) := by
    rw [← hM]
    exact PmOneMod.of_prime_factors _ M hM1 (by
      intro q hq hqd
      exact hfac q hq (by rw [← hM]; exact_mod_cast Int.natCast_dvd_natCast.2 hqd))
  obtain ⟨s, hs, hsd⟩ := hpm.exists_sign
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = s - h := ⟨_, rfl⟩
  have hxd : (c : ℤ) ^ e ∣ (Nat.fib (c ^ n) : ℤ) - x := by
    have hrw : (Nat.fib (c ^ n) : ℤ) - x = ((Nat.fib (c ^ n) : ℤ) + h) - s := by rw [hx]; ring
    rw [hrw]; exact hsd
  -- `x = 0` is impossible because `c ∤ F(c^n)`
  have hx0 : x ≠ 0 := by
    intro hxz
    rw [hxz, sub_zero] at hxd
    exact not_dvd_fib_prime_pow hc hc5 n
      (dvd_trans (dvd_pow_self (c : ℤ) (by omega : e ≠ 0)) hxd)
  -- the composition identity turns the congruence into `c^e ∣ Φ_J(x) − x`
  have hcomp : (Nat.fib (c ^ (n + d)) : ℤ) = fibOddPoly (Nat.fib (c ^ n)) J := by
    have hodd : Odd (c ^ n) := hcodd.pow
    have hidx : (2 * J + 1) * c ^ n = c ^ (n + d) := by rw [hJ, pow_add]; ring
    rw [← hidx]
    exact fib_odd_mul J hodd
  have hΦ : (c : ℤ) ^ e ∣ fibOddPoly (Nat.fib (c ^ n)) J - fibOddPoly x J :=
    dvd_fibOddPoly_sub hxd J
  have hshift : (c : ℤ) ^ e ∣ (Nat.fib (c ^ (n + d)) : ℤ) - (Nat.fib (c ^ n) : ℤ) :=
    dvd_trans (pow_dvd_pow _ hen) (hconv n (by omega))
  have hfinal : (c : ℤ) ^ e ∣ fibOddPoly x J - x := by
    have hsum : fibOddPoly x J - x
        = -(fibOddPoly (Nat.fib (c ^ n)) J - fibOddPoly x J)
          + ((Nat.fib (c ^ (n + d)) : ℤ) - (Nat.fib (c ^ n) : ℤ))
          + ((Nat.fib (c ^ n) : ℤ) - x) := by rw [hcomp]; ring
    rw [hsum]
    exact dvd_add (dvd_add (dvd_neg.2 hΦ) hshift) hxd
  -- but `Φ_J(x) − x` is a fixed nonzero integer
  have hne := (fibOddPoly_far hx0 hJ1).1
  have hle := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hfinal)
  have hbd : |fibOddPoly x J - x| ≤ (B : ℤ) := by rw [hx]; exact hB s hs
  omega

/-! ### Steps 3–5 at an odd prime: the covering theorem and prime-free intervals -/

/-- The mechanism at a general prime `c`: a good prime dividing `F(c^m) + h` divides
`F(c^(m + k j)) + h` for every `k`. -/
theorem dvd_fib_prime_pow_add_of_good {c p m : ℕ} {h : ℤ} (hc : c.Prime) (hp : p.Prime)
    (hv : padicValNat c (glCard 2 p) ≤ m) (hd : (p : ℤ) ∣ (Nat.fib (c ^ m) : ℤ) + h) :
    ∃ j, 1 ≤ j ∧ ∀ k : ℕ, (p : ℤ) ∣ (Nat.fib (c ^ (m + k * j)) : ℤ) + h := by
  have hdet : ¬ (p : ℤ) ∣ FibonacciCovering.fibMat.det := by
    rw [FibonacciCovering.fibMat_det]
    intro hdd
    have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdd)
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega
  obtain ⟨j, hj1, hj⟩ :=
    FibonacciCovering.exists_entry_pow_congr_mul FibonacciCovering.fibMat hp hc hdet hv
  refine ⟨j, hj1, fun k => ?_⟩
  have hjk : (p : ℤ) ∣ (Nat.fib (c ^ (m + k * j)) : ℤ) - (Nat.fib (c ^ m) : ℤ) := by
    have hxx := hj k 0 1
    rw [FibonacciCovering.fibMat_pow, FibonacciCovering.fibMat_pow] at hxx
    simpa using hxx
  have hsum := dvd_add hjk hd
  have hrw : (Nat.fib (c ^ (m + k * j)) : ℤ) - (Nat.fib (c ^ m) : ℤ)
      + ((Nat.fib (c ^ m) : ℤ) + h) = (Nat.fib (c ^ (m + k * j)) : ℤ) + h := by ring
  rwa [hrw] at hsum

lemma fib_prime_pow_lt {c a b : ℕ} (hc : 2 ≤ c) (ha : 1 ≤ a) (hab : a < b) :
    Nat.fib (c ^ a) < Nat.fib (c ^ b) := by
  have h2a : 2 ≤ c ^ a := by
    calc 2 ≤ c := hc
    _ = c ^ 1 := (pow_one c).symm
    _ ≤ c ^ a := Nat.pow_le_pow_right (by omega) ha
  have h2b : 2 ≤ c ^ b := le_trans h2a (Nat.pow_le_pow_right (by omega) (by omega))
  exact Nat.fib_strictMonoOn (Set.mem_Ici.2 h2a) (Set.mem_Ici.2 h2b)
    (Nat.pow_lt_pow_right (by omega) hab)

/-- **(D1) for Fibonacci along the tower `c^n`, at every odd prime `c ≠ 5`.** -/
theorem fib_prime_pow_covering {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hc5 : c ≠ 5) (H : ℕ) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h : ℤ, |h| ≤ H →
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ (Nat.fib (c ^ (L * k + m)) : ℤ) + h := by
  classical
  set S : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ) with hS
  have hmemS : ∀ h : ℤ, |h| ≤ (H : ℤ) → h ∈ S := by
    intro h hh
    rw [hS, Finset.mem_Icc]
    have := abs_le.1 hh
    exact ⟨this.1, this.2⟩
  have hall : ∀ᶠ n in atTop, ∀ h ∈ S, ∃ q : ℕ, q.Prime ∧
      (q : ℤ) ∣ (Nat.fib (c ^ n) : ℤ) + h ∧ padicValNat c (glCard 2 q) ≤ n :=
    (Filter.eventually_all_finset S).2 (fun h _ => exists_good_prime_factor_odd hc hc2 hc5 h)
  obtain ⟨m, hm⟩ := eventually_atTop.1 hall
  have hm0 := hm m le_rfl
  set Q : ℤ → ℕ → Prop := fun h q => q.Prime ∧ (q : ℤ) ∣ (Nat.fib (c ^ m) : ℤ) + h ∧
    padicValNat c (glCard 2 q) ≤ m with hQ
  set P : ℤ → ℕ := fun h => if hh : ∃ q, Q h q then hh.choose else 2 with hP
  have hPspec : ∀ h ∈ S, Q h (P h) := by
    intro h hh
    have hex : ∃ q, Q h q := hm0 h hh
    rw [hP]
    simp only [dif_pos hex]
    exact hex.choose_spec
  set R : ℤ → ℕ → Prop := fun h j => 1 ≤ j ∧
    ∀ k : ℕ, (P h : ℤ) ∣ (Nat.fib (c ^ (m + k * j)) : ℤ) + h with hR
  set Jf : ℤ → ℕ := fun h => if hh : ∃ j, R h j then hh.choose else 1 with hJf
  have hJspec : ∀ h ∈ S, R h (Jf h) := by
    intro h hh
    obtain ⟨hpr, hpd, hpv⟩ := hPspec h hh
    have hex : ∃ j, R h j := dvd_fib_prime_pow_add_of_good hc hpr hpv hpd
    rw [hJf]
    simp only [dif_pos hex]
    exact hex.choose_spec
  have hJpos : ∀ h : ℤ, 1 ≤ Jf h := by
    intro h
    rw [hJf]
    by_cases hh : ∃ j, R h j
    · simp only [dif_pos hh]; exact hh.choose_spec.1
    · simp only [dif_neg hh]
      exact le_refl 1
  refine ⟨m, ∏ h ∈ S, Jf h, ?_, P, ?_⟩
  · exact Finset.one_le_prod' (fun h _ => hJpos h)
  intro h hh
  have hhS : h ∈ S := hmemS h hh
  obtain ⟨hpr, hpd, hpv⟩ := hPspec h hhS
  refine ⟨hpr, fun k => ?_⟩
  obtain ⟨t, ht⟩ : Jf h ∣ ∏ h' ∈ S, Jf h' := Finset.dvd_prod_of_mem Jf hhS
  have hkey := (hJspec h hhS).2 (t * k)
  have hidx : m + t * k * Jf h = (∏ h' ∈ S, Jf h') * k + m := by rw [ht]; ring
  rwa [hidx] at hkey

/-- **Prime-free intervals of any fixed length around `F(c^n)`, infinitely often**, at every odd
prime `c ≠ 5`.  Together with phase 40's `c = 2` case this is Theorem C of
`ROADMAP-PRIME-TOWERS.md` for every prime except `c = 5`. -/
theorem fib_prime_pow_prime_free {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hc5 : c ≠ 5) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  obtain ⟨m, L, hL, p, hp⟩ := fib_prime_pow_covering hc hc2 hc5 H
  rw [frequently_atTop]
  intro a
  obtain ⟨K, hK⟩ : ∃ K, K = max a (H + 5) + 1 := ⟨_, rfl⟩
  refine ⟨L * (K + 1) + m, ?_, ?_⟩
  · have h1 : K + 1 ≤ L * (K + 1) := Nat.le_mul_of_pos_left _ hL
    have h2 : a ≤ K := by rw [hK]; omega
    omega
  intro h hh
  obtain ⟨hpr, hpd⟩ := hp h hh
  have hKH : H + 5 ≤ K := by rw [hK]; omega
  have h1 : K ≤ L * K := Nat.le_mul_of_pos_left _ hL
  have hlt12 : L * K + m < L * (K + 1) + m := by
    have hexp : L * (K + 1) = L * K + L := by ring
    omega
  have hfibge : ((L * K + m : ℕ) : ℤ) ≤ (Nat.fib (c ^ (L * K + m)) : ℤ) := by
    have hle : L * K + m ≤ Nat.fib (c ^ (L * K + m)) := by
      refine le_trans (Nat.le_fib_self (by omega)) (Nat.fib_mono ?_)
      calc L * K + m ≤ 2 ^ (L * K + m) := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ c ^ (L * K + m) := Nat.pow_le_pow_left hc.two_le _
    exact_mod_cast hle
  have hHle : (H : ℤ) ≤ ((L * K + m : ℕ) : ℤ) := by exact_mod_cast (by omega : H ≤ L * K + m)
  have habs := abs_le.1 hh
  have hA1 : (0 : ℤ) < (Nat.fib (c ^ (L * K + m)) : ℤ) + h := by omega
  have hgrow : (Nat.fib (c ^ (L * K + m)) : ℤ) < (Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) := by
    exact_mod_cast fib_prime_pow_lt hc.two_le (show 1 ≤ L * K + m by omega) hlt12
  intro hprime
  have hd2 := hpd (K + 1)
  have hd1 := hpd K
  have hnat : ((Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h).natAbs.Prime :=
    Int.prime_iff_natAbs_prime.1 hprime
  have hdnat : p h ∣ ((Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h).natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd2
    simpa using this
  have hpeq : p h = ((Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h).natAbs := by
    rcases hnat.eq_one_or_self_of_dvd _ hdnat with hx | hx
    · exact absurd hx hpr.one_lt.ne'
    · exact hx
  have hA2 : (0 : ℤ) < (Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h := by omega
  have hpval : ((p h : ℤ)) = (Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h := by rw [hpeq]; omega
  have hple : ((p h : ℤ)) ≤ (Nat.fib (c ^ (L * K + m)) : ℤ) + h := Int.le_of_dvd hA1 hd1
  omega

/-! ### The last prime: `c = 5`

`c = 5` is excluded from everything above because `5 ∣ disc`, so the Frobenius congruence
degenerates (`Φ_2 = 25x⁵ − 25x³ + 5x ≡ 0 (mod 5)`).  That degeneration is not an obstacle but a
**gift**: it says `5 ∣ Φ_2(x)` identically, whence `5^n ∣ F(5^n)` and the `5`-adic limit of
`F(5^n)` is `0` rather than a unit.  The filter's window condition `F(5^n) + h ≡ ±1` then reads
`h ≡ ±1 (mod 5^(n/2))` directly, so it fails outright for every `h ≠ ±1` — no `Φ_J` fixed-point
analysis at all.

`h = ±1` are genuine **survivors** of the congruence filter at `c = 5` (the window condition holds
identically), which is why the roadmap routes them through the elementary `F(4k+1) ± 1`
factorizations instead.  They are therefore excluded from the covering statement below; a covering
prime for them cannot exist by this mechanism. -/

open LeanFormalizations.Mills.FibonacciAllPrimes in
/-- `5^n ∣ F(5^n)`.  Immediate from `Φ_2(x) = 25x⁵ − 25x³ + 5x = 5x(5x⁴ − 5x² + 1)`, the `c = 5`
instance of the odd composition identity. -/
theorem five_pow_dvd_fib_five_pow (n : ℕ) : (5 : ℤ) ^ n ∣ (Nat.fib (5 ^ n) : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hodd : Odd (5 ^ n) := (by decide : Odd 5).pow
      have hidx : (2 * 2 + 1) * 5 ^ n = 5 ^ (n + 1) := by rw [pow_succ]; ring
      have hcomp : (Nat.fib (5 ^ (n + 1)) : ℤ) = fibOddPoly (Nat.fib (5 ^ n)) 2 := by
        rw [← hidx]; exact fib_odd_mul 2 hodd
      obtain ⟨x, hx⟩ : ∃ x : ℤ, x = (Nat.fib (5 ^ n) : ℤ) := ⟨_, rfl⟩
      have hpoly : fibOddPoly x 2 = 5 * x * (5 * x ^ 4 - 5 * x ^ 2 + 1) := by
        simp only [fibOddPoly]; ring
      obtain ⟨u, hu⟩ := ih
      refine ⟨u * (5 * x ^ 4 - 5 * x ^ 2 + 1), ?_⟩
      rw [hcomp, ← hx, hpoly, hx, hu, pow_succ]
      ring

/-- **Step 2 at `c = 5`, for every `h ≠ ±1`.**  Since `5^n ∣ F(5^n)`, the window condition on
`F(5^n) + h` is `5^(n/2) ∣ h − s` with `s = ±1`, which fails as soon as `5^(n/2) > |h| + 1`. -/
theorem exists_good_prime_factor_five {h : ℤ} (hh1 : h ≠ 1) (hh2 : h ≠ -1) :
    ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (Nat.fib (5 ^ n) : ℤ) + h ∧
      padicValNat 5 (glCard 2 p) ≤ n := by
  have hfive : Nat.Prime 5 := by norm_num
  refine eventually_atTop.2 ⟨max 5 (2 * h.natAbs + 8), fun n hn => ?_⟩
  have hn5 : 5 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : 2 * h.natAbs + 8 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨e, hedef⟩ : ∃ e, e = n / 2 := ⟨_, rfl⟩
  have he1 : 1 ≤ e := by omega
  have hen : e ≤ n := by omega
  have heB : (h.natAbs : ℤ) + 1 < (5 : ℤ) ^ e := by
    have h1 : h.natAbs + 2 ≤ e := by omega
    have h2 : e < 2 ^ e := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ e ≤ 5 ^ e := Nat.pow_le_pow_left (by omega) e
    have : h.natAbs + 1 < 5 ^ e := by omega
    exact_mod_cast this
  by_contra hcon
  have hfac : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (Nat.fib (5 ^ n) : ℤ) + h →
      PmOneMod ((5 : ℤ) ^ e) (q : ℤ) := by
    intro q hq hqd
    have hvq : ¬ (padicValNat 5 (glCard 2 q) ≤ n) := fun hv => hcon ⟨q, hq, hqd, hv⟩
    have hqc : q ≠ 5 := by
      intro hx
      rw [hx, padicValNat_glCard_two_self hfive] at hvq
      omega
    have := pow_dvd_sub_or_add_of_lt_padicValNat_odd hfive (by norm_num) hq hqc (n := n) (by omega)
    rw [← hedef] at this
    exact this
  have hfibbig : (h.natAbs : ℤ) < (Nat.fib (5 ^ n) : ℤ) := by
    have h1 : (n : ℤ) ≤ (Nat.fib (5 ^ n) : ℤ) := by
      have hle : n ≤ Nat.fib (5 ^ n) := by
        refine le_trans (Nat.le_fib_self hn5) (Nat.fib_mono ?_)
        calc n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ 5 ^ n := Nat.pow_le_pow_left (by norm_num) n
      exact_mod_cast hle
    have h2 : ((2 * h.natAbs + 8 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnB
    push_cast at h2
    omega
  have hval : (0 : ℤ) < (Nat.fib (5 ^ n) : ℤ) + h := by
    have h4 : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
    have h5 : -|h| ≤ h := neg_abs_le h
    omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = (Nat.fib (5 ^ n) : ℤ) + h :=
    ⟨((Nat.fib (5 ^ n) : ℤ) + h).toNat, by omega⟩
  have hM1 : 1 ≤ M := by
    have : (0 : ℤ) < (M : ℤ) := by rw [hM]; exact hval
    exact_mod_cast this
  have hpm : PmOneMod ((5 : ℤ) ^ e) ((Nat.fib (5 ^ n) : ℤ) + h) := by
    rw [← hM]
    exact PmOneMod.of_prime_factors _ M hM1 (by
      intro q hq hqd
      exact hfac q hq (by rw [← hM]; exact_mod_cast Int.natCast_dvd_natCast.2 hqd))
  obtain ⟨s, hs, hsd⟩ := hpm.exists_sign
  -- `5^e ∣ F(5^n)` turns the window condition into `5^e ∣ h − s`
  have hdvdF : (5 : ℤ) ^ e ∣ (Nat.fib (5 ^ n) : ℤ) :=
    dvd_trans (pow_dvd_pow 5 hen) (five_pow_dvd_fib_five_pow n)
  have hhs : (5 : ℤ) ^ e ∣ h - s := by
    have hrw : h - s = ((Nat.fib (5 ^ n) : ℤ) + h - s) - (Nat.fib (5 ^ n) : ℤ) := by ring
    rw [hrw]
    exact dvd_sub hsd hdvdF
  have hne : h - s ≠ 0 := by rcases hs with rfl | rfl <;> intro hx <;> omega
  have hle := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hhs)
  have habs : |h - s| ≤ (h.natAbs : ℤ) + 1 := by
    have h4 : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
    have h5 : -|h| ≤ h := neg_abs_le h
    have h6 : h ≤ |h| := le_abs_self h
    rcases hs with rfl | rfl <;> rw [abs_le] <;> omega
  omega

/-! ### The assembly, factored out

Steps 3–5 depend on the prime `c` only through the step-2 input, so state them once for an
arbitrary finite set `S` of shifts.  `c = 5` then reuses them verbatim with
`S = Icc (−H) H \ {1, −1}`. -/

/-- **Steps 3–4, for an arbitrary finite set of shifts.**  Given that each shift in `S` eventually
has a good prime factor, one index `m` and one modulus `L` serve them all. -/
theorem covering_of_good {c : ℕ} (hc : c.Prime) (S : Finset ℤ)
    (hgood : ∀ h ∈ S, ∀ᶠ n in atTop, ∃ q : ℕ, q.Prime ∧
      (q : ℤ) ∣ (Nat.fib (c ^ n) : ℤ) + h ∧ padicValNat c (glCard 2 q) ≤ n) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h ∈ S,
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ (Nat.fib (c ^ (L * k + m)) : ℤ) + h := by
  classical
  obtain ⟨m, hm⟩ := eventually_atTop.1 ((Filter.eventually_all_finset S).2 hgood)
  have hm0 := hm m le_rfl
  set Q : ℤ → ℕ → Prop := fun h q => q.Prime ∧ (q : ℤ) ∣ (Nat.fib (c ^ m) : ℤ) + h ∧
    padicValNat c (glCard 2 q) ≤ m with hQ
  set P : ℤ → ℕ := fun h => if hh : ∃ q, Q h q then hh.choose else 2 with hP
  have hPspec : ∀ h ∈ S, Q h (P h) := by
    intro h hh
    have hex : ∃ q, Q h q := hm0 h hh
    rw [hP]
    simp only [dif_pos hex]
    exact hex.choose_spec
  set R : ℤ → ℕ → Prop := fun h j => 1 ≤ j ∧
    ∀ k : ℕ, (P h : ℤ) ∣ (Nat.fib (c ^ (m + k * j)) : ℤ) + h with hR
  set Jf : ℤ → ℕ := fun h => if hh : ∃ j, R h j then hh.choose else 1 with hJf
  have hJspec : ∀ h ∈ S, R h (Jf h) := by
    intro h hh
    obtain ⟨hpr, hpd, hpv⟩ := hPspec h hh
    have hex : ∃ j, R h j := dvd_fib_prime_pow_add_of_good hc hpr hpv hpd
    rw [hJf]
    simp only [dif_pos hex]
    exact hex.choose_spec
  have hJpos : ∀ h : ℤ, 1 ≤ Jf h := by
    intro h
    rw [hJf]
    by_cases hh : ∃ j, R h j
    · simp only [dif_pos hh]; exact hh.choose_spec.1
    · simp only [dif_neg hh]
      exact le_refl 1
  refine ⟨m, ∏ h ∈ S, Jf h, Finset.one_le_prod' (fun h _ => hJpos h), P, ?_⟩
  intro h hhS
  obtain ⟨hpr, hpd, hpv⟩ := hPspec h hhS
  refine ⟨hpr, fun k => ?_⟩
  obtain ⟨t, ht⟩ : Jf h ∣ ∏ h' ∈ S, Jf h' := Finset.dvd_prod_of_mem Jf hhS
  have hkey := (hJspec h hhS).2 (t * k)
  have hidx : m + t * k * Jf h = (∏ h' ∈ S, Jf h') * k + m := by rw [ht]; ring
  rwa [hidx] at hkey

/-- **Step 5, for an arbitrary finite set of shifts.**  A covering prime forces non-primality,
by comparing the values at `k = K` and `k = K + 1`. -/
theorem prime_free_of_covering {c : ℕ} (hc : c.Prime) (S : Finset ℤ) (H : ℕ)
    (hSb : ∀ h ∈ S, |h| ≤ (H : ℤ))
    (hcov : ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h ∈ S,
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ (Nat.fib (c ^ (L * k + m)) : ℤ) + h) :
    ∃ᶠ n in atTop, ∀ h ∈ S, ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  obtain ⟨m, L, hL, p, hp⟩ := hcov
  rw [frequently_atTop]
  intro a
  obtain ⟨K, hK⟩ : ∃ K, K = max a (H + 5) + 1 := ⟨_, rfl⟩
  refine ⟨L * (K + 1) + m, ?_, ?_⟩
  · have h1 : K + 1 ≤ L * (K + 1) := Nat.le_mul_of_pos_left _ hL
    have h2 : a ≤ K := by rw [hK]; omega
    omega
  intro h hhS
  obtain ⟨hpr, hpd⟩ := hp h hhS
  have hh := hSb h hhS
  have hKH : H + 5 ≤ K := by rw [hK]; omega
  have h1 : K ≤ L * K := Nat.le_mul_of_pos_left _ hL
  have hlt12 : L * K + m < L * (K + 1) + m := by
    have hexp : L * (K + 1) = L * K + L := by ring
    omega
  have hfibge : ((L * K + m : ℕ) : ℤ) ≤ (Nat.fib (c ^ (L * K + m)) : ℤ) := by
    have hle : L * K + m ≤ Nat.fib (c ^ (L * K + m)) := by
      refine le_trans (Nat.le_fib_self (by omega)) (Nat.fib_mono ?_)
      calc L * K + m ≤ 2 ^ (L * K + m) := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ c ^ (L * K + m) := Nat.pow_le_pow_left hc.two_le _
    exact_mod_cast hle
  have hHle : (H : ℤ) ≤ ((L * K + m : ℕ) : ℤ) := by exact_mod_cast (by omega : H ≤ L * K + m)
  have habs := abs_le.1 hh
  have hA1 : (0 : ℤ) < (Nat.fib (c ^ (L * K + m)) : ℤ) + h := by omega
  have hgrow : (Nat.fib (c ^ (L * K + m)) : ℤ) < (Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) := by
    exact_mod_cast fib_prime_pow_lt hc.two_le (show 1 ≤ L * K + m by omega) hlt12
  intro hprime
  have hd2 := hpd (K + 1)
  have hd1 := hpd K
  have hnat : ((Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h).natAbs.Prime :=
    Int.prime_iff_natAbs_prime.1 hprime
  have hdnat : p h ∣ ((Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h).natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hd2
    simpa using this
  have hpeq : p h = ((Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h).natAbs := by
    rcases hnat.eq_one_or_self_of_dvd _ hdnat with hx | hx
    · exact absurd hx hpr.one_lt.ne'
    · exact hx
  have hA2 : (0 : ℤ) < (Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h := by omega
  have hpval : ((p h : ℤ)) = (Nat.fib (c ^ (L * (K + 1) + m)) : ℤ) + h := by rw [hpeq]; omega
  have hple : ((p h : ℤ)) ≤ (Nat.fib (c ^ (L * K + m)) : ℤ) + h := Int.le_of_dvd hA1 hd1
  omega

/-- The shifts `|h| ≤ H` other than the two `c = 5` survivors `h = ±1`. -/
noncomputable def fiveShifts (H : ℕ) : Finset ℤ := ((Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 1).erase (-1)

lemma mem_fiveShifts {H : ℕ} {h : ℤ} (hb : |h| ≤ (H : ℤ)) (h1 : h ≠ 1) (h2 : h ≠ -1) :
    h ∈ fiveShifts H := by
  rw [fiveShifts, Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc]
  have := abs_le.1 hb
  exact ⟨h2, h1, this.1, this.2⟩

lemma fiveShifts_bound {H : ℕ} {h : ℤ} (hh : h ∈ fiveShifts H) : |h| ≤ (H : ℤ) := by
  rw [fiveShifts, Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hh
  exact abs_le.2 ⟨hh.2.2.1, hh.2.2.2⟩

lemma fiveShifts_ne {H : ℕ} {h : ℤ} (hh : h ∈ fiveShifts H) : h ≠ 1 ∧ h ≠ -1 := by
  rw [fiveShifts, Finset.mem_erase, Finset.mem_erase] at hh
  exact ⟨hh.2.1, hh.1⟩

/-- **(D1) at `c = 5`, for every shift other than the two survivors `h = ±1`.** -/
theorem fib_five_pow_covering (H : ℕ) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h : ℤ, |h| ≤ H → h ≠ 1 → h ≠ -1 →
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ (Nat.fib (5 ^ (L * k + m)) : ℤ) + h := by
  obtain ⟨m, L, hL, p, hp⟩ := covering_of_good (by norm_num : Nat.Prime 5) (fiveShifts H)
    (fun h hh => exists_good_prime_factor_five (fiveShifts_ne hh).1 (fiveShifts_ne hh).2)
  exact ⟨m, L, hL, p, fun h hb h1 h2 => hp h (mem_fiveShifts hb h1 h2)⟩

/-- **Prime-free intervals around `F(5^n)`, infinitely often**, away from the two survivors. -/
theorem fib_five_pow_prime_free (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → h ≠ 1 → h ≠ -1 →
      ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + h) := by
  have hfr := prime_free_of_covering (by norm_num : Nat.Prime 5) (fiveShifts H) H
    (fun h hh => fiveShifts_bound hh) (covering_of_good (by norm_num : Nat.Prime 5) (fiveShifts H)
      (fun h hh => exists_good_prime_factor_five (fiveShifts_ne hh).1 (fiveShifts_ne hh).2))
  refine hfr.mono (fun n hn h hb h1 h2 => hn h (mem_fiveShifts hb h1 h2))

/-! ### The `c = 5` survivors `h = ±1`, by elementary factorisation

`h = ±1` cannot be reached by a covering prime (they are filter survivors at `c = 5`), but they do
not need one: `5^n ≡ 1 (mod 4)`, and writing `5^n = 4k+1`,

  `F(4k+1) + 1 = F(2k+1) · L(2k)`,   `F(4k+1) − 1 = F(2k) · L(2k+1)`,

both of which are just `F(4k+1) = F(2k+1)² + F(2k)²` (`Nat.fib_two_mul_add_one`) plus Cassini
`F(2k+1)² − F(2k+1)F(2k) − F(2k)² = 1`.  So no new identity is needed beyond `fib_cassini`. -/

lemma not_prime_of_mul {a b : ℤ} (ha : 1 < a) (hb : 1 < b) : ¬ Prime (a * b) := by
  intro hp
  have hnat : (a * b).natAbs.Prime := Int.prime_iff_natAbs_prime.1 hp
  have hmul : (a * b).natAbs = a.natAbs * b.natAbs := Int.natAbs_mul a b
  have ha2 : 2 ≤ a.natAbs := by
    have : |a| = (a.natAbs : ℤ) := Int.abs_eq_natAbs a
    have h2 : (2 : ℤ) ≤ |a| := by rw [abs_of_pos (by omega : (0:ℤ) < a)]; omega
    omega
  have hb2 : 2 ≤ b.natAbs := by
    have : |b| = (b.natAbs : ℤ) := Int.abs_eq_natAbs b
    have h2 : (2 : ℤ) ≤ |b| := by rw [abs_of_pos (by omega : (0:ℤ) < b)]; omega
    omega
  rw [hmul] at hnat
  rcases (Nat.prime_mul_iff.1 hnat) with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- `5^n = 4k + 1` with `k ≥ 6`, for `n ≥ 2`. -/
lemma five_pow_eq_four_mul_add_one {n : ℕ} (hn : 2 ≤ n) : ∃ k, 6 ≤ k ∧ 5 ^ n = 4 * k + 1 := by
  have hmod : 5 ^ n % 4 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h25 : 25 ≤ 5 ^ n := by
    calc (25 : ℕ) = 5 ^ 2 := by norm_num
    _ ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨5 ^ n / 4, by omega, by omega⟩

/-- **The `c = 5` survivors are composite anyway.**  `F(5^n) ± 1` is not prime for any `n ≥ 2`. -/
theorem fib_five_pow_pm_one_not_prime {n : ℕ} (hn : 2 ≤ n) :
    ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + 1) ∧ ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + (-1)) := by
  obtain ⟨k, hk6, hk⟩ := five_pow_eq_four_mul_add_one hn
  obtain ⟨F0, hF0⟩ : ∃ F0 : ℤ, F0 = (Nat.fib (2 * k) : ℤ) := ⟨_, rfl⟩
  obtain ⟨F1, hF1⟩ : ∃ F1 : ℤ, F1 = (Nat.fib (2 * k + 1) : ℤ) := ⟨_, rfl⟩
  -- `F(4k+1) = F(2k+1)² + F(2k)²`
  have hsum : (Nat.fib (5 ^ n) : ℤ) = F1 ^ 2 + F0 ^ 2 := by
    have hidx : 2 * (2 * k) + 1 = 5 ^ n := by omega
    have h := Nat.fib_two_mul_add_one (2 * k)
    rw [hidx] at h
    rw [hF1, hF0]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
  -- Cassini at the even index `2k`
  have hcas : F1 ^ 2 - F1 * F0 - F0 ^ 2 = 1 := by
    have h := FibonacciCovering.fib_cassini (2 * k)
    have hpar : (-1 : ℤ) ^ (2 * k) = 1 :=
      Even.neg_one_pow ⟨k, by ring⟩
    rw [hpar] at h
    rw [hF1, hF0]
    exact h
  -- both factors are large
  have hF0big : 144 ≤ F0 := by
    have h1 : Nat.fib 12 ≤ Nat.fib (2 * k) := Nat.fib_mono (by omega)
    have h2 : Nat.fib 12 = 144 := by decide
    rw [hF0]
    have : (144 : ℕ) ≤ Nat.fib (2 * k) := by omega
    exact_mod_cast this
  have hF01 : F0 < F1 := by
    rw [hF0, hF1]
    have : Nat.fib (2 * k) < Nat.fib (2 * k + 1) :=
      Nat.fib_lt_fib_succ (by omega)
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · -- `F(5^n) + 1 = F1 · (2F1 − F0)`
    have hfac : (Nat.fib (5 ^ n) : ℤ) + 1 = F1 * (2 * F1 - F0) := by
      rw [hsum]; linarith [hcas]
    rw [hfac]
    exact not_prime_of_mul (by omega) (by omega)
  · -- `F(5^n) − 1 = F0 · (2F0 + F1)`
    have hfac : (Nat.fib (5 ^ n) : ℤ) + (-1) = F0 * (2 * F0 + F1) := by
      rw [hsum]; linarith [hcas]
    rw [hfac]
    exact not_prime_of_mul (by omega) (by omega)

/-- **Theorem C at `c = 5`, in full**: prime-free intervals of any fixed length around `F(5^n)`,
infinitely often, with no exceptional shifts. -/
theorem fib_five_pow_prime_free_all (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + h) := by
  have hpm : ∀ᶠ n in atTop, ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + 1) ∧
      ¬ Prime ((Nat.fib (5 ^ n) : ℤ) + (-1)) :=
    eventually_atTop.2 ⟨2, fun n hn => fib_five_pow_pm_one_not_prime hn⟩
  refine ((fib_five_pow_prime_free H).and_eventually hpm).mono ?_
  rintro n ⟨hrest, hp1, hm1⟩ h hb
  by_cases h1 : h = 1
  · rw [h1]; exact hp1
  by_cases h2 : h = -1
  · rw [h2]; exact hm1
  exact hrest h hb h1 h2

/-! ### Theorem C, assembled over every prime -/

/-- **Theorem C of `ROADMAP-PRIME-TOWERS.md`, complete.**  For every prime `c` and every `H`, the
interval `[F(c^n) − H, F(c^n) + H]` contains no prime for infinitely many `n`.

This is Saito's *"We desire to remove the reversibility"* (arXiv:2504.14968) for the Fibonacci
tower `c^n`, which is not reversible.  The three regimes are genuinely different:
* `c = 2` — phase 40, certificate `2^(n+1) ∣ 5F(2^n)² + 3`;
* odd `c ≠ 5` — phase 41, certificate the `c`-adic convergence `c^n ∣ F(c^(n+d)) − F(c^n)`
  together with the `Φ_J` fixed-point obstruction;
* `c = 5` — the `5`-adic limit is `0`, so the window fails outright for `h ≠ ±1`, and the two
  survivors `h = ±1` fall to the `F(4k+1) ± 1` factorisations. -/
theorem fib_prime_pow_prime_free_all {c : ℕ} (hc : c.Prime) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  by_cases hc2 : c = 2
  · subst hc2; exact FibonacciCovering.fib_two_pow_prime_free H
  by_cases hc5 : c = 5
  · subst hc5; exact fib_five_pow_prime_free_all H
  exact fib_prime_pow_prime_free hc hc2 hc5 H

end LeanFormalizations.Mills.FibonacciCoveringAllPrimes


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

end LeanFormalizations.Mills.FibonacciCoveringAllPrimes

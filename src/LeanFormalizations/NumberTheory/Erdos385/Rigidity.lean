/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #385 / #430: elementary rigidity (phase E1)

`F(n) = max{m + p(m) : m < n composite}`, with `p(m)` the least prime factor.  #385(i) asks whether
`F(n) > n` for all large `n`; #430 is equivalent (Adenwalla).  Call `n` **bad** when `F(n) ≤ n`.

The definition of `F` copies formal-conjectures' `Erdos385.F` (`ErdosProblems/385.lean`), and
`terms` copies `Erdos430.terms` from formal-conjectures PR #5261.  formal-conjectures is not a
dependency, so `Composite` is restated here exactly as its `Nat.Composite`.

## Frozen statements (do not edit; prove them)

* `le_F`, `bad_iff_F_eq` (CKS, Tao blog comments 2024-08-21/23): `n ≤ F n` for `n ≥ 5`, so bad
  means `F n = n`.
* `bad_iff_forall_sub` (unpacking): bad iff every composite `n − a` has `p(n − a) ≤ a`.
* `prime_sub_one_of_bad` (CKS): bad ⇒ `n − 1` prime.
* `primorial_dvd_of_minFac_sub_le` (**Lemma R**, `DOOR-EXCEPTIONAL-ERDOS-385.md`): if
  `p(n − p) ≤ p` for every prime `p ≤ y` and `y + 2 ≤ n`, then `y# ∣ n`.
* `exists_prime_pair_of_bad` (**Corollary R′**): a bad `n < y#` has `n − 1` prime and `n − p`
  prime for some prime `3 ≤ p ≤ y`.
* `exists_composite_mem_terms_iff` (#430 ⟺ #385(i), pointwise) and `erdos430_iff_erdos385_i`.

Data check: `scripts/test_erdos385_rigidity.py` (each statement by brute force on small `n`).

## Route

* `le_F`: if `n − 1` is composite, `m = n − 1` gives `m + p(m) ≥ n + 1`.  Otherwise `n − 1` is an
  odd prime, so `n − 2 ≥ 4` is even, hence composite, and `(n − 2) + 2 = n`.  The set under `sSup`
  is bounded by `2n` (`p(m) ≤ m`), so `le_csSup` applies.
* `bad_iff_forall_sub`: `m = n − a`, then `m + p(m) ≤ n ⟺ p(m) ≤ a`.
* `prime_sub_one_of_bad`: `a = 1`; `p(m) ≥ 2 > 1`.
* Lemma R: strong induction over the primes `p ≤ y`.  `n − 2 ≥ 2` and `p(n − 2) ≤ 2` give `2 ∣ n`.
  If every prime `< p` divides `n` and `q = p(n − p) ≤ p` with `q < p`, then `q ∣ n` and
  `q ∣ n − p` force `q ∣ p`, impossible; so `q = p` and `p ∣ n`.  Then `primorial` is the product
  of distinct primes, each dividing `n` (`Finset.prod_primes_dvd`).
* R′: if `n − p` is not prime for every prime `3 ≤ p ≤ y`, badness gives `p(n − p) ≤ p` at each
  such `p` (and at `p = 2`, since `n` is even); Lemma R gives `y# ∣ n`, contradicting `n < y#`.
  When `n < y + 2`, apply Lemma R at `y' = n − 2` instead and check the small cases.
* #430: `m ∈ terms n` and `m` not prime ⟺ `m` composite with `p(m) > n − m` ⟺ `m + p(m) > n`.
-/

namespace LeanFormalizations.Erdos385

open Filter

/-- Composite, exactly as formal-conjectures' `Nat.Composite`. -/
abbrev Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- `F(n) = max{m + p(m) : m < n composite}`, copied from formal-conjectures' `Erdos385.F`. -/
noncomputable def F (n : ℕ) : ℕ := sSup {m + m.minFac | (m < n) (_ : Composite m)}

/-- `n` is bad when `F(n) ≤ n`: no composite `m < n` reaches past `n`. -/
def Bad (n : ℕ) : Prop := F n ≤ n

/-- The terms of #430's sequence, copied from `Erdos430.terms` (formal-conjectures PR #5261). -/
def terms (n : ℕ) : Finset ℕ :=
  (Finset.Ioo 1 n).filter fun m => ∀ p ∈ m.primeFactors, n - m < p

/-- **CKS.**  `F(n) ≥ n` once a composite below `n` exists. -/
theorem le_F {n : ℕ} (hn : 5 ≤ n) : n ≤ F n := by
  sorry

/-- **CKS.**  Bad means exactly `F(n) = n`. -/
theorem bad_iff_F_eq {n : ℕ} (hn : 5 ≤ n) : Bad n ↔ F n = n := by
  sorry

/-- Badness position by position: every composite `n − a` has least prime factor `≤ a`. -/
theorem bad_iff_forall_sub {n : ℕ} (hn : 5 ≤ n) :
    Bad n ↔ ∀ a, 1 ≤ a → a < n → Composite (n - a) → (n - a).minFac ≤ a := by
  sorry

/-- **CKS.**  A bad `n` sits just above a prime. -/
theorem prime_sub_one_of_bad {n : ℕ} (hn : 5 ≤ n) (h : Bad n) : (n - 1).Prime := by
  sorry

/-- **Lemma R (rigidity).**  If `p(n − p) ≤ p` for every prime `p ≤ y`, then `y# ∣ n`.
Equivalently, the only class mod `y#` blocking every position in `[2, y]` is `0`. -/
theorem primorial_dvd_of_minFac_sub_le {n y : ℕ} (hy : y + 2 ≤ n)
    (h : ∀ p, p.Prime → p ≤ y → (n - p).minFac ≤ p) : primorial y ∣ n := by
  sorry

/-- **Corollary R′.**  A bad `n < y#` is the top of a prime pair `n − p < n − 1` with
`3 ≤ p ≤ y`; so every bad `n` has a prime pair of gap `< (1 + o(1)) log n` just below it. -/
theorem exists_prime_pair_of_bad {n y : ℕ} (hn : 5 ≤ n) (h : Bad n) (hy : n < primorial y) :
    (n - 1).Prime ∧ ∃ p, p.Prime ∧ 3 ≤ p ∧ p ≤ y ∧ (n - p).Prime := by
  sorry

/-- **Lemma R, dichotomy form** (what the E2 count uses): a bad `n ≥ y + 2` is either a multiple
of `y#` or the top of a prime pair `n − p < n − 1` with `3 ≤ p ≤ y`. -/
theorem primorial_dvd_or_exists_prime_pair_of_bad {n y : ℕ} (hn : 5 ≤ n) (h : Bad n)
    (hy : y + 2 ≤ n) :
    primorial y ∣ n ∨ ∃ p, p.Prime ∧ 3 ≤ p ∧ p ≤ y ∧ (n - p).Prime := by
  sorry

/-- **#430 ⟺ #385(i), pointwise.**  #430's sequence for `n` has a composite term iff `n` is
not bad. -/
theorem exists_composite_mem_terms_iff {n : ℕ} (hn : 5 ≤ n) :
    (∃ m ∈ terms n, ¬ m.Prime) ↔ ¬ Bad n := by
  sorry

/-- **#430 ⟺ #385(i)** (Adenwalla), in the shapes of formal-conjectures' `erdos_430` and
`erdos_385.parts.i`. -/
theorem erdos430_iff_erdos385_i :
    (∀ᶠ n in atTop, ¬ ∀ m ∈ terms n, m.Prime) ↔ (∀ᶠ n in atTop, n < F n) := by
  sorry

end LeanFormalizations.Erdos385

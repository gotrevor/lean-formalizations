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


theorem bddAbove_F (n : ℕ) :
    BddAbove {m + m.minFac | (m < n) (_ : Composite m)} := by
  refine ⟨2 * n, ?_⟩
  rintro x ⟨m, hm, hc, rfl⟩
  have := Nat.minFac_le (show 0 < m by omega)
  omega

theorem add_minFac_le_F {n m : ℕ} (hm : m < n) (hc : Composite m) :
    m + m.minFac ≤ F n :=
  le_csSup (bddAbove_F n) ⟨m, hm, hc, rfl⟩

private lemma composite_four : Composite 4 := ⟨by norm_num, by norm_num⟩

private lemma F_le_iff {n k : ℕ} (hn : 5 ≤ n) :
    F n ≤ k ↔ ∀ m, m < n → Composite m → m + m.minFac ≤ k := by
  unfold F
  rw [csSup_le_iff (bddAbove_F n) ⟨_, 4, by omega, composite_four, rfl⟩]
  constructor
  · intro h m hm hc; exact h _ ⟨m, hm, hc, rfl⟩
  · rintro h x ⟨m, hm, hc, rfl⟩; exact h m hm hc

private lemma two_le_minFac {m : ℕ} (hm : m ≠ 1) : 2 ≤ m.minFac :=
  (Nat.minFac_prime hm).two_le

private lemma prime_dvd_primorial {p k : ℕ} (hp : p.Prime) (hk : p ≤ k) : p ∣ primorial k :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)

/-- **CKS.**  `F(n) ≥ n` once a composite below `n` exists. -/
theorem le_F {n : ℕ} (hn : 5 ≤ n) : n ≤ F n := by
  by_cases hp : (n - 1).Prime
  · have hodd := hp.eq_two_or_odd
    have hc : Composite (n - 2) := ⟨by omega, fun h2 => by
      rcases h2.eq_two_or_odd with h | h <;> omega⟩
    have h2 : (n - 2).minFac = 2 := Nat.minFac_eq_two_iff _ |>.2 (by omega)
    have := add_minFac_le_F (n := n) (m := n - 2) (by omega) hc
    omega
  · have := add_minFac_le_F (n := n) (m := n - 1) (by omega) ⟨by omega, hp⟩
    have := two_le_minFac (m := n - 1) (by omega)
    omega

/-- **CKS.**  Bad means exactly `F(n) = n`. -/
theorem bad_iff_F_eq {n : ℕ} (hn : 5 ≤ n) : Bad n ↔ F n = n := by
  have := le_F hn
  unfold Bad; omega

/-- Badness position by position: every composite `n − a` has least prime factor `≤ a`. -/
theorem bad_iff_forall_sub {n : ℕ} (hn : 5 ≤ n) :
    Bad n ↔ ∀ a, 1 ≤ a → a < n → Composite (n - a) → (n - a).minFac ≤ a := by
  unfold Bad
  rw [F_le_iff hn]
  constructor
  · intro h a ha1 ha hc
    have := h (n - a) (by omega) hc
    omega
  · intro h m hm hc
    have := h (n - m) (by have := hc.1; omega) (by have := hc.1; omega)
      (by rwa [show n - (n - m) = m by omega])
    rw [show n - (n - m) = m by omega] at this
    omega

/-- **CKS.**  A bad `n` sits just above a prime. -/
theorem prime_sub_one_of_bad {n : ℕ} (hn : 5 ≤ n) (h : Bad n) : (n - 1).Prime := by
  by_contra hp
  have := (bad_iff_forall_sub hn).1 h 1 le_rfl (by omega) ⟨by omega, hp⟩
  have := two_le_minFac (m := n - 1) (by omega)
  omega

/-- **Lemma R (rigidity).**  If `p(n − p) ≤ p` for every prime `p ≤ y`, then `y# ∣ n`.
Equivalently, the only class mod `y#` blocking every position in `[2, y]` is `0`. -/
theorem primorial_dvd_of_minFac_sub_le {n y : ℕ} (hy : y + 2 ≤ n)
    (h : ∀ p, p.Prime → p ≤ y → (n - p).minFac ≤ p) : primorial y ∣ n := by
  have key : ∀ p, p.Prime → p ≤ y → p ∣ n := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp hpy
      have hq := Nat.minFac_prime (n := n - p) (by omega)
      have hle := h p hp hpy
      have hdvd : (n - p).minFac ∣ n - p := Nat.minFac_dvd _
      rcases lt_or_eq_of_le hle with hlt | heq
      · exfalso
        have hqn := ih _ hlt hq (by omega)
        have : (n - p).minFac ∣ p := by
          have := Nat.dvd_sub hqn hdvd
          rwa [show n - (n - p) = p by omega] at this
        rcases (Nat.dvd_prime hp).1 this with h1 | h1
        · exact hq.one_lt.ne' h1
        · omega
      · rw [heq] at hdvd
        have := Nat.dvd_add hdvd (dvd_refl p)
        rwa [show n - p + p = n by omega] at this
  exact Finset.prod_primes_dvd n (fun p hp => (Finset.mem_filter.1 hp).2.prime)
    (fun p hp => key p (Finset.mem_filter.1 hp).2
      (by have := Finset.mem_range.1 (Finset.mem_filter.1 hp).1; omega))

/-- **Corollary R′.**  A bad `n < y#` is the top of a prime pair `n − p < n − 1` with
`3 ≤ p ≤ y`; so every bad `n` has a prime pair of gap `< (1 + o(1)) log n` just below it. -/
theorem exists_prime_pair_of_bad {n y : ℕ} (hn : 5 ≤ n) (h : Bad n) (hy : n < primorial y) :
    (n - 1).Prime ∧ ∃ p, p.Prime ∧ 3 ≤ p ∧ p ≤ y ∧ (n - p).Prime := by
  have hp1 := prime_sub_one_of_bad hn h
  refine ⟨hp1, ?_⟩
  by_contra hne
  push Not at hne
  have hmin : ∀ p, p.Prime → p ≤ y → p + 2 ≤ n → (n - p).minFac ≤ p := by
    intro p hp hpy hpn
    by_cases hc : (n - p).Prime
    · exfalso
      rcases hp.eq_two_or_odd with h2 | h2
      · subst h2
        rcases hc.eq_two_or_odd with h3 | h3 <;> rcases hp1.eq_two_or_odd with h4 | h4 <;> omega
      · exact absurd hc (hne p hp (by have := hp.two_le; omega) hpy)
    · exact (bad_iff_forall_sub hn).1 h p (by have := hp.two_le; omega) (by omega)
        ⟨by omega, hc⟩
  have hR := primorial_dvd_of_minFac_sub_le (n := n) (y := min y (n - 2)) (by omega)
    (fun p hp hpy => hmin p hp (by omega) (by omega))
  by_cases hyn : y ≤ n - 2
  · rw [min_eq_left hyn] at hR
    have := Nat.le_of_dvd (by omega) hR
    omega
  · rw [min_eq_right (by omega)] at hR
    obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ((n - 2) / 2) (by omega)
    have hpn : p ∣ n := (prime_dvd_primorial hp (by omega)).trans hR
    have h2n : 2 ∣ n := (prime_dvd_primorial Nat.prime_two (by omega)).trans hR
    by_cases hp2 : p = 2
    · subst hp2
      have : n ≤ 5 := by omega
      have : n = 5 := by omega
      subst this; norm_num at hp1
    · have hcop : Nat.Coprime 2 p :=
        (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      have h2p := hcop.mul_dvd_of_dvd_of_dvd h2n hpn
      have := Nat.le_of_dvd (by omega) h2p
      obtain ⟨k, hk⟩ := h2p
      have hk1 : k = 1 := by
        rcases k with _ | _ | k
        · omega
        · rfl
        · have : n ≤ 2 * p + 1 := by omega
          nlinarith
      subst hk1
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      exact hne p hp hp3 (by omega) (by rwa [show n - p = p by omega])

/-- **Lemma R, dichotomy form** (what the E2 count uses): a bad `n ≥ y + 2` is either a multiple
of `y#` or the top of a prime pair `n − p < n − 1` with `3 ≤ p ≤ y`. -/
theorem primorial_dvd_or_exists_prime_pair_of_bad {n y : ℕ} (hn : 5 ≤ n) (h : Bad n)
    (hy : y + 2 ≤ n) :
    primorial y ∣ n ∨ ∃ p, p.Prime ∧ 3 ≤ p ∧ p ≤ y ∧ (n - p).Prime := by
  have hp1 := prime_sub_one_of_bad hn h
  by_contra hne
  push Not at hne
  apply hne.1
  apply primorial_dvd_of_minFac_sub_le hy
  intro p hp hpy
  by_cases hc : (n - p).Prime
  · exfalso
    rcases hp.eq_two_or_odd with h2 | h2
    · subst h2
      rcases hc.eq_two_or_odd with h3 | h3 <;> rcases hp1.eq_two_or_odd with h4 | h4 <;> omega
    · exact hne.2 p hp (by have := hp.two_le; omega) hpy hc
  · exact (bad_iff_forall_sub hn).1 h p (by have := hp.two_le; omega) (by omega)
      ⟨by omega, hc⟩

/-- **#430 ⟺ #385(i), pointwise.**  #430's sequence for `n` has a composite term iff `n` is
not bad. -/
theorem exists_composite_mem_terms_iff {n : ℕ} (hn : 5 ≤ n) :
    (∃ m ∈ terms n, ¬ m.Prime) ↔ ¬ Bad n := by
  have key : ∀ m, m < n → Composite m →
      ((∀ p ∈ m.primeFactors, n - m < p) ↔ n < m + m.minFac) := by
    intro m hm hc
    have hmf : m.minFac ∈ m.primeFactors :=
      Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by have := hc.1; omega), Nat.minFac_dvd _,
        by have := hc.1; omega⟩
    constructor
    · intro hall; have := hall _ hmf; omega
    · intro hlt p hp
      have := Nat.minFac_le_of_dvd (Nat.mem_primeFactors.1 hp).1.two_le
        (Nat.mem_primeFactors.1 hp).2.1
      omega
  unfold Bad
  rw [not_le]
  constructor
  · rintro ⟨m, hm, hmp⟩
    obtain ⟨hm1, hall⟩ := Finset.mem_filter.1 hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hm1
    have hc : Composite m := ⟨h1, hmp⟩
    exact lt_of_lt_of_le ((key m h2 hc).1 hall) (add_minFac_le_F h2 hc)
  · intro hlt
    by_contra hall
    push Not at hall
    have : F n ≤ n := by
      rw [F_le_iff hn]
      intro m hm hc
      by_contra hgt
      push Not at hgt
      exact hc.2 (hall m (Finset.mem_filter.2
        ⟨Finset.mem_Ioo.2 ⟨hc.1, hm⟩, (key m hm hc).2 hgt⟩))
    omega

/-- **#430 ⟺ #385(i)** (Adenwalla), in the shapes of formal-conjectures' `erdos_430` and
`erdos_385.parts.i`. -/
theorem erdos430_iff_erdos385_i :
    (∀ᶠ n in atTop, ¬ ∀ m ∈ terms n, m.Prime) ↔ (∀ᶠ n in atTop, n < F n) := by
  have h5 : ∀ᶠ n in atTop, 5 ≤ n := eventually_ge_atTop 5
  constructor
  · intro h
    filter_upwards [h, h5] with n hn hn5
    push Not at hn
    have := (exists_composite_mem_terms_iff hn5).1 hn
    unfold Bad at this; omega
  · intro h
    filter_upwards [h, h5] with n hn hn5
    have := (exists_composite_mem_terms_iff hn5).2 (by unfold Bad; omega)
    push Not; exact this

end LeanFormalizations.Erdos385

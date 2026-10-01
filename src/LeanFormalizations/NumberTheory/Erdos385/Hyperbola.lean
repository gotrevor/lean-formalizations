/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Rigidity

/-!
# Erdős #385: the hyperbola criterion and the binary reformulation (phase E9a)

A witness for `n` (a composite `m < n` with `m + p(m) > n`) is determined by its least prime
factor `p`: `m` is the largest multiple of `p` below `n`, so `m = p ⌊n/p⌋` and `p ∤ n`.  Hence:

* `good_iff_exists_prime_floor`: for `n ≥ 5`, `n` is good iff some prime `p` with `p ∤ n` has
  `p ≤ ⌊n/p⌋` and `minFac ⌊n/p⌋ ≥ p`;
* `good_of_prime_pair`: primes `p < q` with `pq < n < pq + p` make `n` good (the case
  `⌊n/p⌋ = q` prime);
* `HyperbolaPrimePairs`, `eventually_not_bad_of_hyperbolaPrimePairs`, `erdos430_of_hyperbolaPrimePairs`:
  if prime pairs on the strip `pq < n < pq + p` exist for all large `n`, then #385(i) and #430
  hold.

**Why the reformulation matters (direction, not a result).**  Near `p ≈ √n` the map
`p ↦ ⌊n/p⌋` is a reflection, `⌊n/p⌋ = 2A + c(p) − p` with `A = ⌊√n⌋` and `c` a slowly increasing
step function.  So `HyperbolaPrimePairs` is a Goldbach problem: some even `2A + 2j` must be
`p + q` with `p` in a window of length `≍ √A/√j` placed at distance `≍ √(Aj)` below `A`.  That is
a binary problem, which is why #385(i) resists every method (Maze row "for every n via the
hyperbola prime pairs").

**Evidence** (`scripts/erdos385-hyperbola-probe.py`, checks against the definition of `F` on
`[5, 20000]` and against the known bad `n` 267672, 267680): the prime-pair count
`W(n) = #{(p, q) : p < q primes, pq < n < pq + p}` vanishes for 491 values `n ≤ 10^8`, the
largest being `267689`, nine above the last bad `n`; `min W = 7` on `[10^6, 10^7)` and `27` on
`[10^7, 10^8)`, and the mean of `W` tracks `3.9 √n / log² n`.  So prime pairs alone, the binary
witnesses, already cover every `n` from just past the last bad one.

Frozen: these statements.  `good_iff_exists_prime_floor` and `good_of_prime_pair` are elementary
(use `bad_iff_forall_sub`, `add_minFac_le_F`, `Nat.minFac_le_of_dvd`).
-/

namespace LeanFormalizations.Erdos385

open Filter

/-- **The hyperbola criterion.**  `n ≥ 5` is good iff some prime `p ∤ n` has `⌊n/p⌋ ≥ p` with no
prime factor below `p`; the witness is `m = p ⌊n/p⌋`. -/
theorem good_iff_exists_prime_floor {n : ℕ} (hn : 5 ≤ n) :
    ¬ Bad n ↔ ∃ p, p.Prime ∧ ¬ p ∣ n ∧ p ≤ n / p ∧ p ≤ (n / p).minFac := by
  constructor
  · intro hgood
    have hex : ∃ a, 1 ≤ a ∧ a < n ∧ Composite (n - a) ∧ a < (n - a).minFac := by
      by_contra hne
      push Not at hne
      exact hgood ((bad_iff_forall_sub hn).2 fun a h1 h2 h3 => hne a h1 h2 h3)
    obtain ⟨a, ha1, han, hc, hlt⟩ := hex
    set m := n - a with hm
    have hm1 : m ≠ 1 := by have := hc.1; omega
    have hpp : m.minFac.Prime := Nat.minFac_prime hm1
    set p := m.minFac with hpdef
    have hpm : p ∣ m := Nat.minFac_dvd m
    obtain ⟨k, hk⟩ := hpm
    have hp2 := hpp.two_le
    have hnk : n = p * k + a := by omega
    have hdiv : n / p = k := by
      rw [hnk, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hlt]; simp
    have hsq : p * p ≤ m := by
      have := Nat.minFac_sq_le_self (by have := hc.1; omega : 0 < m) hc.2
      simpa [pow_two] using this
    have hpk : p ≤ k := by
      by_contra h; push Not at h
      have : p * k < p * p := Nat.mul_lt_mul_of_pos_left h (by omega)
      omega
    refine ⟨p, hpp, ?_, by omega, ?_⟩
    · intro hd
      have h1 : p ∣ p * k := dvd_mul_right p k
      have : p ∣ a := (Nat.dvd_add_right h1).1 (hnk ▸ hd)
      have := Nat.le_of_dvd (by omega) this
      omega
    · rw [hdiv]
      have hk1 : k ≠ 1 := by omega
      exact Nat.minFac_le_of_dvd (Nat.minFac_prime hk1).two_le
        (hk ▸ dvd_mul_of_dvd_right (Nat.minFac_dvd k) p)
  · rintro ⟨p, hp, hpn, hple, hmin⟩ hbad
    set k := n / p
    have hp2 := hp.two_le
    have hk2 : 2 ≤ k := by omega
    have hlt : p * k < n := by
      have := Nat.div_mul_le_self n p
      rcases this.lt_or_eq with h | h
      · rw [mul_comm]; exact h
      · exact absurd ⟨k, by rw [mul_comm]; exact h.symm⟩ hpn
    have hgt : n < p * k + p := by
      have := Nat.lt_div_mul_add (a := n) (b := p) (by omega)
      rw [mul_comm]; exact this
    have hc : Composite (p * k) := ⟨by nlinarith, Nat.not_prime_mul (by omega) (by omega)⟩
    have hmf : (p * k).minFac = p := by
      apply le_antisymm (Nat.minFac_le_of_dvd hp2 (dvd_mul_right p k))
      have hq := Nat.minFac_prime (show p * k ≠ 1 by nlinarith)
      rcases (Nat.Prime.dvd_mul hq).1 (Nat.minFac_dvd (p * k)) with h | h
      · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm
      · exact hmin.trans (Nat.minFac_le_of_dvd hq.two_le h)
    have := add_minFac_le_F hlt hc
    unfold Bad at hbad
    omega

/-- **Prime-pair witnesses.**  Primes `p < q` with `pq < n < pq + p` make `n` good. -/
theorem good_of_prime_pair {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (h1 : p * q < n) (h2 : n < p * q + p) : ¬ Bad n := by
  intro hbad
  have hc : Composite (p * q) := ⟨by nlinarith [hp.two_le, hq.two_le],
    Nat.not_prime_mul hp.ne_one hq.ne_one⟩
  have hmf : (p * q).minFac = p := by
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q))
    have hr := Nat.minFac_prime hc.1.ne'
    rcases (Nat.Prime.dvd_mul hr).1 (Nat.minFac_dvd (p * q)) with h | h
    · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hr hp).1 h).symm
    · rw [(Nat.prime_dvd_prime_iff_eq hr hq).1 h]; omega
  have := add_minFac_le_F h1 hc
  unfold Bad at hbad
  omega

/-- **Prime pairs on the hyperbolic strip, eventually** (a binary problem; open).  Believed: the
expected count is `≍ √n / log² n`, and the data above show no failure past `267689`. -/
def HyperbolaPrimePairs : Prop :=
  ∀ᶠ n in atTop, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p * q < n ∧ n < p * q + p

/-- Edge: prime pairs on the strip give #385(i). -/
theorem eventually_not_bad_of_hyperbolaPrimePairs (h : HyperbolaPrimePairs) :
    ∀ᶠ n in atTop, n < F n := by
  filter_upwards [h] with n ⟨p, q, hp, hq, hpq, h1, h2⟩
  have := good_of_prime_pair hp hq hpq h1 h2
  unfold Bad at this; omega

/-- Edge: prime pairs on the strip give #430 (via `erdos430_iff_erdos385_i`). -/
theorem erdos430_of_hyperbolaPrimePairs (h : HyperbolaPrimePairs) :
    ∀ᶠ n in atTop, ¬ ∀ m ∈ terms n, m.Prime := by
  exact erdos430_iff_erdos385_i.2 (eventually_not_bad_of_hyperbolaPrimePairs h)

end LeanFormalizations.Erdos385

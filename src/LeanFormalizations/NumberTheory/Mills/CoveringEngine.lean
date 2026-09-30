/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciCovering
import LeanFormalizations.NumberTheory.Mills.LucasPrimePow
import LeanFormalizations.NumberTheory.Mills.LucasCoveringAllPrimes

/-!
# Phase 41: the Theorem C engine — covering and prime-free intervals along `c^n`, any matrix

Phase 40 proved (D1) and prime-free intervals for `F(2^n)`.  Its mechanism is general.  If every
value `ℓ(A^(c^n)) + h` (for `|h| ≤ H`, `n` large) has a prime factor `p` with a small `c`-part of
`|GL_d(𝔽_p)|`, then one `m` and one period `L` work for all `h` at once.  See
`ROADMAP-PRIME-TOWERS.md` §1 Theorem C.

## Route
1. `covering_of_good`: refactor phase 40's steps 3–4 (`exists_entry_pow_congr_mul`, one `m` via
   `Filter.eventually_all_finset`, `L = ∏` periods) to a general `A : Matrix (Fin d) (Fin d) ℤ`
   and a `ℤ`-linear functional `ℓ` (entries and the trace are both `ℓ`).  Linearity makes the entrywise
   congruence `A^(c^(m+kj)) ≡ A^(c^m) (mod p)` pass to `ℓ`.
2. `prime_free_of_good`: phase 40's step 5 (compare `k = K` and `K + 1`), assuming only
   `|ℓ(A^(c^n))| → ∞`.
3. Lucas instance: `lucasV_good` gives the hypothesis of step 1 for `A = lucasM P`, `ℓ = trace`,
   odd prime `c ∤ P`.
   - **Window at a single `n` is impossible for large `n`.**  If every prime factor `q` of
     `V(c^n) + h` has `v_c(glCard 2 q) > n`, then each `q ≡ ±1 (mod c^(n/2))`
     (`FibonacciPrimePow.pow_dvd_sub_or_add_of_lt_padicValNat`), hence so is the product, and
     `V(c^n) ≡ x (mod c^(n/2))` with `x ∈ {±1 − h}`.
   - Descend with the Gauss-type congruence `V(c^(k+1)) ≡ V(c^k) (mod c^(k+1))` (prove it from
     `lucasV_mul_odd`: `V_c(y) − V_c(x) ≡ 0 (mod c^(k+1))` when `y ≡ x (mod c^k)`, because
     `V_c(x, −1) = x^c + c·g(x)`).  This gives `V(c^r) ≡ x (mod c^r)` for `r ≈ n/2`, then
     `lucasV x (−1) c ≡ x (mod c^(r−1))`.
   - `lucasV_neg_one_growth` makes `lucasV x (−1) c − x` a nonzero integer bounded in terms of
     `|h|`, unless `x = 0`, which contradicts `lucasV_prime_pow_mod` (`V ≡ P ≢ 0`).  So `r`, hence
     `n`, is bounded.
   - Also handle prime factors dividing `det = −1` (none) and the prime `c` itself
     (`v_c(glCard 2 c) = 0`, so `c` is always good).
4. Fibonacci instance at odd `c ≠ 5`: same, with phase 37's `fibOddPoly` at `2j + 1 = c²`
   (`F(c^(k+2)) = Φ_j(F(c^k))`; `Φ_j` is odd, so both `Φ_j(x) ∓ x ≠ 0` for `x ≠ 0` by
   `fibOddPoly_far`) and `not_dvd_fib_prime_pow`.  The descent uses
   `F(c^(k+1)) ≡ ±F(c^k) (mod c^(k+1))`; prove whichever sign-agnostic form is convenient, e.g.
   `F(c^(k+2)) ≡ F(c^k) (mod c^(k+1))` from `fib_odd_mul`.
5. `fib_prime_pow_prime_free`: every prime `c ≠ 5` (`c = 2` is phase 40).

Frozen: every statement below; statements of all earlier Mills phase files and `Literature/`.
Do not mark new declarations `private`.
-/

namespace LeanFormalizations.Mills.CoveringEngine

open LeanFormalizations.Mills.ThreeAdic LeanFormalizations.Mills.LucasPrimePow Filter
open LeanFormalizations.Mills.FibonacciCoveringAllPrimes
open LeanFormalizations.Mills.LucasCoveringAllPrimes

/-! ### Generic plumbing -/

/-- A `ℤ`-linear functional is divisible by anything that divides every entry. -/
lemma dvd_linearMap_of_entries {d : ℕ} (l : Matrix (Fin d) (Fin d) ℤ →ₗ[ℤ] ℤ) {a : ℤ}
    {M : Matrix (Fin d) (Fin d) ℤ} (h : ∀ i j, a ∣ M i j) : a ∣ l M := by
  obtain ⟨B, hB⟩ := SmulDvd.of_entries a M h
  exact ⟨l B, by rw [hB, map_smul, smul_eq_mul]⟩

/-- **Steps 3–4, fully abstract.**  `G` is the "good prime" predicate; `hmech` promotes a good
prime at one index to the whole arithmetic progression through it. -/
theorem covering_of_mech (t : ℕ → ℤ) (S : Finset ℤ) (G : ℕ → ℕ → Prop)
    (hmech : ∀ (p m : ℕ) (h : ℤ), p.Prime → G p m → (p : ℤ) ∣ t m + h →
      ∃ j, 1 ≤ j ∧ ∀ k : ℕ, (p : ℤ) ∣ t (m + k * j) + h)
    (hgood : ∀ h ∈ S, ∀ᶠ n in atTop, ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ t n + h ∧ G q n) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h ∈ S,
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ t (L * k + m) + h := by
  classical
  obtain ⟨m, hm⟩ := eventually_atTop.1 ((Filter.eventually_all_finset S).2 hgood)
  have hm0 := hm m le_rfl
  set Q : ℤ → ℕ → Prop := fun h q => q.Prime ∧ (q : ℤ) ∣ t m + h ∧ G q m with hQ
  set P : ℤ → ℕ := fun h => if hh : ∃ q, Q h q then hh.choose else 2 with hP
  have hPspec : ∀ h ∈ S, Q h (P h) := by
    intro h hh
    have hex : ∃ q, Q h q := hm0 h hh
    rw [hP]
    simp only [dif_pos hex]
    exact hex.choose_spec
  set R : ℤ → ℕ → Prop := fun h j => 1 ≤ j ∧
    ∀ k : ℕ, (P h : ℤ) ∣ t (m + k * j) + h with hR
  set Jf : ℤ → ℕ := fun h => if hh : ∃ j, R h j then hh.choose else 1 with hJf
  have hJspec : ∀ h ∈ S, R h (Jf h) := by
    intro h hh
    obtain ⟨hpr, hpd, hpv⟩ := hPspec h hh
    have hex : ∃ j, R h j := hmech (P h) m h hpr hpv hpd
    rw [hJf]
    simp only [dif_pos hex]
    exact hex.choose_spec
  have hJpos : ∀ h : ℤ, 1 ≤ Jf h := by
    intro h
    rw [hJf]
    by_cases hh : ∃ j, R h j
    · simp only [dif_pos hh]; exact hh.choose_spec.1
    · simp only [dif_neg hh]; exact le_refl 1
  refine ⟨m, ∏ h ∈ S, Jf h, Finset.one_le_prod' (fun h _ => hJpos h), P, ?_⟩
  intro h hhS
  obtain ⟨hpr, hpd, hpv⟩ := hPspec h hhS
  refine ⟨hpr, fun k => ?_⟩
  obtain ⟨u, hu⟩ : Jf h ∣ ∏ h' ∈ S, Jf h' := Finset.dvd_prod_of_mem Jf hhS
  have hkey := (hJspec h hhS).2 (u * k)
  have hidx : m + u * k * Jf h = (∏ h' ∈ S, Jf h') * k + m := by rw [hu]; ring
  rwa [hidx] at hkey

/-- The shift set `{h : |h| ≤ H}`. -/
noncomputable def shifts (H : ℕ) : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ)

lemma mem_shifts {H : ℕ} {h : ℤ} (hb : |h| ≤ (H : ℤ)) : h ∈ shifts H := by
  rw [shifts, Finset.mem_Icc]
  exact ⟨(abs_le.1 hb).1, (abs_le.1 hb).2⟩

lemma shifts_bound {H : ℕ} {h : ℤ} (hh : h ∈ shifts H) : |h| ≤ (H : ℤ) := by
  rw [shifts, Finset.mem_Icc] at hh
  exact abs_le.2 hh

/-- **The engine: (D1) along `c^n`** for any integer matrix and linear functional. -/
theorem covering_of_good {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (ℓ : Matrix (Fin d) (Fin d) ℤ →ₗ[ℤ] ℤ) {c : ℕ} (hc : c.Prime) (H : ℕ)
    (hgood : ∀ h : ℤ, |h| ≤ H → ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ A.det ∧
      (p : ℤ) ∣ ℓ (A ^ (c ^ n)) + h ∧ padicValNat c (glCard d p) ≤ n) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h : ℤ, |h| ≤ H →
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ ℓ (A ^ (c ^ (L * k + m))) + h := by
  classical
  obtain ⟨m, L, hL, p, hp⟩ := covering_of_mech (fun n => ℓ (A ^ (c ^ n))) (shifts H)
    (fun q n => ¬ (q : ℤ) ∣ A.det ∧ padicValNat c (glCard d q) ≤ n)
    (fun q n h hq hG hdvd => by
      obtain ⟨j, hj1, hj⟩ :=
        FibonacciCovering.exists_entry_pow_congr_mul A hq hc hG.1 hG.2
      refine ⟨j, hj1, fun k => ?_⟩
      have hdiff : (q : ℤ) ∣ ℓ (A ^ c ^ (n + k * j)) - ℓ (A ^ c ^ (n : ℕ)) := by
        rw [← map_sub]
        exact dvd_linearMap_of_entries ℓ (fun a b => by
          have := hj k a b
          simpa using this)
      have hsum := dvd_add hdiff hdvd
      have e : ℓ (A ^ c ^ (n + k * j)) - ℓ (A ^ c ^ (n : ℕ)) + (ℓ (A ^ c ^ (n : ℕ)) + h)
          = ℓ (A ^ c ^ (n + k * j)) + h := by ring
      rwa [e] at hsum)
    (fun h hh => by
      refine ((hgood h (shifts_bound hh)).mono ?_)
      rintro n ⟨q, hq, hqd, hqdvd, hqv⟩
      exact ⟨q, hq, hqdvd, hqd, hqv⟩)
  exact ⟨m, L, hL, p, fun h hb => hp h (mem_shifts hb)⟩

/-- **The engine: prime-free intervals** of half-width `H` around `ℓ(A^(c^n))`, infinitely often. -/
theorem prime_free_of_good {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (ℓ : Matrix (Fin d) (Fin d) ℤ →ₗ[ℤ] ℤ) {c : ℕ} (hc : c.Prime) (H : ℕ)
    (hgrow : Tendsto (fun n : ℕ => |ℓ (A ^ (c ^ n))|) atTop atTop)
    (hgood : ∀ h : ℤ, |h| ≤ H → ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ A.det ∧
      (p : ℤ) ∣ ℓ (A ^ (c ^ n)) + h ∧ padicValNat c (glCard d p) ≤ n) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (ℓ (A ^ (c ^ n)) + h) := by
  obtain ⟨m, L, hL, p, hp⟩ := covering_of_good A ℓ hc H hgood
  have := prime_free_of_covering_seq (t := fun n => ℓ (A ^ (c ^ n))) (S := shifts H) (H := H)
    (fun h hh => shifts_bound hh) hgrow hL (fun h hh => hp h (shifts_bound hh))
  exact this.mono (fun n hn h hb => hn h (mem_shifts hb))

/-- **Prime-free intervals around `V_(c^n)(P, −1)`** (e.g. Lucas numbers `P = 1`), odd prime `c ∤ P`. -/
theorem lucasV_prime_pow_prime_free {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP : ¬ (c : ℤ) ∣ P) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (lucasV P (-1) (c ^ n) + h) := by
  sorry

/-- **Prime-free intervals around `F(c^n)`**, every prime `c ≠ 5`. -/
theorem fib_prime_pow_prime_free {c : ℕ} (hc : c.Prime) (h5 : c ≠ 5) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  rcases eq_or_ne c 2 with rfl | hc2
  · exact FibonacciCovering.fib_two_pow_prime_free H
  · exact FibonacciCoveringAllPrimes.fib_prime_pow_prime_free hc hc2 h5 H

end LeanFormalizations.Mills.CoveringEngine

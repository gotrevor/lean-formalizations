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


/-! ### The Lucas companion sequence `V(c^n)` -/

lemma dvd_trace_of_entries {d : ℕ} {a : ℤ} {M : Matrix (Fin d) (Fin d) ℤ}
    (h : ∀ i j, a ∣ M i j) : a ∣ M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.dvd_sum (fun i _ => h i i)

/-- **`c`-adic convergence of the companion sequence.**  There is a shift `d ≥ 1` with
`V(c^(n+d)) ≡ V(c^n) (mod c^n)` for every `n ≥ 1`. -/
theorem exists_shift_lucasV_prime_pow_congr {c : ℕ} (hc : c.Prime) (P : ℤ) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ n : ℕ, 1 ≤ n →
      (c : ℤ) ^ n ∣ lucasV P (-1) (c ^ (n + d)) - lucasV P (-1) (c ^ n) := by
  have hdet : ¬ (c : ℤ) ∣ (lucasM P).det := by
    rw [lucasM_det]
    intro hdd
    have h1 : (c : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdd)
    have h2 : (2 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc.two_le
    omega
  obtain ⟨d, s, hd, hsle, hmain⟩ := exists_shift_pow_congr (lucasM P) hc hdet
  have hs1 : s ≤ 1 := by rwa [padicValNat_glCard_two_self hc] at hsle
  refine ⟨d, hd, fun n hn => ?_⟩
  have hkey : (c : ℤ) ^ (n - s + 1) ∣
      lucasV P (-1) (c ^ (n + d)) - lucasV P (-1) (c ^ n) := by
    rw [← trace_lucasM_pow, ← trace_lucasM_pow, ← Matrix.trace_sub]
    exact dvd_trace_of_entries (fun i j => by
      have := hmain n (by omega) i j
      simpa using this)
  exact dvd_trans (pow_dvd_pow _ (by omega)) hkey

/-- **Step 2 for the companion sequence.**  For `n` large relative to `|h|`, some prime factor of
`V(c^n) + h` has a small `c`-part of `|GL₂(𝔽_p)|`.

If every prime factor were bad then `V(c^n) ≡ x (mod c^(n/2))` with `x = s − h`, `s = ±1`; the
composition `V(c^(n+d)) = V_(c^d)(V(c^n))` and the `c`-adic convergence above turn this into
`c^(n/2) ∣ V_(c^d)(x) − x`, a fixed nonzero integer (`lucasV_neg_one_growth`, with `x ≠ 0` because
`c ∤ V(c^n)`). -/
theorem exists_good_lucasV_prime_factor {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP1 : 1 ≤ P) (hPc : ¬ (c : ℤ) ∣ P) (h : ℤ) :
    ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ lucasV P (-1) (c ^ n) + h ∧
      padicValNat c (glCard 2 p) ≤ n := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with hx | hx
    · interval_cases c <;> simp_all
    · exact hx
  obtain ⟨d, hd1, hconv⟩ := exists_shift_lucasV_prime_pow_congr hc P
  have hWodd : Odd (c ^ d) := hcodd.pow
  have hW3 : 3 ≤ c ^ d := by
    calc 3 ≤ c := hc3
    _ = c ^ 1 := (pow_one c).symm
    _ ≤ c ^ d := Nat.pow_le_pow_right (by omega) hd1
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ s : ℤ, (s = 1 ∨ s = -1) →
      |lucasV (s - h) (-1) (c ^ d) - (s - h)| ≤ (B : ℤ) := by
    refine ⟨(max |lucasV (1 - h) (-1) (c ^ d) - (1 - h)|
      |lucasV (-1 - h) (-1) (c ^ d) - (-1 - h)|).toNat, fun s hs => ?_⟩
    have hnn : (0 : ℤ) ≤ max |lucasV (1 - h) (-1) (c ^ d) - (1 - h)|
        |lucasV (-1 - h) (-1) (c ^ d) - (-1 - h)| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    rw [Int.toNat_of_nonneg hnn]
    rcases hs with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hVn : ∀ n : ℕ, (n : ℤ) ≤ lucasV P (-1) (c ^ n) := by
    intro n
    have h1 : n ≤ c ^ n :=
      le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by omega) n)
    have h2 : ((c ^ n : ℕ) : ℤ) ≤ lucasV P (-1) (c ^ n) :=
      nat_le_lucasV hP1 (Nat.one_le_pow _ _ hc.pos)
    have h3 : (n : ℤ) ≤ ((c ^ n : ℕ) : ℤ) := by exact_mod_cast h1
    omega
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
  have hfac : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ lucasV P (-1) (c ^ n) + h →
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
  have hbig : (h.natAbs : ℤ) < lucasV P (-1) (c ^ n) := by
    have h1 := hVn n
    have h2 : ((2 * B + 2 * h.natAbs + 8 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnB
    push_cast at h2
    omega
  have hval : (0 : ℤ) < lucasV P (-1) (c ^ n) + h := by
    have h4 : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
    have h5 : -|h| ≤ h := neg_abs_le h
    omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = lucasV P (-1) (c ^ n) + h :=
    ⟨(lucasV P (-1) (c ^ n) + h).toNat, by omega⟩
  have hM1 : 1 ≤ M := by
    have : (0 : ℤ) < (M : ℤ) := by rw [hM]; exact hval
    exact_mod_cast this
  have hpm : PmOneMod ((c : ℤ) ^ e) (lucasV P (-1) (c ^ n) + h) := by
    rw [← hM]
    exact PmOneMod.of_prime_factors _ M hM1 (by
      intro q hq hqd
      exact hfac q hq (by rw [← hM]; exact_mod_cast Int.natCast_dvd_natCast.2 hqd))
  obtain ⟨s, hs, hsd⟩ := hpm.exists_sign
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = s - h := ⟨_, rfl⟩
  have hxd : (c : ℤ) ^ e ∣ lucasV P (-1) (c ^ n) - x := by
    have hrw : lucasV P (-1) (c ^ n) - x = (lucasV P (-1) (c ^ n) + h) - s := by rw [hx]; ring
    rw [hrw]; exact hsd
  have hx0 : x ≠ 0 := by
    intro hxz
    rw [hxz, sub_zero] at hxd
    have hcd : (c : ℤ) ∣ lucasV P (-1) (c ^ n) :=
      dvd_trans (dvd_pow_self (c : ℤ) (by omega : e ≠ 0)) hxd
    exact hPc (by
      have := dvd_sub hcd (lucasV_prime_pow_mod hc hc2 P n)
      simpa using this)
  have hcomp : lucasV P (-1) (c ^ (n + d)) = lucasV (lucasV P (-1) (c ^ n)) (-1) (c ^ d) := by
    have hidx : c ^ d * c ^ n = c ^ (n + d) := by rw [← pow_add]; ring_nf
    rw [← hidx]
    exact lucasV_mul_odd P (c ^ d) hcodd.pow
  have hΦ : (c : ℤ) ^ e ∣
      lucasV (lucasV P (-1) (c ^ n)) (-1) (c ^ d) - lucasV x (-1) (c ^ d) :=
    dvd_lucasV_sub hxd (c ^ d)
  have hshift : (c : ℤ) ^ e ∣ lucasV P (-1) (c ^ (n + d)) - lucasV P (-1) (c ^ n) :=
    dvd_trans (pow_dvd_pow _ hen) (hconv n (by omega))
  have hfinal : (c : ℤ) ^ e ∣ lucasV x (-1) (c ^ d) - x := by
    have hsum : lucasV x (-1) (c ^ d) - x
        = -(lucasV (lucasV P (-1) (c ^ n)) (-1) (c ^ d) - lucasV x (-1) (c ^ d))
          + (lucasV P (-1) (c ^ (n + d)) - lucasV P (-1) (c ^ n))
          + (lucasV P (-1) (c ^ n) - x) := by rw [hcomp]; ring
    rw [hsum]
    exact dvd_add (dvd_add (dvd_neg.2 hΦ) hshift) hxd
  have hgr := lucasV_neg_one_growth hWodd hW3 hx0
  have hne : lucasV x (-1) (c ^ d) - x ≠ 0 := by
    intro hz
    have : |lucasV x (-1) (c ^ d)| = |x| := by rw [show lucasV x (-1) (c ^ d) = x by omega]
    omega
  have hle := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hfinal)
  have hbd : |lucasV x (-1) (c ^ d) - x| ≤ (B : ℤ) := by rw [hx]; exact hB s hs
  omega

/-- The `P ≥ 1` case of the theorem below, obtained from the engine with `A = lucasM P` and
`ℓ = trace`. -/
theorem lucasV_prime_pow_prime_free_pos {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP1 : 1 ≤ P) (hPc : ¬ (c : ℤ) ∣ P) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (lucasV P (-1) (c ^ n) + h) := by
  have hc2' : 2 ≤ c := hc.two_le
  have htr : ∀ n : ℕ,
      (Matrix.traceLinearMap (Fin 2) ℤ ℤ) ((lucasM P) ^ (c ^ n)) = lucasV P (-1) (c ^ n) :=
    fun n => trace_lucasM_pow P _
  have hVn : ∀ n : ℕ, (n : ℤ) ≤ lucasV P (-1) (c ^ n) := by
    intro n
    have h1 : n ≤ c ^ n :=
      le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by omega) n)
    have h2 : ((c ^ n : ℕ) : ℤ) ≤ lucasV P (-1) (c ^ n) :=
      nat_le_lucasV hP1 (Nat.one_le_pow _ _ hc.pos)
    have h3 : (n : ℤ) ≤ ((c ^ n : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  have hgrow : Tendsto
      (fun n : ℕ => |(Matrix.traceLinearMap (Fin 2) ℤ ℤ) ((lucasM P) ^ (c ^ n))|) atTop atTop := by
    refine tendsto_atTop_mono (f := fun n : ℕ => (n : ℤ)) (fun n => ?_)
      tendsto_natCast_atTop_atTop
    rw [htr n]
    have := hVn n
    have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    rw [abs_of_nonneg (by have := hVn n; omega)]
    exact hVn n
  have hgood : ∀ h : ℤ, |h| ≤ H → ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧
      ¬ (p : ℤ) ∣ (lucasM P).det ∧
      (p : ℤ) ∣ (Matrix.traceLinearMap (Fin 2) ℤ ℤ) ((lucasM P) ^ (c ^ n)) + h ∧
      padicValNat c (glCard 2 p) ≤ n := by
    intro h _
    refine (exists_good_lucasV_prime_factor hc hc2 hP1 hPc h).mono ?_
    rintro n ⟨p, hp, hpd, hpv⟩
    refine ⟨p, hp, ?_, by rw [htr n]; exact hpd, hpv⟩
    rw [lucasM_det]
    intro hdd
    have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdd)
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega
  refine (prime_free_of_good (lucasM P) (Matrix.traceLinearMap (Fin 2) ℤ ℤ) hc H hgrow
    hgood).mono ?_
  intro n hn h hb
  rw [← htr n]
  exact hn h hb

/-- **Prime-free intervals around `V_(c^n)(P, −1)`** (e.g. Lucas numbers `P = 1`), odd prime `c ∤ P`. -/
theorem lucasV_prime_pow_prime_free {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {P : ℤ}
    (hP : ¬ (c : ℤ) ∣ P) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (lucasV P (-1) (c ^ n) + h) := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hP0 : P ≠ 0 := fun hz => hP (by simp [hz])
  rcases lt_or_gt_of_ne hP0 with hneg | hpos
  · have hP' : ¬ (c : ℤ) ∣ -P := fun hd => hP (dvd_neg.1 hd)
    refine (lucasV_prime_pow_prime_free_pos hc hc2 (by omega : (1:ℤ) ≤ -P) hP' H).mono ?_
    intro n hn h hb hpr
    refine hn (-h) (by rwa [abs_neg]) ?_
    have hflip : lucasV (-P) (-1) (c ^ n) = -lucasV P (-1) (c ^ n) := by
      rw [lucasV_neg, (hcodd.pow (n := n)).neg_one_pow]
      ring
    rw [hflip, show -lucasV P (-1) (c ^ n) + -h = -(lucasV P (-1) (c ^ n) + h) by ring]
    exact hpr.neg
  · exact lucasV_prime_pow_prime_free_pos hc hc2 hpos hP H

/-- **Prime-free intervals around `F(c^n)`**, every prime `c ≠ 5`. -/
theorem fib_prime_pow_prime_free {c : ℕ} (hc : c.Prime) (h5 : c ≠ 5) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime ((Nat.fib (c ^ n) : ℤ) + h) := by
  rcases eq_or_ne c 2 with rfl | hc2
  · exact FibonacciCovering.fib_two_pow_prime_free H
  · exact FibonacciCoveringAllPrimes.fib_prime_pow_prime_free hc hc2 h5 H

end LeanFormalizations.Mills.CoveringEngine

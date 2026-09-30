/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.FibonacciCoveringAllPrimes
import LeanFormalizations.NumberTheory.Mills.LucasUnitAllPrimes

/-!
# Theorem C for every Lucas sequence `U(P, ±1)`: prime-free intervals around `U(c^n)`

Phases 40–41 proved Dubickas's (D1) and prime-free intervals for the Fibonacci tower `F(c^n)` at
every prime.  Everything there except the `c = 2` and `c = 5` certificates was already generic; this
file carries the odd-`c` argument over to an arbitrary Lucas sequence `U_N(P, Q)` with `Q = ±1` and
`D = P² − 4Q ≥ 5`, reusing phase 38's `lucasOddPoly` composition and phase 41's `c`-adic
convergence theorem.

## Two reusable abstractions
The assembly (steps 3–5) depends on the sequence only through a *mechanism* hypothesis and a growth
hypothesis, so it is stated here for an abstract `t : ℕ → ℤ`:
`covering_of_good_seq` and `prime_free_of_covering_seq`.  The latter improves on phase 40's version:
it needs only `|t n| → ∞`, not monotonicity, because it picks the *second* comparison index after
the first (phase 33's iterated-return idea, in its cheapest form).  Both are ready for Theorem A
(order `d`, inert primes) and Theorem B (2×2 traces).
-/

namespace LeanFormalizations.Mills.LucasCoveringAllPrimes

open LeanFormalizations.Mills.ThreeAdic Filter
open LeanFormalizations.Mills.LucasInert LeanFormalizations.Mills.LucasTwoPow
open LeanFormalizations.Mills.LucasUnitAllPrimes
open LeanFormalizations.Mills.FibonacciCoveringAllPrimes

/-! ### The assembly, for an abstract sequence -/

/-- **Steps 3–4 for an abstract sequence.**  If each shift in the finite set `S` eventually has a
good prime factor, and the mechanism promotes a good prime to a whole arithmetic progression, then
one index `m` and one modulus `L` serve every shift in `S`. -/
theorem covering_of_good_seq {c : ℕ} (t : ℕ → ℤ) (S : Finset ℤ)
    (hmech : ∀ (p m : ℕ) (h : ℤ), p.Prime → padicValNat c (glCard 2 p) ≤ m →
      (p : ℤ) ∣ t m + h → ∃ j, 1 ≤ j ∧ ∀ k : ℕ, (p : ℤ) ∣ t (m + k * j) + h)
    (hgood : ∀ h ∈ S, ∀ᶠ n in atTop, ∃ q : ℕ, q.Prime ∧
      (q : ℤ) ∣ t n + h ∧ padicValNat c (glCard 2 q) ≤ n) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h ∈ S,
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ t (L * k + m) + h := by
  classical
  obtain ⟨m, hm⟩ := eventually_atTop.1 ((Filter.eventually_all_finset S).2 hgood)
  have hm0 := hm m le_rfl
  set Q : ℤ → ℕ → Prop := fun h q => q.Prime ∧ (q : ℤ) ∣ t m + h ∧
    padicValNat c (glCard 2 q) ≤ m with hQ
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
    · simp only [dif_neg hh]
      exact le_refl 1
  refine ⟨m, ∏ h ∈ S, Jf h, Finset.one_le_prod' (fun h _ => hJpos h), P, ?_⟩
  intro h hhS
  obtain ⟨hpr, hpd, hpv⟩ := hPspec h hhS
  refine ⟨hpr, fun k => ?_⟩
  obtain ⟨u, hu⟩ : Jf h ∣ ∏ h' ∈ S, Jf h' := Finset.dvd_prod_of_mem Jf hhS
  have hkey := (hJspec h hhS).2 (u * k)
  have hidx : m + u * k * Jf h = (∏ h' ∈ S, Jf h') * k + m := by rw [hu]; ring
  rwa [hidx] at hkey

/-- **Step 5 for an abstract sequence**, assuming only `|t n| → ∞`.

Phase 40's version needed `t` increasing.  Here the two comparison indices are chosen in order:
first `n₁` with `|t n₁| > H`, which bounds every covering prime by `|t n₁| + H`; then `n₂` with
`|t n₂|` beyond that bound, so `|t n₂ + h| > p_h` for *every* shift at once.  A prime `p_h`
dividing a prime value must equal it, which is the contradiction. -/
theorem prime_free_of_covering_seq {t : ℕ → ℤ} {S : Finset ℤ} {H : ℕ}
    (hSb : ∀ h ∈ S, |h| ≤ (H : ℤ))
    (hgrow : Tendsto (fun n => |t n|) atTop atTop)
    {m L : ℕ} (hL : 1 ≤ L) {p : ℤ → ℕ}
    (hp : ∀ h ∈ S, (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ t (L * k + m) + h) :
    ∃ᶠ n in atTop, ∀ h ∈ S, ¬ Prime (t n + h) := by
  rw [frequently_atTop]
  intro a
  -- first index: `|t n₁| > H`
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hgrow.eventually_gt_atTop (H : ℤ))
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = max a N₀ := ⟨_, rfl⟩
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, n₁ = L * K₁ + m := ⟨_, rfl⟩
  have hK₁le : K₁ ≤ n₁ := by
    rw [hn₁]
    have := Nat.le_mul_of_pos_left K₁ hL
    omega
  have hgt₁ : (H : ℤ) < |t n₁| := hN₀ n₁ (by rw [hK₁] at hK₁le; omega)
  -- second index: `|t n₂| > |t n₁| + 2H`
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hgrow.eventually_gt_atTop (|t n₁| + 2 * (H : ℤ)))
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = max (max a N₀) N₁ ⊔ (K₁ + 1) := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n₂, n₂ = L * K₂ + m := ⟨_, rfl⟩
  have hK₂le : K₂ ≤ n₂ := by
    rw [hn₂]
    have := Nat.le_mul_of_pos_left K₂ hL
    omega
  have hgt₂ : |t n₁| + 2 * (H : ℤ) < |t n₂| := hN₁ n₂ (by
    have : N₁ ≤ K₂ := by rw [hK₂]; exact le_trans (le_max_right _ _) le_sup_left
    omega)
  refine ⟨n₂, ?_, ?_⟩
  · have : a ≤ K₂ := by
      rw [hK₂]
      exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) le_sup_left
    omega
  intro h hhS
  obtain ⟨hpr, hpd⟩ := hp h hhS
  have hhb := hSb h hhS
  have habs := abs_le.1 hhb
  -- the covering prime is at most `|t n₁| + H`
  have hne₁ : t n₁ + h ≠ 0 := by
    have h1 : -|t n₁| ≤ t n₁ := neg_abs_le _
    have h2 : t n₁ ≤ |t n₁| := le_abs_self _
    intro hz
    have : |t n₁| ≤ (H : ℤ) := by
      rcases lt_or_ge (t n₁) 0 with hneg | hpos
      · rw [abs_of_neg hneg]; omega
      · rw [abs_of_nonneg hpos]; omega
    omega
  have hple : ((p h : ℤ)) ≤ |t n₁| + (H : ℤ) := by
    have h1 : ((p h : ℤ)) ≤ |t n₁ + h| := by
      refine Int.le_of_dvd (abs_pos.2 hne₁) ((dvd_abs _ _).2 ?_)
      have := hpd K₁
      rwa [← hn₁] at this
    have h2 : |t n₁ + h| ≤ |t n₁| + |h| := abs_add_le _ _
    omega
  intro hprime
  have hdvd₂ : (p h : ℤ) ∣ t n₂ + h := by
    have := hpd K₂
    rwa [← hn₂] at this
  have heq := abs_eq_of_prime_dvd_prime hpr hdvd₂ hprime
  have hlow : |t n₂| - (H : ℤ) ≤ |t n₂ + h| := by
    have h1 : |t n₂| ≤ |t n₂ + h| + |h| := by
      have := abs_add_le (t n₂ + h) (-h)
      simpa using this
    omega
  omega

/-! ### The Lucas instance: the mechanism and the good prime factor -/

/-- The mechanism for `U(c^n)`, strengthened to every multiple of the period (phase 38's
`exists_lucasU_prime_pow_congr` used phase 32's single-step version). -/
theorem exists_lucasU_prime_pow_congr_mul {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1) {c p m : ℕ}
    (hp : p.Prime) (hc : c.Prime) (hv : padicValNat c (glCard 2 p) ≤ m) :
    ∃ j, 1 ≤ j ∧ ∀ k : ℕ,
      (p : ℤ) ∣ lucasU P Q (c ^ (m + k * j)) - lucasU P Q (c ^ m) := by
  have hdet : ¬ (p : ℤ) ∣ (lucasA P Q).det := by
    rw [lucasA_det]; exact not_dvd_of_unit hQ hp
  obtain ⟨j, hj1, hj⟩ :=
    FibonacciCovering.exists_entry_pow_congr_mul (lucasA P Q) hp hc hdet hv
  refine ⟨j, hj1, fun k => ?_⟩
  have hk := hj k 1 0
  rwa [lucasA_pow_apply_one_zero, lucasA_pow_apply_one_zero] at hk

/-- A good prime dividing `U(c^m) + h` divides `U(c^(m + k j)) + h` for every `k`. -/
theorem dvd_lucasU_prime_pow_add_of_good {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1) {c p m : ℕ} {h : ℤ}
    (hp : p.Prime) (hc : c.Prime) (hv : padicValNat c (glCard 2 p) ≤ m)
    (hd : (p : ℤ) ∣ lucasU P Q (c ^ m) + h) :
    ∃ j, 1 ≤ j ∧ ∀ k : ℕ, (p : ℤ) ∣ lucasU P Q (c ^ (m + k * j)) + h := by
  obtain ⟨j, hj1, hj⟩ := exists_lucasU_prime_pow_congr_mul hQ hp hc hv
  refine ⟨j, hj1, fun k => ?_⟩
  have hsum := dvd_add (hj k) hd
  have hrw : lucasU P Q (c ^ (m + k * j)) - lucasU P Q (c ^ m)
      + (lucasU P Q (c ^ m) + h) = lucasU P Q (c ^ (m + k * j)) + h := by ring
  rwa [hrw] at hsum

/-! ### The Lucas certificate and the good prime factor -/

lemma pmOneMod_neg {M x : ℤ} (hx : PmOneMod M x) : PmOneMod M (-x) := by
  rcases hx with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact Or.inr ⟨-a, by linarith [ha]⟩
  · exact Or.inl ⟨-a, by linarith [ha]⟩

/-- **Step 2 for `U(c^n)`**, at every odd prime `c ∤ D`.  Same shape as the Fibonacci case: if every
prime factor of `U(c^n) + h` had a large `c`-part then `U(c^n) ≡ x (mod c^(n/2))` with `x = s − h`,
`s = ±1`; the `c`-adic convergence `c^n ∣ U(c^(n+d)) − U(c^n)` plus the exact composition
`U(c^d · N) = Φ_J(U(N))` turn that into `c^(n/2) ∣ Φ_J(x) − x`, which `lucasOddPoly_far` forbids
(`x ≠ 0` because `c ∤ U(c^n)`). -/
theorem exists_good_lucasU_prime_factor {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1)
    (hD5 : 5 ≤ P ^ 2 - 4 * Q) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (h : ℤ) :
    ∀ᶠ n in atTop, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ lucasU P Q (c ^ n) + h ∧
      padicValNat c (glCard 2 p) ≤ n := by
  have hcodd : Odd c := hc.odd_of_ne_two hc2
  have hc3 : 3 ≤ c := by
    have := hc.two_le
    rcases Nat.lt_or_ge c 3 with hx | hx
    · interval_cases c <;> simp_all
    · exact hx
  -- the `c`-adic convergence of `U(c^n)`
  have hdet : ¬ (c : ℤ) ∣ (lucasA P Q).det := by
    rw [lucasA_det]; exact not_dvd_of_unit hQ hc
  obtain ⟨d, s, hd1, hsle, hconvm⟩ := exists_shift_pow_congr (lucasA P Q) hc hdet
  have hs1 : s ≤ 1 := by rwa [padicValNat_glCard_two_self hc] at hsle
  have hconv : ∀ n : ℕ, 1 ≤ n →
      (c : ℤ) ^ n ∣ lucasU P Q (c ^ (n + d)) - lucasU P Q (c ^ n) := by
    intro n hn
    have hk := hconvm n (by omega) 1 0
    rw [lucasA_pow_apply_one_zero, lucasA_pow_apply_one_zero] at hk
    exact dvd_trans (pow_dvd_pow _ (by omega)) hk
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
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
      |lucasOddPoly (P ^ 2 - 4 * Q) Q (σ - h) J - (σ - h)| ≤ (B : ℤ) := by
    refine ⟨(max |lucasOddPoly (P ^ 2 - 4 * Q) Q (1 - h) J - (1 - h)|
      |lucasOddPoly (P ^ 2 - 4 * Q) Q (-1 - h) J - (-1 - h)|).toNat, fun σ hσ => ?_⟩
    have hnn : (0 : ℤ) ≤ max |lucasOddPoly (P ^ 2 - 4 * Q) Q (1 - h) J - (1 - h)|
        |lucasOddPoly (P ^ 2 - 4 * Q) Q (-1 - h) J - (-1 - h)| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    rw [Int.toNat_of_nonneg hnn]
    rcases hσ with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hgrow.eventually_gt_atTop (|h| + 1))
  refine eventually_atTop.2 ⟨max (max 1 N₀) (2 * B + 8), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnB : 2 * B + 8 ≤ n := le_trans (le_max_right _ _) hn
  have hbig : |h| + 1 < |lucasU P Q (c ^ n)| := hN₀ n hnN₀
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
  have hfac : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ lucasU P Q (c ^ n) + h →
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
  -- `U(c^n) + h ≠ 0`, so it has a factorisation into primes (up to sign)
  have hne : lucasU P Q (c ^ n) + h ≠ 0 := by
    have h1 : -|lucasU P Q (c ^ n)| ≤ lucasU P Q (c ^ n) := neg_abs_le _
    have h2 : lucasU P Q (c ^ n) ≤ |lucasU P Q (c ^ n)| := le_abs_self _
    have h3 : -|h| ≤ h := neg_abs_le h
    have h4 : h ≤ |h| := le_abs_self h
    intro hz
    have : |lucasU P Q (c ^ n)| ≤ |h| := by
      rcases lt_or_ge (lucasU P Q (c ^ n)) 0 with hneg | hpos
      · rw [abs_of_neg hneg]; omega
      · rw [abs_of_nonneg hpos]; omega
    omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = |lucasU P Q (c ^ n) + h| :=
    ⟨(lucasU P Q (c ^ n) + h).natAbs, (Int.abs_eq_natAbs _).symm⟩
  have hM1 : 1 ≤ M := by
    have : (0 : ℤ) < (M : ℤ) := by rw [hM]; exact abs_pos.2 hne
    exact_mod_cast this
  have hpmM : PmOneMod ((c : ℤ) ^ e) (M : ℤ) :=
    PmOneMod.of_prime_factors _ M hM1 (by
      intro q hq hqd
      refine hfac q hq ?_
      have hdM : (q : ℤ) ∣ (M : ℤ) := by exact_mod_cast Int.natCast_dvd_natCast.2 hqd
      rw [hM] at hdM
      exact (dvd_abs _ _).1 hdM)
  have hpm : PmOneMod ((c : ℤ) ^ e) (lucasU P Q (c ^ n) + h) := by
    rcases abs_choice (lucasU P Q (c ^ n) + h) with hch | hch
    · rw [← hch, ← hM]; exact hpmM
    · have : (M : ℤ) = -(lucasU P Q (c ^ n) + h) := by rw [hM, hch]
      have h2 := pmOneMod_neg hpmM
      rw [this] at h2
      simpa using h2
  obtain ⟨σ, hσ, hσd⟩ := hpm.exists_sign
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = σ - h := ⟨_, rfl⟩
  have hxd : (c : ℤ) ^ e ∣ lucasU P Q (c ^ n) - x := by
    have hrw : lucasU P Q (c ^ n) - x = (lucasU P Q (c ^ n) + h) - σ := by rw [hx]; ring
    rw [hrw]; exact hσd
  have hx0 : x ≠ 0 := by
    intro hxz
    rw [hxz, sub_zero] at hxd
    exact not_dvd_lucasU_prime_pow hQ hc hc2 hD n
      (dvd_trans (dvd_pow_self (c : ℤ) (by omega : e ≠ 0)) hxd)
  have hcomp : lucasU P Q (c ^ (n + d))
      = lucasOddPoly (P ^ 2 - 4 * Q) Q (lucasU P Q (c ^ n)) J := by
    have hodd : Odd (c ^ n) := hcodd.pow
    have hidx : (2 * J + 1) * c ^ n = c ^ (n + d) := by rw [hJ, pow_add]; ring
    rw [← hidx]
    exact lucasU_odd_mul hQ J hodd
  have hΦ : (c : ℤ) ^ e ∣ lucasOddPoly (P ^ 2 - 4 * Q) Q (lucasU P Q (c ^ n)) J
      - lucasOddPoly (P ^ 2 - 4 * Q) Q x J := dvd_lucasOddPoly_sub hxd J
  have hshift : (c : ℤ) ^ e ∣ lucasU P Q (c ^ (n + d)) - lucasU P Q (c ^ n) :=
    dvd_trans (pow_dvd_pow _ hen) (hconv n hn1)
  have hfinal : (c : ℤ) ^ e ∣ lucasOddPoly (P ^ 2 - 4 * Q) Q x J - x := by
    have hsum : lucasOddPoly (P ^ 2 - 4 * Q) Q x J - x
        = -(lucasOddPoly (P ^ 2 - 4 * Q) Q (lucasU P Q (c ^ n)) J
            - lucasOddPoly (P ^ 2 - 4 * Q) Q x J)
          + (lucasU P Q (c ^ (n + d)) - lucasU P Q (c ^ n))
          + (lucasU P Q (c ^ n) - x) := by rw [hcomp]; ring
    rw [hsum]
    exact dvd_add (dvd_add (dvd_neg.2 hΦ) hshift) hxd
  have hfar := (lucasOddPoly_far hQ hD5 hx0 hJ1).1
  have hle := Int.le_of_dvd (abs_pos.2 hfar) ((dvd_abs _ _).2 hfinal)
  have hbd : |lucasOddPoly (P ^ 2 - 4 * Q) Q x J - x| ≤ (B : ℤ) := by rw [hx]; exact hB σ hσ
  omega

/-! ### Theorem C for Lucas sequences -/

/-- **(D1) for `U(P, ±1)` along the tower `c^n`**, at every odd prime `c ∤ D`. -/
theorem lucasU_prime_pow_covering {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1)
    (hD5 : 5 ≤ P ^ 2 - 4 * Q) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (H : ℕ) :
    ∃ m L : ℕ, 1 ≤ L ∧ ∃ p : ℤ → ℕ, ∀ h : ℤ, |h| ≤ H →
      (p h).Prime ∧ ∀ k : ℕ, (p h : ℤ) ∣ lucasU P Q (c ^ (L * k + m)) + h := by
  obtain ⟨m, L, hL, p, hp⟩ :=
    covering_of_good_seq (c := c) (fun n => lucasU P Q (c ^ n)) (Finset.Icc (-(H : ℤ)) (H : ℤ))
      (fun q m' h' hq hv hd => dvd_lucasU_prime_pow_add_of_good hQ hq hc hv hd)
      (fun h' _ => exists_good_lucasU_prime_factor hQ hD5 hc hc2 hD hgrow h')
  refine ⟨m, L, hL, p, fun h hh => hp h ?_⟩
  rw [Finset.mem_Icc]
  have := abs_le.1 hh
  exact ⟨this.1, this.2⟩

/-- **Prime-free intervals of any fixed length around `U(c^n)`, infinitely often**, at every odd
prime `c ∤ D` — Saito's (D2) for a NON-reversible tower, for every Lucas sequence with unit
`Q = ±1` and `D = P² − 4Q ≥ 5`. -/
theorem lucasU_prime_pow_prime_free {P Q : ℤ} (hQ : Q = 1 ∨ Q = -1)
    (hD5 : 5 ≤ P ^ 2 - 4 * Q) {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
    (hD : ¬ (c : ℤ) ∣ P ^ 2 - 4 * Q)
    (hgrow : Tendsto (fun n : ℕ => |lucasU P Q (c ^ n)|) atTop atTop) (H : ℕ) :
    ∃ᶠ n in atTop, ∀ h : ℤ, |h| ≤ H → ¬ Prime (lucasU P Q (c ^ n) + h) := by
  obtain ⟨m, L, hL, p, hp⟩ := covering_of_good_seq (c := c) (fun n => lucasU P Q (c ^ n))
    (Finset.Icc (-(H : ℤ)) (H : ℤ))
    (fun q m' h' hq hv hd => dvd_lucasU_prime_pow_add_of_good hQ hq hc hv hd)
    (fun h' _ => exists_good_lucasU_prime_factor hQ hD5 hc hc2 hD hgrow h')
  have hmem : ∀ h : ℤ, |h| ≤ (H : ℤ) → h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    intro h hh
    rw [Finset.mem_Icc]
    have := abs_le.1 hh
    exact ⟨this.1, this.2⟩
  have hbnd : ∀ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), |h| ≤ (H : ℤ) := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    exact abs_le.2 ⟨hh.1, hh.2⟩
  refine (prime_free_of_covering_seq (H := H) hbnd hgrow hL hp).mono ?_
  exact fun n hn h hh => hn h (hmem h hh)

end LeanFormalizations.Mills.LucasCoveringAllPrimes

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Principal units at a height-one prime, and the `p`-adic exponent lemma

Infrastructure for `NumberTheory/Leopoldt/RankOne.lean`.  The phase-26 handoff expected this to
need a `ℤ_p`-action on the principal units `U⁽¹⁾` built by continuity, plus torsion-freeness.
**Neither is needed.**  The whole of Leopoldt in unit rank `≤ 1` follows from one elementary
valuation identity:

> if `W (θ - 1) < 1` and `t : ℤ` is prime to the residue characteristic, then
> `W (θ ^ t - 1) = W (θ - 1)`.

(`valuation_zpow_sub_one`.)  So on a principal unit, raising to an exponent *prime to `p`* does not
move the valuation at all, and only the `p`-part of the exponent can push `θ ^ m` towards `1`.
Since `a ≠ 0` in `ℤ_p` bounds the `p`-part of `m n` from above (`exists_pow_split`), the valuations
`W (ε ^ (N * m n) - 1)` stay bounded away from `0`, contradicting `→ 1`.
-/
import LeanFormalizations.Literature.Leopoldt

namespace LeanFormalizations.Leopoldt

open NumberField IsDedekindDomain Filter Topology

/-! ### Splitting an integer along a bounded power of `p` -/

/-- If `p ^ k ∤ m`, then `m = p ^ j * t` with `j < k` and `p ∤ t`. -/
theorem exists_pow_split (p : ℕ) (hp : 1 < p) :
    ∀ (k : ℕ) (m : ℤ), ¬ ((p : ℤ) ^ k ∣ m) → ∃ j t : _, j < k ∧ m = (p : ℤ) ^ j * t ∧ ¬ ((p : ℤ) ∣ t)
  | 0, m, h => absurd (by simpa using (one_dvd m)) h
  | k + 1, m, h => by
    by_cases hk : ((p : ℤ) ^ k ∣ m)
    · obtain ⟨t, ht⟩ := hk
      refine ⟨k, t, Nat.lt_succ_self k, ht, fun hdvd ↦ h ?_⟩
      obtain ⟨s, hs⟩ := hdvd
      exact ⟨s, by rw [ht, hs]; ring⟩
    · obtain ⟨j, t, hj, ht, hpt⟩ := exists_pow_split p hp k m hk
      exact ⟨j, t, hj.trans (Nat.lt_succ_self k), ht, hpt⟩

/-! ### The valuation of `θ ^ t - 1` on a principal unit -/

section Valuation

variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "W" => v.valuation K

/-- A principal unit has valuation `1`. -/
theorem valuation_eq_one_of_principal {θ : K} (hθ : W (θ - 1) < 1) : W θ = 1 := by
  have h : θ = 1 + (θ - 1) := by ring
  rw [h, Valuation.map_one_add_of_lt _ hθ]

/-- On a principal unit, every natural power is again principal, with no larger distance to `1`. -/
theorem valuation_pow_sub_one_le {θ : K} (hθ : W (θ - 1) < 1) (j : ℕ) :
    W (θ ^ j - 1) ≤ W (θ - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hrw : θ ^ (j + 1) - 1 = θ * (θ ^ j - 1) + (θ - 1) := by ring
      rw [hrw]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ le_rfl)
      rw [map_mul, valuation_eq_one_of_principal v hθ, one_mul]
      exact ih

/-- The key identity: raising a principal unit to an exponent prime to the residue characteristic
does not change the valuation of `θ - 1`. -/
theorem valuation_pow_sub_one {θ : K} (hθ : W (θ - 1) < 1) {j : ℕ}
    (hj : W ((j : ℕ) : K) = 1) : W (θ ^ j - 1) = W (θ - 1) := by
  have hgeom : θ ^ j - 1 = (∑ i ∈ Finset.range j, θ ^ i) * (θ - 1) := by
    rw [geom_sum_mul]
  have hsum : W ((∑ i ∈ Finset.range j, θ ^ i) - (j : ℕ)) < 1 := by
    have hrw : (∑ i ∈ Finset.range j, θ ^ i) - ((j : ℕ) : K)
        = ∑ i ∈ Finset.range j, (θ ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hrw]
    refine lt_of_le_of_lt (Valuation.map_sum_le _ ?_) hθ
    intro i _
    exact valuation_pow_sub_one_le v hθ i
  have hS : W (∑ i ∈ Finset.range j, θ ^ i) = 1 := by
    have h : (∑ i ∈ Finset.range j, θ ^ i)
        = ((j : ℕ) : K) + ((∑ i ∈ Finset.range j, θ ^ i) - ((j : ℕ) : K)) := by ring
    rw [h, Valuation.map_add_eq_of_lt_left _ (by rw [hj]; exact hsum), hj]
  rw [hgeom, map_mul, hS, one_mul]

/-- The `ℤ`-power version. -/
theorem valuation_zpow_sub_one {θ : K} (hθ : W (θ - 1) < 1) {t : ℤ}
    (ht : W ((t : ℤ) : K) = 1) : W (θ ^ t - 1) = W (θ - 1) := by
  have h1 : W θ = 1 := valuation_eq_one_of_principal v hθ
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at h1
  rcases le_or_gt 0 t with h | h
  · lift t to ℕ using h with n
    simpa using valuation_pow_sub_one v hθ (j := n) (by simpa using ht)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = -(n : ℤ) := ⟨(-t).toNat, by omega⟩
    subst hn
    have h2 : θ ^ (-(n : ℤ)) * θ ^ (n : ℕ) = 1 := by
      rw [← zpow_natCast θ n, ← zpow_add₀ hθ0]
      simp
    have hpow : θ ^ (-(n : ℤ)) - 1 = -(θ ^ (-(n : ℤ))) * (θ ^ (n : ℕ) - 1) := by
      linear_combination h2
    have hv : W (θ ^ (-(n : ℤ))) = 1 := by
      rw [zpow_neg, map_inv₀, zpow_natCast, map_pow, valuation_eq_one_of_principal v hθ]
      simp
    rw [hpow, map_mul, Valuation.map_neg, hv, one_mul]
    exact valuation_pow_sub_one v hθ (j := n) (by simpa using ht)

/-! ### Integers prime to the residue characteristic are `v`-units -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- An integer prime to `p` has `v`-valuation `1`, at any `v` above `p`. -/
theorem valuation_intCast_eq_one (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) {t : ℤ}
    (ht : ¬ ((p : ℤ) ∣ t)) : W ((t : ℤ) : K) = 1 := by
  have hcast : ((t : ℤ) : K) = algebraMap (𝓞 K) K ((t : ℤ) : 𝓞 K) :=
    (map_intCast (algebraMap (𝓞 K) K) t).symm
  rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hmem
  have hcop : IsCoprime ((p : ℕ) : ℤ) t := by
    refine (Prime.coprime_iff_not_dvd ?_).mpr ht
    exact Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨a, b, hab⟩ := hcop
  have : (1 : 𝓞 K) ∈ v.asIdeal := by
    have := congrArg (fun z : ℤ ↦ ((z : ℤ) : 𝓞 K)) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hmem)
  exact absurd (Ideal.eq_top_of_isUnit_mem _ this isUnit_one) v.isPrime.ne_top

/-! ### A unit becomes principal after raising to an exponent prime to `p` -/

/-- In a finite domain of characteristic `p` there is an exponent `N ≥ 1` prime to `p` killing
every unit.  Take `N = card Rˣ`: if `p ∣ N`, Cauchy gives a unit `u` of order `p`, and then
`(u - 1) ^ p = u ^ p - 1 = 0`, so `u = 1` — a contradiction. -/
theorem exists_exponent_of_finite_domain (R : Type*) [CommRing R] [IsDomain R] [Fintype R]
    (p : ℕ) [hp : Fact p.Prime] (hchar : (p : R) = 0) :
    ∃ N : ℕ, 0 < N ∧ ¬ (p ∣ N) ∧ ∀ x : R, IsUnit x → x ^ N = 1 := by
  haveI : CharP R p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hchar
  haveI : Fintype Rˣ := Fintype.ofFinite _
  refine ⟨Fintype.card Rˣ, Fintype.card_pos, ?_, ?_⟩
  · intro hdvd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := Rˣ) p hdvd
    have hup : ((u : R)) ^ p = 1 := by
      have h : u ^ p = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
      calc ((u : R)) ^ p = ((u ^ p : Rˣ) : R) := by rw [Units.val_pow_eq_pow_val]
        _ = 1 := by rw [h, Units.val_one]
    have h1 : ((u : R) - 1) ^ p = 0 := by
      rw [sub_pow_char, hup, one_pow, sub_self]
    have h2 : (u : R) - 1 = 0 := by
      simpa using pow_eq_zero_iff (n := p) hp.out.pos.ne' |>.mp h1
    have hu1 : u = 1 := Units.ext (by
      have : (u : R) = 1 := by linear_combination h2
      simpa using this)
    rw [hu1, orderOf_one] at hu
    exact hp.out.ne_one hu.symm
  · rintro x ⟨u, rfl⟩
    rw [← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one]

/-- There is an exponent `N` prime to `p` (and `≥ 1`) making any unit of `𝓞 K` principal at `v`. -/
theorem exists_principal_exponent (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) (ε : (𝓞 K)ˣ) :
    ∃ N : ℕ, 0 < N ∧ ¬ (p ∣ N) ∧ W (((ε : 𝓞 K) : K) ^ N - 1) < 1 := by
  haveI : (v.asIdeal).IsPrime := v.isPrime
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  haveI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hchar : ((p : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := by
    have h : ((p : ℕ) : 𝓞 K ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal ((p : ℕ) : 𝓞 K) :=
      (map_natCast (Ideal.Quotient.mk v.asIdeal) p).symm
    rw [h, Ideal.Quotient.eq_zero_iff_mem]
    exact hv
  obtain ⟨N, hN, hpN, hkill⟩ := exists_exponent_of_finite_domain (𝓞 K ⧸ v.asIdeal) p hchar
  refine ⟨N, hN, hpN, ?_⟩
  have hmem : (ε : 𝓞 K) ^ N - 1 ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one,
      hkill _ ((Ideal.Quotient.mk v.asIdeal).isUnit_map ε.isUnit), sub_self]
  have h := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)
    (v := v) ((ε : 𝓞 K) ^ N - 1)).mpr hmem
  simpa using h

/-! ### Exact behaviour of the principal filtration under `θ ↦ θ ^ p`

Phase 28 groundwork (towards `padicLog`, hence Brumer, hence rank `≥ 2`).  `valuation_pow_sub_one_le`
only says the level does not decrease.  The *exact* statement is
`ν (θ^p − 1) = min (ν p + ν x, p · ν x)` with `x = θ − 1`, which is what makes `U⁽¹⁾` pro-`p` with
no `p`-torsion and makes the `padicLog` series converge.  Multiplicatively:

`W (θ^p − 1) = max (W p · W x) (W x ^ p)` whenever those two differ,

and the tie `W p = W x ^ (p−1)` is exactly the exceptional case — `θ = −1` in `ℚ₂` is the tie, and
it is a genuine `p`-torsion element of `U⁽¹⁾`.  So the no-`p`-torsion statement really does need the
hypothesis, and it holds automatically for `p` odd at an unramified `v` (`ν p = 1`, `ν x ≥ 1`,
`1 = (p−1) ν x` impossible).
-/

/-- An integer has `v`-valuation at most `1`. -/
theorem valuation_natCast_le_one (n : ℕ) : W ((n : ℕ) : K) ≤ 1 := by
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) v ((n : ℕ) : 𝓞 K)
  simpa using h

/-- The binomial decomposition of `θ ^ p − 1` for a prime `p`, isolating the two extreme terms
`p · x` and `x ^ p`; everything between them has valuation `≤ W p · W x ^ 2`. -/
theorem valuation_pow_char_sub_one {θ : K} (hθ : W (θ - 1) < 1)
    (hne : W ((p : ℕ) : K) ≠ W (θ - 1) ^ (p - 1)) :
    W (θ ^ p - 1) = max (W ((p : ℕ) : K) * W (θ - 1)) (W (θ - 1) ^ p) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  set x : K := θ - 1 with hxdef
  have hθx : θ = x + 1 := by rw [hxdef]; ring
  rcases eq_or_ne x 0 with hx0 | hx0
  · have hθ1 : θ = 1 := sub_eq_zero.mp (hxdef.symm.trans hx0)
    have hL : W (θ ^ p - 1) = 0 := by rw [hθ1]; simp
    rw [hL, hx0]
    simp [zero_pow hp.out.pos.ne']
  set B : K := ∑ k ∈ Finset.range q, ((Nat.choose p (k + 2) : ℕ) : K) * x ^ (k + 2) with hB
  have hdecomp : θ ^ p - 1 = ((p : ℕ) : K) * x + B + x ^ p := by
    rw [hθx, add_pow]
    simp only [one_pow, mul_one]
    rw [hq, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [hB, hq]
    push_cast
    ring_nf
    simp only [Nat.choose_one_right, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one,
      Nat.cast_add, Nat.cast_ofNat]
    ring
  -- the middle block is small
  have hBle : W B ≤ W ((p : ℕ) : K) * W x ^ 2 := by
    rw [hB]
    refine Valuation.map_sum_le _ fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (by omega) (by omega : k + 2 < p)
    rw [map_mul, map_pow]
    have h1 : W ((Nat.choose p (k + 2) : ℕ) : K) ≤ W ((p : ℕ) : K) := by
      rw [hc]
      push_cast
      rw [map_mul]
      exact mul_le_of_le_one_right' (valuation_natCast_le_one v c)
    have h2 : W x ^ (k + 2) ≤ W x ^ 2 := by
      rw [pow_add, mul_comm]
      exact mul_le_of_le_one_right' (pow_le_one' (le_of_lt hθ) k)
    exact mul_le_mul' h1 h2
  -- so `p * x + B` has the valuation of `p * x`
  have hWp : W ((p : ℕ) : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hWx : W x ≠ 0 := by rwa [Valuation.ne_zero_iff]
  have hBlt : W B < W (((p : ℕ) : K) * x) := by
    rw [map_mul]
    refine lt_of_le_of_lt hBle ?_
    rw [pow_two, ← mul_assoc]
    exact mul_lt_of_lt_one_right (zero_lt_iff.mpr (mul_ne_zero hWp hWx)) hθ
  have hAB : W (((p : ℕ) : K) * x + B) = W ((p : ℕ) : K) * W x := by
    rw [Valuation.map_add_eq_of_lt_left _ hBlt, map_mul]
  -- and the two extremes differ, so the sum's valuation is their max
  have hdiff : W (((p : ℕ) : K) * x + B) ≠ W (x ^ p) := by
    rw [hAB, map_pow]
    intro h
    apply hne
    have hpow : W x ^ p = W x ^ (p - 1) * W x := by
      rw [← pow_succ]
      congr 1
      have := hp.out.pos
      omega
    rw [hpow] at h
    exact mul_right_cancel₀ hWx h
  rw [hdecomp, Valuation.map_add_of_distinct_val _ hdiff, hAB, map_pow]

/-- **No `p`-torsion in the principal units**, away from the exceptional tie
`W p = W (θ − 1) ^ (p − 1)`.  (The tie is real: `θ = −1` at `p = 2` over `ℚ₂`.) -/
theorem pow_char_ne_one_of_principal {θ : K} (hθ : W (θ - 1) < 1) (hθ1 : θ ≠ 1)
    (hne : W ((p : ℕ) : K) ≠ W (θ - 1) ^ (p - 1)) : θ ^ p ≠ 1 := by
  intro hcon
  have hW : W (θ ^ p - 1) = 0 := by rw [hcon, sub_self, map_zero]
  rw [valuation_pow_char_sub_one v hθ hne] at hW
  have hWp : W ((p : ℕ) : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hWx : W (θ - 1) ≠ 0 := by
    rw [Valuation.ne_zero_iff, sub_ne_zero]
    exact hθ1
  rw [max_eq_iff] at hW
  rcases hW with ⟨h, -⟩ | ⟨h, -⟩
  · exact mul_ne_zero hWp hWx h
  · exact pow_ne_zero _ hWx h

/-! ### The deep regime: exact growth, and genuine torsion-freeness

The tie `W p = W x ^ (p−1)` (additively `e = (p−1) ν x`) can recur along the tower in ramified
cases, so `pow_char_ne_one_of_principal` does not iterate unconditionally.  But **above** the tie —
`ν x > e/(p−1)`, multiplicatively `W x ^ (p−1) < W p`, which is exactly the classical
`log`/`exp` convergence range — the deep condition is self-propagating, the `x^p` term is
永 dominated by the `p·x` term, and the growth is exact for every `j`:

`W (θ ^ (p^j) − 1) = W p ^ j · W (θ − 1)`.

Two consequences: `U^(m)` for `m > e/(p−1)` is **torsion-free** (`pow_pow_char_ne_one_of_deep`),
and `θ ^ (p^j) → 1` at a *known* rate, which is the quantitative input `padicLog` and the
`ℤ_p`-module structure need.
-/

/-- The deep condition `W (θ − 1) ^ (p − 1) < W p` propagates along `θ ↦ θ ^ p`, and the growth is
exact: `W (θ ^ (p^j) − 1) = W p ^ j · W (θ − 1)`. -/
theorem valuation_pow_pow_char_sub_one {θ : K} (hθ : W (θ - 1) < 1)
    (hdeep : W (θ - 1) ^ (p - 1) < W ((p : ℕ) : K)) (j : ℕ) :
    W (θ ^ (p ^ j) - 1) = W ((p : ℕ) : K) ^ j * W (θ - 1) := by
  have hWp : W ((p : ℕ) : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hWple : W ((p : ℕ) : K) ≤ 1 := valuation_natCast_le_one v p
  rcases eq_or_ne (θ - 1) 0 with hx0 | hx0
  · have hθ1 : θ = 1 := sub_eq_zero.mp hx0
    rw [hθ1]
    simp
  have hWx : W (θ - 1) ≠ 0 := by rwa [Valuation.ne_zero_iff]
  induction j with
  | zero => simp
  | succ j ih =>
      -- `ψ := θ ^ (p ^ j)` is principal, still deep, and one more `p`-th power applies the formula
      have hψ : W (θ ^ (p ^ j) - 1) < 1 := by
        rw [ih]
        calc W ((p : ℕ) : K) ^ j * W (θ - 1) ≤ 1 * W (θ - 1) :=
              mul_le_mul_right' (pow_le_one' hWple j) _
          _ = W (θ - 1) := one_mul _
          _ < 1 := hθ
      have hψ0 : W (θ ^ (p ^ j) - 1) ≠ 0 := by
        rw [ih]
        exact mul_ne_zero (pow_ne_zero _ hWp) hWx
      have hψdeep : W (θ ^ (p ^ j) - 1) ^ (p - 1) < W ((p : ℕ) : K) := by
        rw [ih, mul_pow]
        calc (W ((p : ℕ) : K) ^ j) ^ (p - 1) * W (θ - 1) ^ (p - 1)
              < (W ((p : ℕ) : K) ^ j) ^ (p - 1) * W ((p : ℕ) : K) :=
              mul_lt_mul_of_pos_left hdeep
                (zero_lt_iff.mpr (pow_ne_zero _ (pow_ne_zero _ hWp)))
          _ ≤ 1 * W ((p : ℕ) : K) :=
              mul_le_mul_right' (pow_le_one' (pow_le_one' hWple j) _) _
          _ = W ((p : ℕ) : K) := one_mul _
      have hkey := valuation_pow_char_sub_one v hψ (ne_of_gt hψdeep)
      have hsmall : W (θ ^ (p ^ j) - 1) ^ p
          < W ((p : ℕ) : K) * W (θ ^ (p ^ j) - 1) := by
        have hpow : W (θ ^ (p ^ j) - 1) ^ p
            = W (θ ^ (p ^ j) - 1) ^ (p - 1) * W (θ ^ (p ^ j) - 1) := by
          rw [← pow_succ]
          congr 1
          have := hp.out.pos
          omega
        rw [hpow]
        exact mul_lt_mul_of_pos_right hψdeep (zero_lt_iff.mpr hψ0)
      rw [pow_succ, pow_mul, hkey, max_eq_left (le_of_lt hsmall), ih]
      simp [pow_succ, mul_comm, mul_left_comm]

/-- **Torsion-freeness of the deep principal units.**  Above the tie there is no `p`-power
torsion at all: the valuations `W p ^ j · W (θ − 1)` are never `0`. -/
theorem pow_pow_char_ne_one_of_deep {θ : K} (hθ : W (θ - 1) < 1) (hθ1 : θ ≠ 1)
    (hdeep : W (θ - 1) ^ (p - 1) < W ((p : ℕ) : K)) (j : ℕ) : θ ^ (p ^ j) ≠ 1 := by
  intro hcon
  have hWp : W ((p : ℕ) : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hWx : W (θ - 1) ≠ 0 := by
    rw [Valuation.ne_zero_iff, sub_ne_zero]
    exact hθ1
  have h := valuation_pow_pow_char_sub_one v hθ hdeep j
  rw [hcon, sub_self, map_zero] at h
  exact mul_ne_zero (pow_ne_zero _ hWp) hWx h.symm

/-! ### The `ℤ_p`-action: the uniform-continuity estimate

Step (3) of the phase-28 route.  On a deep `θ`, congruent exponents give close powers **at a known
rate**: `p^j ∣ k − k'` implies `W (θ^k − θ^{k'}) ≤ W p ^ j · W (θ − 1)`.  So `k ↦ θ^k` is uniformly
continuous from the `p`-adic topology on `ℤ` to `K_v`, hence extends to `ℤ_p → U⁽¹⁾` by
completeness, and the extension is injective by `pow_pow_char_ne_one_of_deep`.  That is the
`ℤ_p`-module structure on the deep principal units; `padicLog` and Brumer follow.

Everything here is in `K` and needs no completeness — the extension itself is the next leaf.
-/

/-- The `ℤ`-power version of `valuation_pow_sub_one_le`. -/
theorem valuation_zpow_sub_one_le {θ : K} (hθ : W (θ - 1) < 1) (t : ℤ) :
    W (θ ^ t - 1) ≤ W (θ - 1) := by
  have h1 : W θ = 1 := valuation_eq_one_of_principal v hθ
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at h1
  rcases le_or_gt 0 t with h | h
  · lift t to ℕ using h with n
    simpa using valuation_pow_sub_one_le v hθ n
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = -(n : ℤ) := ⟨(-t).toNat, by omega⟩
    subst hn
    have h2 : θ ^ (-(n : ℤ)) * θ ^ (n : ℕ) = 1 := by
      rw [← zpow_natCast θ n, ← zpow_add₀ hθ0]
      simp
    have hpow : θ ^ (-(n : ℤ)) - 1 = -(θ ^ (-(n : ℤ))) * (θ ^ (n : ℕ) - 1) := by
      linear_combination h2
    have hv1 : W (θ ^ (-(n : ℤ))) = 1 := by
      rw [zpow_neg, map_inv₀, zpow_natCast, map_pow, h1]
      simp
    rw [hpow, map_mul, Valuation.map_neg, hv1, one_mul]
    exact valuation_pow_sub_one_le v hθ n

/-- On a deep principal unit, an exponent divisible by `p ^ j` pushes the valuation down by at
least the exact factor `W p ^ j`. -/
theorem valuation_zpow_sub_one_le_of_dvd {θ : K} (hθ : W (θ - 1) < 1)
    (hdeep : W (θ - 1) ^ (p - 1) < W ((p : ℕ) : K)) (j : ℕ) {m : ℤ} (hm : ((p : ℕ) : ℤ) ^ j ∣ m) :
    W (θ ^ m - 1) ≤ W ((p : ℕ) : K) ^ j * W (θ - 1) := by
  obtain ⟨t, ht⟩ := hm
  have hWple : W ((p : ℕ) : K) ≤ 1 := valuation_natCast_le_one v p
  have hψ : W (θ ^ (p ^ j) - 1) = W ((p : ℕ) : K) ^ j * W (θ - 1) :=
    valuation_pow_pow_char_sub_one v hθ hdeep j
  have hψlt : W (θ ^ (p ^ j) - 1) < 1 := by
    rw [hψ]
    calc W ((p : ℕ) : K) ^ j * W (θ - 1) ≤ 1 * W (θ - 1) :=
          mul_le_mul_right' (pow_le_one' hWple j) _
      _ = W (θ - 1) := one_mul _
      _ < 1 := hθ
  have hrw : θ ^ m = (θ ^ (p ^ j)) ^ t := by
    rw [ht, ← zpow_natCast θ (p ^ j), ← zpow_mul]
    congr 1
  rw [hrw, ← hψ]
  exact valuation_zpow_sub_one_le v hψlt t

/-- **The Cauchy estimate.**  Congruent exponents give close powers, at the known rate `W p ^ j`.
This is exactly the uniform continuity of `k ↦ θ ^ k` for the `p`-adic topology on `ℤ`. -/
theorem valuation_zpow_sub_zpow_le {θ : K} (hθ : W (θ - 1) < 1)
    (hdeep : W (θ - 1) ^ (p - 1) < W ((p : ℕ) : K)) (j : ℕ) {k l : ℤ}
    (hkl : ((p : ℕ) : ℤ) ^ j ∣ (k - l)) :
    W (θ ^ k - θ ^ l) ≤ W ((p : ℕ) : K) ^ j * W (θ - 1) := by
  have h1 : W θ = 1 := valuation_eq_one_of_principal v hθ
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at h1
  have hfac : θ ^ k - θ ^ l = θ ^ l * (θ ^ (k - l) - 1) := by
    rw [mul_sub, mul_one, ← zpow_add₀ hθ0]
    congr 2
    ring
  have hWl : W (θ ^ l) = 1 := by rw [map_zpow₀, h1, one_zpow]
  rw [hfac, map_mul, hWl, one_mul]
  exact valuation_zpow_sub_one_le_of_dvd v hθ hdeep j hkl

/-! ### Beyond rank one: the ultrametric leading term of a product of principal units

This is the tool that reaches past rank `1`, and it makes the shape of the rank-`≥ 2` wall exact.
For principal units `1 + xᵢ`, if one `xᵢ₀` is *strictly closest to `0`'s complement* — i.e. `W xᵢ₀`
strictly the largest, additively `ν xᵢ₀` strictly the smallest — then

`W (∏ (1 + xᵢ) − 1) = W xᵢ₀`

**exactly**: the cross terms `xᵢxⱼ` are strictly smaller, so the leading term survives.  Combined
with the exact growth of step 2, this proves Leopoldt for `r ≥ 2` **whenever the levels
`ν(εᵢ^N − 1) + v_p(aᵢ)·e` have a unique minimum**.  What is left is precisely the *tie* case, where
two or more leading terms sit at the same level and can cancel in the residue field — and that
cancellation problem is exactly Baker/Brumer.  So the wall is a residue-field cancellation
problem, not a missing construction.
-/

/-- A product of principal units stays strictly inside any ball that contains all the `xᵢ`. -/
theorem valuation_prod_one_add_sub_one_lt {ι : Type*} (x : ι → K)
    {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) (hc1 : c ≤ 1) :
    ∀ s : Finset ι, (∀ i ∈ s, W (x i) < c) → W (∏ i ∈ s, (1 + x i) - 1) < c := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using zero_lt_iff.mpr hc
  | insert a t ha ih =>
      intro hall
      have hQ : W (∏ i ∈ t, (1 + x i) - 1) < c :=
        ih fun i hi ↦ hall i (Finset.mem_insert_of_mem hi)
      have hxa : W (x a) < c := hall a (Finset.mem_insert_self a t)
      set Q : K := ∏ i ∈ t, (1 + x i) - 1 with hQdef
      have hrw : ∏ i ∈ insert a t, (1 + x i) - 1 = x a + Q + x a * Q := by
        rw [Finset.prod_insert ha, hQdef]
        ring
      rw [hrw]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hxa hQ)
      · rw [map_mul]
        calc W (x a) * W Q ≤ 1 * W Q :=
              mul_le_mul_right' (le_of_lt (lt_of_lt_of_le hxa hc1)) _
          _ = W Q := one_mul _
          _ < c := hQ

/-- **The leading term survives.**  If `W (x i₀)` is strictly the largest, the product of the
principal units `1 + xᵢ` sits at exactly the level of `xᵢ₀`. -/
theorem valuation_prod_one_add_sub_one {ι : Type*} [DecidableEq ι] (x : ι → K) (s : Finset ι)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hne : W (x i₀) ≠ 0) (hlt : W (x i₀) < 1)
    (hmax : ∀ i ∈ s, i ≠ i₀ → W (x i) < W (x i₀)) :
    W (∏ i ∈ s, (1 + x i) - 1) = W (x i₀) := by
  have hsplit : s = insert i₀ (s.erase i₀) := (Finset.insert_erase hi₀).symm
  have hnotmem : i₀ ∉ s.erase i₀ := Finset.notMem_erase i₀ s
  set Q : K := ∏ i ∈ s.erase i₀, (1 + x i) - 1 with hQdef
  have hQ : W Q < W (x i₀) := by
    rw [hQdef]
    refine valuation_prod_one_add_sub_one_lt v x hne (le_of_lt hlt) _ fun i hi ↦ ?_
    exact hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  have hrw : ∏ i ∈ s, (1 + x i) - 1 = x i₀ + (Q + x i₀ * Q) := by
    rw [hsplit, Finset.prod_insert hnotmem, hQdef]
    ring
  rw [hrw]
  refine Valuation.map_add_eq_of_lt_left _ ?_
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hQ ?_)
  rw [map_mul]
  calc W (x i₀) * W Q ≤ 1 * W Q := mul_le_mul_right' (le_of_lt hlt) _
    _ = W Q := one_mul _
    _ < W (x i₀) := hQ

/-! ### The heart of the rank-one case

Only the `p`-part of the exponent can move `ε ^ m` towards `1` at `v`, and `a ≠ 0` in `ℤ_p`
bounds that `p`-part.  So the valuations stay bounded away from `0`.
-/

/-- **The rank-one local obstruction.**  If `ε` has infinite order, `m n → a` in `ℤ_p` and
`ε ^ (m n) → 1` in one completion `K_v` with `v ∣ p`, then `a = 0`. -/
theorem eq_zero_of_local_tendsto_one (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) (ε : (𝓞 K)ˣ)
    (hinf : ∀ j : ℕ, 0 < j → ((ε : 𝓞 K) : K) ^ j ≠ 1)
    (a : ℤ_[p]) (m : ℕ → ℤ)
    (hm : Tendsto (fun n ↦ ((m n : ℤ) : ℤ_[p])) atTop (𝓝 a))
    (hloc : Tendsto (fun n ↦ algebraMap K (v.adicCompletion K) (((ε : 𝓞 K) : K) ^ (m n)))
      atTop (𝓝 1)) :
    a = 0 := by
  by_contra ha
  obtain ⟨N, hN, hpN, hxN⟩ := exists_principal_exponent v hv ε
  set x : K := ((ε : 𝓞 K) : K) with hxdef
  -- `θ j := x ^ (N * p ^ j)` is principal, and `j ↦ W (θ j - 1)` is antitone and never `0`.
  have hθp : ∀ j : ℕ, W (x ^ (N * p ^ j) - 1) < 1 := by
    intro j
    have h : x ^ (N * p ^ j) = (x ^ N) ^ (p ^ j) := by rw [← pow_mul]
    rw [h]
    exact lt_of_le_of_lt (valuation_pow_sub_one_le v hxN _) hxN
  have hanti : Antitone (fun j : ℕ ↦ W (x ^ (N * p ^ j) - 1)) := by
    refine antitone_nat_of_succ_le fun j ↦ ?_
    have h : x ^ (N * p ^ (j + 1)) = (x ^ (N * p ^ j)) ^ p := by
      rw [← pow_mul]; ring_nf
    rw [h]
    exact valuation_pow_sub_one_le v (hθp j) _
  -- extract the bound on the `p`-part of `m n`
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hna
  have hev : ∀ᶠ n in atTop, ¬ ((p : ℤ) ^ k ∣ m n) := by
    have hball : ∀ᶠ n in atTop, ‖((m n : ℤ) : ℤ_[p]) - a‖ < ‖a‖ := by
      have h := hm (Metric.ball_mem_nhds a hna)
      simpa [Metric.mem_ball, dist_eq_norm] using h
    filter_upwards [hball] with n hn
    intro hdvd
    have h1 : ‖((m n : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
      rw [PadicInt.norm_int_le_pow_iff_dvd]
      exact_mod_cast hdvd
    have h2 : ‖a‖ ≤ max ‖((m n : ℤ) : ℤ_[p])‖ ‖((m n : ℤ) : ℤ_[p]) - a‖ := by
      have h3 := PadicInt.nonarchimedean ((m n : ℤ) : ℤ_[p]) (-(((m n : ℤ) : ℤ_[p]) - a))
      rw [show ((m n : ℤ) : ℤ_[p]) + (-(((m n : ℤ) : ℤ_[p]) - a)) = a from by ring,
        norm_neg] at h3
      exact h3
    exact absurd h2 (not_le.mpr (max_lt (lt_of_le_of_lt h1 hk) hn))
  -- hence the valuations are bounded below by the (nonzero) value at `j = k`
  have hlow : ∀ᶠ n in atTop,
      W (x ^ (N * p ^ k) - 1) ≤ W (x ^ ((N : ℤ) * m n) - 1) := by
    filter_upwards [hev] with n hn
    obtain ⟨j, t, hjk, hmt, hpt⟩ := exists_pow_split p hp.out.one_lt k (m n) hn
    have hrw : x ^ ((N : ℤ) * m n) = (x ^ (N * p ^ j)) ^ t := by
      rw [hmt, ← zpow_natCast x (N * p ^ j), ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [hrw, valuation_zpow_sub_one v (hθp j) (valuation_intCast_eq_one v hv hpt)]
    exact hanti (le_of_lt hjk)
  -- the local limit forces the valuations to shrink past that bound
  have hne : W (x ^ (N * p ^ k) - 1) ≠ 0 := by
    rw [Valuation.ne_zero_iff, sub_ne_zero]
    exact hinf _ (Nat.mul_pos hN (pow_pos hp.out.pos k))
  set L := v.adicCompletion K with hL
  set F : ℕ → L := fun n ↦ algebraMap K L (x ^ ((N : ℤ) * m n)) with hFdef
  have hF : Tendsto F atTop (𝓝 1) := by
    have h := hloc.pow N
    simp only [one_pow] at h
    refine h.congr fun n ↦ ?_
    rw [hFdef]
    rw [← map_pow, ← zpow_natCast (x ^ (m n)) N, ← zpow_mul]
    congr 2
    ring
  set c := Valued.v.restrict (algebraMap K L (x ^ (N * p ^ k) - 1)) with hc
  have hcemb : MonoidWithZeroHom.ValueGroup₀.embedding c = W (x ^ (N * p ^ k) - 1) := by
    rw [hc, Valuation.embedding_restrict]
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hcne : c ≠ 0 := by
    intro h
    apply hne
    rw [← hcemb, h, map_zero]
  have hzero : (0 : L) ∈ {y : L | Valued.v.restrict y < c} := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact zero_lt_iff.mpr hcne
  have hsub : Tendsto (fun n ↦ F n - 1) atTop (𝓝 0) := by
    simpa using hF.sub (tendsto_const_nhds (x := (1 : L)) (f := atTop))
  have hfin : ∀ᶠ n in atTop, Valued.v.restrict (F n - 1) < c :=
    hsub ((Valued.isOpen_ball L c).mem_nhds hzero)
  obtain ⟨n, hn1, hn2⟩ := (hlow.and hfin).exists
  have hval : Valued.v (F n - 1) = W (x ^ ((N : ℤ) * m n) - 1) := by
    rw [hFdef]
    rw [show (algebraMap K L (x ^ ((N : ℤ) * m n)) - 1)
        = algebraMap K L (x ^ ((N : ℤ) * m n) - 1) by rw [map_sub, map_one]]
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hn2
  rw [Valuation.embedding_restrict, hval, hcemb] at this
  exact absurd hn1 (not_le.mpr this)

end Valuation

/-! ### Leopoldt's conjecture in unit rank `≤ 1`

Now global.  Two ingredients: multiplicative independence of `r` units forces `r ≤ rank K`
(so `r ≤ 1`), and a prime of `𝓞 K` above `p` exists.  Then `eq_zero_of_local_tendsto_one`
finishes.  Note this is unconditional in `K` and `p`: **no** abelian hypothesis, because in rank
`≤ 1` there is no Baker-type linear form to bound.
-/

section Global

variable {K : Type*} [Field K] [NumberField K]

open Module

/-- A multiplicatively independent family of units has at most `rank K` members:
in `Additive (𝓞 K)ˣ`, which has `ℤ`-rank `rank K`, it is `ℤ`-linearly independent. -/
theorem card_le_rank (r : ℕ) (ε : Fin r → (𝓞 K)ˣ)
    (hindep : ∀ m : Fin r → ℤ, ∏ i, ε i ^ m i = 1 → m = 0) : r ≤ NumberField.Units.rank K := by
  have hli : LinearIndependent ℤ (fun i ↦ Additive.ofMul (ε i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h : ∏ i, ε i ^ g i = 1 := by
      have h2 : Additive.ofMul (∏ i, ε i ^ g i) = ∑ i, g i • Additive.ofMul (ε i) := by
        rw [ofMul_prod]
        exact Finset.sum_congr rfl fun i _ ↦ ofMul_zpow _ _
      rw [hg] at h2
      simpa using congrArg Additive.toMul h2
    exact fun i ↦ congrFun (hindep g h) i
  simpa [NumberField.Units.finrank_eq] using hli.fintype_card_le_finrank

/-- Some height-one prime of `𝓞 K` lies above `p` (it is a nonunit, its norm being `p ^ d`). -/
theorem exists_prime_above (p : ℕ) [hp : Fact p.Prime] :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
    rw [NumberField.isUnit_iff_norm]
    have h : ((RingOfIntegers.norm ℚ ((p : ℕ) : 𝓞 K) : ℚ))
        = (p : ℚ) ^ (finrank ℚ K) := by
      rw [RingOfIntegers.coe_norm]
      push_cast
      rw [show ((p : ℕ) : K) = algebraMap ℚ K (p : ℚ) by push_cast; ring, Algebra.norm_algebraMap]
    rw [h]
    have h1 : 1 < (p : ℚ) := by exact_mod_cast hp.out.one_lt
    have h2 : 0 < finrank ℚ K := Module.finrank_pos
    rw [abs_of_nonneg (by positivity)]
    intro hcon
    nlinarith [one_lt_pow₀ h1 (n := finrank ℚ K) (by omega)]
  have hne : Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hnu
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hp0 : ((p : ℕ) : 𝓞 K) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := 𝓞 K)).mpr hp.out.pos.ne'
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hp0 hmem

/-- **Leopoldt's conjecture holds whenever the unit rank is at most `1`** — for every number
field and every prime, with no abelian hypothesis. -/
theorem leopoldt_of_rank_le_one (p : ℕ) [hp : Fact p.Prime]
    (hrank : NumberField.Units.rank K ≤ 1) :
    LeanFormalizations.Literature.LeopoldtConjecture K p := by
  intro r ε hindep a m hm hlocal
  have hr : r ≤ 1 := le_trans (card_le_rank r ε hindep) hrank
  obtain ⟨v, hv⟩ := exists_prime_above (K := K) p
  funext i
  have hsub : ∀ k : Fin r, k = i := by
    intro k
    have h1 := k.isLt
    have h2 := i.isLt
    exact Fin.ext (by omega)
  have hprod : ∀ f : Fin r → ℤ, ∏ k, ε k ^ f k = ε i ^ f i :=
    fun f ↦ Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
      (fun k _ hk ↦ absurd (hsub k) hk)
  have hprodK : ∀ f : Fin r → ℤ, ∏ k, (((ε k : 𝓞 K)) : K) ^ f k = (((ε i : 𝓞 K)) : K) ^ f i :=
    fun f ↦ Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
      (fun k _ hk ↦ absurd (hsub k) hk)
  have hinf : ∀ j : ℕ, 0 < j → (((ε i : 𝓞 K)) : K) ^ j ≠ 1 := by
    intro j hj hcon
    have hOK : ((ε i : 𝓞 K)) ^ j = 1 := by
      have hinj : Function.Injective (algebraMap (𝓞 K) K) :=
        FaithfulSMul.algebraMap_injective (𝓞 K) K
      apply hinj
      rw [map_pow, map_one]
      exact hcon
    have hu : ε i ^ (j : ℤ) = 1 := by
      rw [zpow_natCast]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hOK, Units.val_one])
    have hz := hindep (Pi.single i (j : ℤ)) (by rw [hprod, Pi.single_eq_same]; exact hu)
    have := congrFun hz i
    rw [Pi.single_eq_same] at this
    simp only [Pi.zero_apply] at this
    omega
  refine eq_zero_of_local_tendsto_one v hv (ε i) hinf (a i) (fun n ↦ m n i) (hm i) ?_
  have h := hlocal v hv
  refine h.congr fun n ↦ ?_
  congr 1
  exact hprodK (m n)

end Global

end LeanFormalizations.Leopoldt

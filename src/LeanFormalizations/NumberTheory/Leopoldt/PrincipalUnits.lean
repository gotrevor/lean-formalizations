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

end LeanFormalizations.Leopoldt

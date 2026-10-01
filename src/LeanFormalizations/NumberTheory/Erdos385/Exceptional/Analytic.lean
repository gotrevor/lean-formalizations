/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Exceptional.Count

/-!
# Erdős #385, phase E4: elementary estimates for the parameter choice

* `primorial_le_mul_prod_sub_one`: `y# ≤ y · ∏_{p ≤ y} (p − 1)`.
* `primeCounting_mul_log_ge`: `π(n) log n ≥ n log 2 − log(n + 1)` (Chebyshev).
* `pow_div_le_choose`: `((m − j)/j)^j ≤ C(m, j)`.
-/

namespace LeanFormalizations.Erdos385.Exceptional

open Finset

theorem prod_Icc_two_eq (y : ℕ) (hy : 1 ≤ y) :
    ∏ k ∈ Icc 2 y, (1 - 1 / (k : ℝ)) = 1 / y := by
  induction y with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hI : Icc 2 (n + 1) = insert (n + 1) (Icc 2 n) := by ext; simp; omega
      rw [hI, prod_insert (by simp), ih hn]
      have : (n : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem primorial_le_mul_prod_sub_one (y : ℕ) (hy : 1 ≤ y) :
    (primorial y : ℝ) ≤ y * ∏ p ∈ ps y, ((p : ℝ) - 1) := by
  have hsub : ps y ⊆ Icc 2 y := by
    intro p hp
    have := mem_filter.1 hp
    exact mem_Icc.2 ⟨this.2.two_le, by have := mem_range.1 this.1; omega⟩
  have hle : ∏ k ∈ Icc 2 y, (1 - 1 / (k : ℝ)) ≤ ∏ p ∈ ps y, (1 - 1 / (p : ℝ)) := by
    rw [← prod_sdiff hsub]
    have h1 : ∏ k ∈ Icc 2 y \ ps y, (1 - 1 / (k : ℝ)) ≤ 1 := by
      apply prod_le_one
      · intro k hk
        have : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 (mem_sdiff.1 hk).1).1
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      · intro k hk
        have : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 (mem_sdiff.1 hk).1).1
        have : 0 ≤ 1 / (k : ℝ) := by positivity
        linarith
    have h2 : 0 ≤ ∏ p ∈ ps y, (1 - 1 / (p : ℝ)) := by
      refine prod_nonneg fun p hp => ?_
      have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    calc _ ≤ 1 * ∏ p ∈ ps y, (1 - 1 / (p : ℝ)) := mul_le_mul_of_nonneg_right h1 h2
      _ = _ := one_mul _
  rw [prod_Icc_two_eq y hy] at hle
  have hP : (primorial y : ℝ) = ∏ p ∈ ps y, (p : ℝ) := by
    rw [primorial_eq_prod_ps]; push_cast; rfl
  have hprod : ∏ p ∈ ps y, (1 - 1 / (p : ℝ)) = (∏ p ∈ ps y, ((p : ℝ) - 1)) / primorial y := by
    rw [hP, ← prod_div_distrib]
    refine prod_congr rfl fun p hp => ?_
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_filter.1 hp).2.ne_zero
    field_simp
  rw [hprod, div_le_div_iff₀ (by positivity) (by exact_mod_cast primorial_pos y)] at hle
  linarith

theorem primeCounting_mul_log_ge (n : ℕ) :
    (n : ℝ) * Real.log 2 - Real.log (n + 1) ≤ (Nat.primeCounting n : ℝ) * Real.log n := by
  have h1 := Chebyshev.psi_le_primeCounting_mul_log n
  rw [Chebyshev.psi_eq_log_lcmUpto] at h1
  have h2 : ((2 : ℝ) ^ n) ≤ ((n : ℝ) + 1) * Nat.lcmUpto n := by
    exact_mod_cast Chebyshev.two_pow_le_mul_lcmUpto n
  have hl : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul (by positivity) hl.ne'] at h3
  linarith

theorem pow_div_le_choose (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (((m : ℝ) - j) / j) ^ j ≤ (m.choose j : ℝ) := by
  have h := Nat.pow_le_choose (α := ℝ) j m
  have hf : (j.factorial : ℝ) ≤ (j : ℝ) ^ j := by exact_mod_cast Nat.factorial_le_pow j
  have hcast : (((m + 1 - j : ℕ) : ℝ)) = (m : ℝ) + 1 - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at h
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hnn : (0 : ℝ) ≤ (m : ℝ) - j := by
    have : (j : ℝ) ≤ m := by exact_mod_cast hjm
    linarith
  calc (((m : ℝ) - j) / j) ^ j = ((m : ℝ) - j) ^ j / (j : ℝ) ^ j := div_pow _ _ _
    _ ≤ ((m : ℝ) + 1 - j) ^ j / (j.factorial : ℝ) := by
        apply div_le_div₀ (pow_nonneg (by linarith) _) (pow_le_pow_left₀ hnn (by linarith) _)
          (by exact_mod_cast Nat.factorial_pos j) hf
    _ ≤ _ := h

theorem primeCounting_le_pool_card (y R : ℕ) :
    Nat.primeCounting R ≤ y + 1 + (pool y R).card := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have : Nat.primesLE R ⊆ range (y + 1) ∪ pool y R := by
    intro p hp
    have hp' : p < R + 1 ∧ p.Prime := by
      simpa [Nat.primesLE, Nat.primesBelow_eq_filter_range] using hp
    by_cases hpy : p ≤ y
    · exact mem_union_left _ (mem_range.2 (by omega))
    · exact mem_union_right _ (mem_filter.2 ⟨mem_Ioc.2 ⟨by omega, by omega⟩, hp'.2⟩)
  calc _ ≤ (range (y + 1) ∪ pool y R).card := card_le_card this
    _ ≤ _ := (card_union_le _ _).trans (by simp)

open Filter in
/-- `log x ≤ η x^{1/4}` eventually, for every `η > 0`, along the naturals. -/
theorem eventually_log_le (η : ℝ) (hη : 0 < η) :
    ∀ᶠ y : ℕ in atTop, Real.log y ≤ η * (y : ℝ) ^ ((1 : ℝ) / 4) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound hη
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop 1] with y hy hy1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y : ℝ) ^ ((1 : ℝ) / 4))] at hy
  exact (le_abs_self _).trans hy

theorem rho_bound {m j K s ℓ c : ℝ} (hs : 0 < s) (hℓ : 0 < ℓ) (hj : 0 < j) (hc : 0 < c)
    (hjs : j ≤ 4 * s ^ 2) (hmj : m / 2 ≤ m - j) (hm : s ^ 8 ≤ 8 * ℓ * m)
    (hK : c * s ^ 4 / ℓ ≤ K) (hℓ2 : ℓ ^ 2 ≤ c / 512 * s ^ 2) :
    8 ≤ ((m - j) / j) * (K / s ^ 8) := by
  have hm0 : 0 < m := by
    have : 0 < s ^ 8 := by positivity
    by_contra h; push Not at h; nlinarith
  have e1 : m / (8 * s ^ 2) ≤ (m - j) / j := by
    calc m / (8 * s ^ 2) = (m / 2) / (4 * s ^ 2) := by ring
      _ ≤ (m - j) / j := div_le_div₀ (by linarith) hmj hj hjs
  have e2 : c / (ℓ * s ^ 4) ≤ K / s ^ 8 := by
    calc c / (ℓ * s ^ 4) = (c * s ^ 4 / ℓ) / s ^ 8 := by field_simp
      _ ≤ K / s ^ 8 := div_le_div_of_nonneg_right hK (by positivity)
  have e3 : 8 ≤ m / (8 * s ^ 2) * (c / (ℓ * s ^ 4)) := by
    have : m / (8 * s ^ 2) * (c / (ℓ * s ^ 4)) = (m * ℓ) * c / (8 * ℓ ^ 2 * s ^ 6) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    have h1 : s ^ 8 * c ≤ 8 * (m * ℓ) * c := by
      have := mul_le_mul_of_nonneg_right hm hc.le
      calc s ^ 8 * c ≤ 8 * ℓ * m * c := this
        _ = _ := by ring
    have h2 : 8 * (8 * ℓ ^ 2 * s ^ 6) * 8 ≤ s ^ 8 * c := by
      have := mul_le_mul_of_nonneg_right hℓ2 (by positivity : (0 : ℝ) ≤ 512 * s ^ 6)
      calc 8 * (8 * ℓ ^ 2 * s ^ 6) * 8 = ℓ ^ 2 * (512 * s ^ 6) := by ring
        _ ≤ c / 512 * s ^ 2 * (512 * s ^ 6) := this
        _ = s ^ 8 * c := by ring
    linarith
  calc (8 : ℝ) ≤ _ := e3
    _ ≤ _ := mul_le_mul e1 e2 (by positivity) (by
        have : 0 ≤ m - j := by linarith
        positivity)

/-- The large-sieve weight from `j`-fold products of pool primes is `≥ 8^j`. -/
theorem pool_weight_ge {c : ℝ} (hc : 0 < c) : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ j K : ℕ, 1 ≤ j →
    (j : ℝ) ≤ 4 * Real.sqrt y → c * y / Real.log y ≤ K →
      (8 : ℝ) ^ j ≤ ((pool y (y ^ 2)).card.choose j : ℝ) * ((K : ℝ) / ((y ^ 2 : ℕ) : ℝ)) ^ j := by
  set η : ℝ := min 1 (Real.sqrt (c / 512)) with hηdef
  have hη : 0 < η := lt_min one_pos (Real.sqrt_pos.2 (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ^ 2 ≤ c / 512 := by
    have : η ≤ Real.sqrt (c / 512) := min_le_right _ _
    calc η ^ 2 ≤ Real.sqrt (c / 512) ^ 2 := pow_le_pow_left₀ hη.le this 2
      _ = c / 512 := Real.sq_sqrt (by positivity)
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.1 ((eventually_log_le η hη).and
    (Filter.eventually_ge_atTop 81))
  refine ⟨Y, fun y hy j K hj1 hjy hK => ?_⟩
  obtain ⟨hlog, hy81⟩ := hY y hy
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (y : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hs] at hlog
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hs4 : s ^ 4 = y := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hy81' : (81 : ℝ) ≤ y := by exact_mod_cast hy81
  have hs3 : 3 ≤ s := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h hs0 (by norm_num : (4 : ℕ) ≠ 0)
    rw [hs4] at this; norm_num at this; linarith
  have hsq : Real.sqrt y = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log y := ⟨_, rfl⟩
  rw [← hℓ] at hlog hK
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact Real.log_pos (by linarith)
  have hℓs : ℓ ≤ η * s := hlog
  have hℓs' : ℓ ≤ s := hℓs.trans (by nlinarith)
  -- `m ≥ y² / (8 log y)`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = (pool y (y ^ 2)).card := ⟨_, rfl⟩
  rw [← hmdef]
  have hpi := primeCounting_mul_log_ge (y ^ 2)
  have hpool := primeCounting_le_pool_card y (y ^ 2)
  rw [← hmdef] at hpool
  have hm1 : (Nat.primeCounting (y ^ 2) : ℝ) ≤ y + 1 + m := by exact_mod_cast hpool
  have hlogy2 : Real.log ((y ^ 2 : ℕ) : ℝ) = 2 * ℓ := by
    push_cast; rw [Real.log_pow, hℓ]; norm_num
  have hlog1 : Real.log (((y ^ 2 : ℕ) : ℝ) + 1) ≤ Real.log 2 + 2 * ℓ := by
    have hy1 : (1 : ℝ) ≤ y := by linarith
    rw [← hlogy2, ← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast; nlinarith
  rw [hlogy2] at hpi
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hpic : (Nat.primeCounting (y ^ 2) : ℝ) * (2 * ℓ) ≥ s ^ 8 * 0.69 - 0.7 - 2 * ℓ := by
    have : ((y ^ 2 : ℕ) : ℝ) = s ^ 8 := by push_cast; rw [← hs4]; ring
    rw [this] at hpi hlog1
    nlinarith
  have hm : s ^ 8 ≤ 8 * ℓ * m := by
    have h4 : (Nat.primeCounting (y ^ 2) : ℝ) * (2 * ℓ) ≤ (s ^ 4 + 1 + m) * (2 * ℓ) := by
      rw [← hs4] at hm1; exact mul_le_mul_of_nonneg_right hm1 (by positivity)
    have hsp : 0 < s := by linarith
    have hA : ℓ * s ^ 4 ≤ s ^ 5 := by
      have := mul_le_mul_of_nonneg_right hℓs' (by positivity : 0 ≤ s ^ 4)
      calc ℓ * s ^ 4 ≤ s * s ^ 4 := this
        _ = s ^ 5 := by ring
    have hB : 27 * s ^ 5 ≤ s ^ 8 := by
      have : (27 : ℝ) ≤ s ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num) hs3 3; norm_num at this; linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ s ^ 5)
      calc 27 * s ^ 5 = s ^ 5 * 27 := by ring
        _ ≤ s ^ 5 * s ^ 3 := this
        _ = s ^ 8 := by ring
    have hC : 27 * s ≤ s ^ 5 := by
      have : (27 : ℝ) ≤ s ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num) hs3 4; norm_num at this; linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ s)
      calc 27 * s = s * 27 := by ring
        _ ≤ s * s ^ 4 := this
        _ = s ^ 5 := by ring
    have hD : (3 : ℝ) ≤ s ^ 5 := by linarith
    have h4' : (Nat.primeCounting (y ^ 2) : ℝ) * (2 * ℓ) ≤
        2 * (ℓ * s ^ 4) + 2 * ℓ + 2 * (ℓ * m) := by
      calc _ ≤ (s ^ 4 + 1 + m) * (2 * ℓ) := h4
        _ = _ := by ring
    have : 8 * ℓ * m = 4 * (2 * (ℓ * m)) := by ring
    rw [this]
    linarith
  -- `m − j ≥ m / 2`
  have hj : (j : ℝ) ≤ 4 * s ^ 2 := by rw [← hsq]; exact hjy
  have hjm : (j : ℝ) ≤ m / 2 := by
    have hsp : 0 < s := by linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h64 : 64 * s ^ 3 ≤ s ^ 7 := by
      have : (64 : ℝ) ≤ s ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num) hs3 4; norm_num at this; linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ s ^ 3)
      calc 64 * s ^ 3 = s ^ 3 * 64 := by ring
        _ ≤ s ^ 3 * s ^ 4 := this
        _ = s ^ 7 := by ring
    have h7 : s ^ 8 ≤ 8 * s * m := by
      have := mul_le_mul_of_nonneg_right hℓs' (by positivity : (0 : ℝ) ≤ 8 * m)
      calc s ^ 8 ≤ 8 * ℓ * m := hm
        _ = ℓ * (8 * m) := by ring
        _ ≤ s * (8 * m) := this
        _ = 8 * s * m := by ring
    have h8 : s * (8 * s ^ 2) ≤ s * m := by
      have : s * (8 * s ^ 2) * 8 ≤ s * m * 8 := by
        calc s * (8 * s ^ 2) * 8 = 64 * s ^ 3 := by ring
          _ ≤ s ^ 7 := h64
          _ ≤ s ^ 7 * 1 := by ring_nf; rfl
          _ ≤ 8 * s * m := by
            have : s ^ 7 = s ^ 8 / s := by field_simp
            rw [this, mul_one, div_le_iff₀ hsp]; nlinarith
          _ = s * m * 8 := by ring
      linarith
    have := le_of_mul_le_mul_left h8 hsp
    linarith
  have hjm' : j ≤ m := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : (j : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hch := pow_div_le_choose m j hj1 hjm'
  -- the base `ρ`
  have hR : ((y ^ 2 : ℕ) : ℝ) = s ^ 8 := by push_cast; rw [← hs4]; ring
  have hK' : c * s ^ 4 / ℓ ≤ K := by rw [hs4]; exact hK
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hρ : 8 ≤ (((m : ℝ) - j) / j) * ((K : ℝ) / ((y ^ 2 : ℕ) : ℝ)) := by
    rw [hR]
    have hℓ2 : ℓ ^ 2 ≤ c / 512 * s ^ 2 := by
      calc ℓ ^ 2 ≤ (η * s) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓs 2
        _ = η ^ 2 * s ^ 2 := by ring
        _ ≤ c / 512 * s ^ 2 := by gcongr
    exact rho_bound (by linarith) hℓ0 hj0 hc hj (by linarith) hm hK' hℓ2
  calc (8 : ℝ) ^ j ≤ ((((m : ℝ) - j) / j) * ((K : ℝ) / ((y ^ 2 : ℕ) : ℝ))) ^ j :=
        pow_le_pow_left₀ (by norm_num) hρ j
    _ = (((m : ℝ) - j) / j) ^ j * ((K : ℝ) / ((y ^ 2 : ℕ) : ℝ)) ^ j := mul_pow _ _ _
    _ ≤ _ := by gcongr

open Filter in
/-- The real-variable conditions on `L = log X` used in the parameter choice. -/
theorem eventually_L_conditions {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, 2 * Real.log L + L ^ ((1 : ℝ) / 2 - ε) ≤ L ∧
      3 ≤ L ^ (ε / 2) ∧ Real.log L ≤ L ^ ((1 : ℝ) / 2 - ε) ∧
      L * Real.log 4 / 8 + 2 * (L ^ ((1 : ℝ) / 2 - ε) + 1) * Real.log L + 1 ≤ L / 2 ∧
      1 ≤ L := by
  set θ : ℝ := 1 / 2 - ε with hθ
  have hθ0 : 0 < θ := by linarith
  have hd := (isLittleO_log_rpow_atTop hθ0).bound (zero_lt_one)
  have hq := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound (zero_lt_one)
  have t1 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - θ)).eventually_ge_atTop 3
  have t2 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < ε / 2)).eventually_ge_atTop 3
  have t3 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 25
  filter_upwards [hd, hq, t1, t2, t3, eventually_ge_atTop (1 : ℝ)] with L hd hq t1 t2 t3 hL1
  have hL0 : 0 ≤ L := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hL0 θ)] at hd
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hL0 (1 / 4))] at hq
  have hd' : Real.log L ≤ L ^ θ := (le_abs_self _).trans hd
  have hq' : Real.log L ≤ L ^ ((1 : ℝ) / 4) := (le_abs_self _).trans hq
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hsplit : L = L ^ θ * L ^ (1 - θ) := by
    rw [← Real.rpow_add (by linarith)]; simp
  have hθp : 0 ≤ L ^ θ := Real.rpow_nonneg hL0 _
  have hb : 3 * L ^ θ ≤ L := by
    have := mul_le_mul_of_nonneg_left t1 hθp
    linarith
  refine ⟨by linarith, t2, hd', ?_, hL1⟩
  -- (e)
  have hq4 : L ^ ((1 : ℝ) / 4) * L ^ ((3 : ℝ) / 4) = L := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hθh : L ^ θ ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h12 : 1 ≤ L ^ ((1 : ℝ) / 2) := Real.one_le_rpow hL1 (by norm_num)
  have h34 : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 4) = L ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hA : (L ^ θ + 1) * Real.log L ≤ 2 * L ^ ((3 : ℝ) / 4) := by
    calc (L ^ θ + 1) * Real.log L ≤ (2 * L ^ ((1 : ℝ) / 2)) * L ^ ((1 : ℝ) / 4) :=
          mul_le_mul (by linarith) hq' hlog0 (by positivity)
      _ = 2 * L ^ ((3 : ℝ) / 4) := by rw [mul_assoc, h34]
  have h34p : 0 ≤ L ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hL0 _
  have hB : 25 * L ^ ((3 : ℝ) / 4) ≤ L := by
    calc 25 * L ^ ((3 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 4) * L ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right t3 h34p
      _ = L := hq4
  have hl4 : Real.log 4 < 1.3863 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have hL25 : 25 ≤ L := by
    have : (25 : ℝ) ≤ L ^ ((1 : ℝ) / 4) := t3
    have h1 : L ^ ((1 : ℝ) / 4) ≤ L := by
      calc L ^ ((1 : ℝ) / 4) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L := Real.rpow_one L
    linarith
  nlinarith

end LeanFormalizations.Erdos385.Exceptional

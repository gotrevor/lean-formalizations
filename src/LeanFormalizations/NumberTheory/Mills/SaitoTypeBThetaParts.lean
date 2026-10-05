/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.SaitoTypeBRecords
import LeanFormalizations.NumberTheory.PrimeIntervals.BHPTests

/-!
# Phase 64a: Saito's Type B pieces for a general short-interval exponent `θ`

`θ`-parametric copies of the BHP-specific steps in `SaitoTypeBParts.lean` and
`SaitoTypeBRecords.lean` (the originals keep their statements).  Parameters: the prime input
`PrimesShortInterval θ` (`0 ≤ θ < 1`), an eventual lower bound `r` on the ratios `C(k+1)/C k`, and
a decay exponent `μ > 0` with `μ ≤ (1 − θ) r − 1` (Saito (5.17): `{ξ^(C k)} ≪ ⌊ξ^(C k)⌋^(−μ)`).

**The degree bound caps the threshold at `5/9`.**  For the E+ exponents `C k = 3^(k+j) + s`
the ratios tend to `3`, so `μ` can be anything below `2 − 3θ`.  The Baker-free degree bound
(`card_le_two_of_records`, `card_mul_le_shift`) is `(ℓ − 1) μ ≤ 1`, and the degree-3 endgame needs
`ℓ ≤ 3`, i.e. `μ > 1/3`, i.e. `θ < 5/9`.  For `θ ∈ [5/9, 2/3)` the decay alone permits Pisot
degree up to `1 + 1/(2 − 3θ)`, and nothing here excludes degree `≥ 4`.
-/

namespace LeanFormalizations.Mills.SaitoTypeB

open LeanFormalizations.Literature LeanFormalizations.Mills Filter
open LeanFormalizations.Mills.ShiftedMillsAll LeanFormalizations.BHPTests

theorem theta_one_lt {θ r μ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hμ0 : 0 < μ)
    (hμ : μ ≤ (1 - θ) * r - 1) : 1 < r := by
  nlinarith

theorem theta_mul_le {θ r μ c : ℝ} (hθ1 : θ < 1) (hμ : μ ≤ (1 - θ) * r - 1) (hc : r ≤ c) :
    θ * c ≤ c - 1 - μ := by
  nlinarith

theorem theta_mu_le {θ r μ c : ℝ} (hθ1 : θ < 1) (hμ : μ ≤ (1 - θ) * r - 1) (hc : r ≤ c) :
    μ ≤ (1 - θ) * c - 1 := by
  nlinarith

/-- The E+ ratios are eventually `≥ r` for any `r < 3`. -/
theorem shiftC_ratio_ev {s : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) {r : ℝ} (hr3 : r < 3) :
    ∃ K₀, ∀ k ≥ K₀, r * shiftC j s k ≤ shiftC j s (k + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|r - 1| * |(s : ℝ)| / (3 - r))
  refine ⟨N + 1, fun k hk => ?_⟩
  have h1 := shiftC_cast hj1 (k := k) (by omega)
  have h2 := shiftC_cast hj1 (k := k + 1) (by omega)
  have e1 : (shiftC j s k : ℝ) = (3 : ℝ) ^ (k + j) + s := by exact_mod_cast h1
  have e2 : (shiftC j s (k + 1) : ℝ) = 3 * (3 : ℝ) ^ (k + j) + s := by
    have : (shiftC j s (k + 1) : ℝ) = (3 : ℝ) ^ (k + 1 + j) + s := by exact_mod_cast h2
    rw [this, show k + 1 + j = (k + j) + 1 by omega, pow_succ]; ring
  have hk3 : (N : ℝ) ≤ (3 : ℝ) ^ (k + j) := by
    have : N ≤ 3 ^ (k + j) := le_trans (by omega) (Nat.lt_pow_self (by norm_num)).le
    exact_mod_cast this
  have h3r : 0 < 3 - r := by linarith
  have hb : |r - 1| * |(s : ℝ)| < (3 - r) * (3 : ℝ) ^ (k + j) := by
    rw [div_lt_iff₀ h3r] at hN; nlinarith
  have hc : (r - 1) * s ≤ |r - 1| * |(s : ℝ)| := by
    rw [← abs_mul]; exact le_abs_self _
  rw [e1, e2]; nlinarith

/-- **One BHP step.**  For all large `q` and every real `c ≥ 29/10` there is a prime `q'` with
`q^c ≤ q' ≤ q^c + q^(21c/40)` and `q' + 1 < (q + 1)^c`. -/
theorem bhp_step_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) :
    ∃ X : ℕ, ∀ q ≥ X, ∀ c : ℝ, ρ ≤ c → ∃ q' : ℕ, q'.Prime ∧
      (q : ℝ) ^ c ≤ q' ∧ (q' : ℝ) ≤ (q : ℝ) ^ c + (q : ℝ) ^ (θ * c) ∧
      (q' : ℝ) + 1 < ((q : ℝ) + 1) ^ c := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  obtain ⟨d₀, hd₀, X, hX⟩ := hP
  refine ⟨max 2 ⌈X⌉₊, fun q hq c hc => ?_⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_left _ _) hq
  have hqX : X ≤ q := le_trans (Nat.le_ceil X) (by exact_mod_cast le_trans (le_max_right _ _) hq)
  have hq0 : (0 : ℝ) < q := by linarith
  have hc1 : (1 : ℝ) ≤ c := by linarith
  set x : ℝ := (q : ℝ) ^ c with hx
  have hxq : (q : ℝ) ≤ x := by
    calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le (by linarith) hc1
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hcount := hX x (le_trans hqX hxq)
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hcpos : 0 < primesIn x (x + x ^ θ) := by
    rcases Nat.eq_zero_or_pos (primesIn x (x + x ^ θ)) with h0 | h0
    · rw [h0] at hcount
      have : (0:ℝ) < d₀ * x ^ θ / Real.log x :=
        div_pos (mul_pos hd₀ (Real.rpow_pos_of_pos hxpos _)) hlogx
      norm_num at hcount
      linarith
    · exact h0
  unfold primesIn at hcpos
  obtain ⟨p, hpmem⟩ := Finset.card_pos.1 hcpos
  simp only [Finset.mem_filter, Finset.mem_Icc] at hpmem
  obtain ⟨⟨hplo, hphi⟩, hp⟩ := hpmem
  have hxθ : x ^ θ = (q : ℝ) ^ (θ * c) := by
    rw [hx, ← Real.rpow_mul hq0.le]; ring_nf
  have hplo' : x ≤ p := le_trans (Nat.le_ceil x) (by exact_mod_cast hplo)
  have hphi' : (p : ℝ) ≤ x + (q : ℝ) ^ (θ * c) := by
    rw [← hxθ]
    exact le_trans (by exact_mod_cast hphi) (Nat.floor_le (by positivity))
  refine ⟨p, hp, hplo', hphi', ?_⟩
  -- `(q+1)^c ≥ q^c + c q^(c−1)` (Bernoulli) and `q^(21c/40) + 1 ≤ 2 q^(c−1)`
  have hbern : x + c * (q : ℝ) ^ (c - 1) ≤ ((q : ℝ) + 1) ^ c := by
    have hb := one_add_mul_self_le_rpow_one_add (s := 1 / (q : ℝ)) (by
      have : 0 ≤ 1 / (q : ℝ) := by positivity
      linarith) hc1
    have hsplit : ((q : ℝ) + 1) ^ c = (q : ℝ) ^ c * (1 + 1 / (q : ℝ)) ^ c := by
      rw [← Real.mul_rpow hq0.le (by positivity)]
      congr 1; field_simp
    have hqc1 : (q : ℝ) ^ (c - 1) = (q : ℝ) ^ c / q := Real.rpow_sub_one hq0.ne' c
    rw [hsplit, hqc1, hx]
    have hxp : 0 < (q : ℝ) ^ c := Real.rpow_pos_of_pos hq0 c
    calc (q : ℝ) ^ c + c * ((q : ℝ) ^ c / q) = (q : ℝ) ^ c * (1 + c * (1 / q)) := by
          field_simp
      _ ≤ (q : ℝ) ^ c * (1 + 1 / (q : ℝ)) ^ c := mul_le_mul_of_nonneg_left hb hxp.le
  have hθle : (q : ℝ) ^ (θ * c) ≤ (q : ℝ) ^ (c - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [theta_mul_le hθ1 hμ hc])
  have h1le : (1 : ℝ) ≤ (q : ℝ) ^ (c - 1) := Real.one_le_rpow (by linarith) (by linarith)
  have hpos : 0 < (q : ℝ) ^ (c - 1) := by linarith
  nlinarith

/-- **Saito Lemma 5.2** (ratios eventually `≥ 29/10`, so BHP alone continues the chain).  If the
floors `p_k = ⌊ξ^(C k)⌋₊` of the least Mills number satisfy the lower chain condition
`p_k^(1/C k) ≤ p_(k+1)^(1/C(k+1))` from some `k₁` on, then eventually
`p_(k+1) ≤ p_k^(c_k) + p_k^(21 c_k/40)`. -/
theorem window_of_least_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) {C : ℕ → ℕ} (h1 : 1 ≤ C 1)
    (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, ρ * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) (hnot : ∀ m ≥ 1, ∀ t : ℤ, ξ ^ C m ≠ (t : ℝ))
    {k₁ : ℕ} (hlow : ∀ k ≥ k₁, root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1))) :
    ∃ k₀, ∀ k ≥ k₀, (⌊ξ ^ C (k + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C k⌋₊ : ℝ) ^ ratio C k + (⌊ξ ^ C k⌋₊ : ℝ) ^ (θ * ratio C k) := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  by_contra hcon
  push_neg at hcon
  obtain ⟨X, hX⟩ := bhp_step_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hξ0 : 0 < ξ := by linarith
  have hCge := C_ge_one h1 h2
  set p : ℕ → ℕ := fun k => ⌊ξ ^ C k⌋₊ with hp
  set k₁' := max (max k₁ K₀) 1 with hk₁'
  obtain ⟨δ, hδ, hδk⟩ := exists_delta hnot hξ0 k₁'
  set B : ℝ := (C k₁' : ℝ) * ξ ^ C k₁' with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M1, hM1⟩ := eventually_atTop.1
    ((floor_tendsto h1 h2 hξ1).eventually_ge_atTop (X : ℝ))
  set M2 := ⌈B / δ⌉₊ + 1 with hM2
  obtain ⟨m, hm, hviol⟩ := hcon (max (max M1 M2) (k₁' + 1))
  have hmM1 : M1 ≤ m := by omega
  have hmM2 : M2 ≤ m := by omega
  have hmk : k₁' + 1 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmK : K₀ ≤ m := by omega
  -- the chain
  have hratio : ∀ k ≥ K₀, 1 ≤ k → ρ ≤ ratio C k := by
    intro k hk hk1
    have hCk : (0 : ℝ) < C k := by exact_mod_cast hCge k hk1
    rw [ratio, le_div_iff₀ hCk]; exact hEv k hk
  have hX' : ∀ q k : ℕ, ∃ q' : ℕ, X ≤ q → K₀ ≤ k → 1 ≤ k → (q'.Prime ∧
      (q : ℝ) ^ ratio C k ≤ q' ∧ (q' : ℝ) ≤ (q : ℝ) ^ ratio C k + (q : ℝ) ^ (θ * ratio C k) ∧
      (q' : ℝ) + 1 < ((q : ℝ) + 1) ^ ratio C k) := by
    intro q k
    by_cases h : X ≤ q ∧ K₀ ≤ k ∧ 1 ≤ k
    · obtain ⟨q', hq'⟩ := hX q h.1 (ratio C k) (hratio k h.2.1 h.2.2)
      exact ⟨q', fun _ _ _ => hq'⟩
    · exact ⟨0, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose nxt hnxt using hX'
  let r : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (p m) (fun n r => nxt r (m + n)) n
  have hr0 : r 0 = p m := rfl
  have hrs : ∀ n, r (n + 1) = nxt (r n) (m + n) := fun n => rfl
  have hpmX : X ≤ p m := by exact_mod_cast hM1 m hmM1
  have hrX : ∀ n, X ≤ r n ∧ (r n).Prime := by
    intro n
    induction n with
    | zero => exact ⟨hpmX, hξS.2 m hm1⟩
    | succ n ih =>
      obtain ⟨hpr, hlo, -, -⟩ := hnxt (r n) (m + n) ih.1 (by omega) (by omega)
      refine ⟨?_, by rw [hrs]; exact hpr⟩
      rw [hrs]
      have hq1 : (1 : ℝ) ≤ (Nat.cast (r n) : ℝ) := by exact_mod_cast ih.2.one_lt.le
      have : ((r n : ℕ) : ℝ) ≤ ((r n : ℕ) : ℝ) ^ ratio C (m + n) := by
        calc ((r n : ℕ) : ℝ) = ((r n : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1
              (by linarith [hratio (m + n) (by omega) (by omega)])
      have : ((r n : ℕ) : ℝ) ≤ nxt (r n) (m + n) := le_trans this hlo
      exact le_trans ih.1 (by exact_mod_cast this)
  set q : ℕ → ℕ := fun j => r (j - m) with hq
  have hqs : ∀ j ≥ m, q (j + 1) = nxt (q j) j := by
    intro j hj
    simp only [hq, show j + 1 - m = (j - m) + 1 by omega, hrs, show m + (j - m) = j by omega]
  have hstep : ∀ j ≥ m, ((q j : ℕ) : ℝ) ^ ratio C j ≤ ((q (j + 1) : ℕ) : ℝ) ∧
      ((q (j + 1) : ℕ) : ℝ) ≤ ((q j : ℕ) : ℝ) ^ ratio C j + ((q j : ℕ) : ℝ) ^ (θ * ratio C j) ∧
      ((q (j + 1) : ℕ) : ℝ) + 1 < (((q j : ℕ) : ℝ) + 1) ^ ratio C j := by
    intro j hj
    rw [hqs j hj]
    obtain ⟨-, a, b, c⟩ := hnxt (q j) j (hrX (j - m)).1 (by omega) (by omega)
    exact ⟨a, b, c⟩
  have hCpos : ∀ k ≥ m, 0 < C k := fun k hk => hCge k (by omega)
  have hrat_eq : ∀ k ≥ m, ratio C k = ((C (k + 1) : ℕ) : ℝ) / (C k : ℕ) := fun k _ => rfl
  obtain ⟨ζ, hζ0, hζfl, hζU⟩ := exists_of_nested (q := q) (k₀ := m) hCpos
    (by simp only [hq, Nat.sub_self, hr0]; exact (hξS.2 m hm1).one_lt.le)
    (fun j hj => root_le_root (Nat.cast_nonneg _) (hCpos j hj) (hCpos (j + 1) (by omega))
      (hstep j hj).1)
    (fun j hj => root_lt_root' (by positivity) (by positivity) (hCpos (j + 1) (by omega))
      (hCpos j hj) (hstep j hj).2.2)
  have hqm : q m = p m := by simp [hq, hr0]
  -- `ζ < ξ`
  have hq1lt : q (m + 1) + 1 ≤ p (m + 1) := by
    have h := (hstep m le_rfl).2.1
    rw [hqm] at h
    have : ((q (m + 1) : ℕ) : ℝ) < p (m + 1) := lt_of_le_of_lt h (hviol)
    exact_mod_cast this
  have hζξ : ζ < ξ := by
    have hU := hζU (m + 1) (by omega)
    have h2' : root (((q (m + 1) : ℕ) : ℝ) + 1) (C (m + 1)) ≤ root (ξ ^ C (m + 1)) (C (m + 1)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have : ((q (m + 1) + 1 : ℕ) : ℝ) ≤ p (m + 1) := by exact_mod_cast hq1lt
      push_cast at this
      exact le_trans this (Nat.floor_le (by positivity))
    have h3' : root (ξ ^ C (m + 1)) (C (m + 1)) = ξ :=
      Real.pow_rpow_inv_natCast hξ0.le (hCpos (m + 1) (by omega)).ne'
    linarith
  -- `ζ^(C m) ≥ p m`
  have hζm : (p m : ℝ) ≤ ζ ^ C m := by
    have := hζfl m le_rfl
    rw [hqm] at this
    rw [← this]; exact Nat.floor_le (by positivity)
  have hpm2 : (2 : ℝ) ≤ p m := by exact_mod_cast (hξS.2 m hm1).two_le
  have hζ1 : 1 < ζ := by
    by_contra h
    push_neg at h
    have : ζ ^ C m ≤ 1 := pow_le_one₀ hζ0.le h
    linarith
  -- closeness: `C m (ξ − ζ) < 1`
  have hclose : (C m : ℝ) * (ξ - ζ) < 1 := by
    have hge := pow_sub_pow_ge hζ0 hζξ.le (C m)
    have hlt : ξ ^ C m < (p m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpow1 : (1 : ℝ) ≤ ζ ^ (C m - 1) := one_le_pow₀ hζ1.le
    have hd : 0 ≤ ξ - ζ := by linarith
    have hCm0 : (0 : ℝ) ≤ C m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow1 (mul_nonneg hCm0 hd)]
  -- the floors of `ζ`
  have hfloor : ∀ k ≥ 1, ⌊ζ ^ C k⌋₊ = p k ∨ ⌊ζ ^ C k⌋₊ = q k ∧ m ≤ k := by
    intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · left
      rw [Nat.floor_eq_iff (by positivity)]
      refine ⟨?_, lt_of_lt_of_le (pow_lt_pow_left₀ hζξ hζ0.le (by have := hCge k hk; omega))
        (Nat.lt_floor_add_one _).le⟩
      rcases Nat.lt_or_ge k k₁' with hk1 | hk1
      · -- the `δ` trick
        have hδ' := hδk k hk hk1.le
        have hle := pow_sub_pow_le hζ0.le hζξ.le (C k)
        have hCk : (C k : ℝ) ≤ C k₁' := by
          rcases Nat.lt_or_ge k k₁' with h | h
          · exact_mod_cast (C_strictMonoOn h1 h2 hk h).le
          · omega
        have hξk : ξ ^ (C k - 1) ≤ ξ ^ C k₁' :=
          pow_le_pow_right₀ hξ1.le (le_trans (Nat.sub_le _ _) (by exact_mod_cast hCk))
        have hBδ : B < (C m : ℝ) * δ := by
          have h1' : B / δ < M2 := by
            have := Nat.le_ceil (B / δ); rw [hM2]; push_cast; linarith
          have h2' : (M2 : ℝ) ≤ C m := by exact_mod_cast le_trans hmM2 (le_C h1 h2 m hm1)
          rw [div_lt_iff₀ hδ] at h1'
          nlinarith
        have hd : 0 ≤ ξ - ζ := by linarith
        have hkey : ξ ^ C k - ζ ^ C k < δ := by
          have e1 : (C k : ℝ) * ξ ^ (C k - 1) * (ξ - ζ) ≤ B * (ξ - ζ) := by
            apply mul_le_mul_of_nonneg_right _ hd
            exact mul_le_mul hCk hξk (by positivity) (by positivity)
          have hCm : (0 : ℝ) < C m := by exact_mod_cast hCge m hm1
          have e2 : B * (ξ - ζ) < δ := by
            by_cases hB0' : B = 0
            · rw [hB0']; simpa using hδ
            have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB0')
            have : B * (ξ - ζ) * C m < δ * C m := by
              calc B * (ξ - ζ) * C m = B * ((C m : ℝ) * (ξ - ζ)) := by ring
                _ < B * 1 := mul_lt_mul_of_pos_left hclose hBpos
                _ = B := by ring
                _ < (C m : ℝ) * δ := hBδ
                _ = δ * C m := by ring
            exact lt_of_mul_lt_mul_right this hCm.le
          linarith
        linarith
      · -- the lower chain from `k` to `m`
        have hchain : ∀ d, k + d ≤ m → root (p k) (C k) ≤ root (p (k + d)) (C (k + d)) := by
          intro d
          induction d with
          | zero => intro _; simp
          | succ d ih =>
            intro hd
            exact le_trans (ih (by omega)) (hlow (k + d) (by omega))
        have h1' := hchain (m - k) (by omega)
        rw [show k + (m - k) = m by omega] at h1'
        have h2' : root (p m) (C m) ≤ ζ := by
          have := Real.rpow_le_rpow (by positivity) hζm
            (inv_nonneg.2 (Nat.cast_nonneg (C m)))
          rwa [Real.pow_rpow_inv_natCast hζ0.le (hCpos m le_rfl).ne'] at this
        have h3' := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_trans h1' h2')
          (C k)
        rwa [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by have := hCge k hk; omega)]
          at h3'
    · right
      exact ⟨hζfl k hkm, hkm⟩
  have hζS : ζ ∈ millsSet C := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rcases hfloor k hk with h | ⟨h, hkm⟩
    · rw [h]; exact hξS.2 k hk
    · rw [h]; exact (hrX (k - m)).2
  exact absurd (hξ.2 hζS) (not_le.2 hζξ)

/-- **Saito Lemma 5.3 at `θ = 21/40`, ratios `≥ 29/10`**: in case (II),
`{ξ^(C k)} ≤ 2 ⌊ξ^(C k)⌋^(−151/400)` eventually. -/
theorem eventually_fract_le_theta {θ ρ μ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) {C : ℕ → ℕ} (h1 : 1 ≤ C 1) (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1))
    {K₀ : ℕ} (hEv : ∀ k ≥ K₀, ρ * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : ξ ∈ millsSet C) {k₀ : ℕ}
    (hII : ∀ k ≥ k₀, (⌊ξ ^ C (k + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C k⌋₊ : ℝ) ^ ratio C k + (⌊ξ ^ C k⌋₊ : ℝ) ^ (θ * ratio C k)) :
    ∃ k₂, ∀ k ≥ k₂, Int.fract (ξ ^ C k) ≤ 2 * (⌊ξ ^ C k⌋₊ : ℝ) ^ (-μ) := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  refine ⟨max k₀ (max K₀ 1), fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hξ1 : 1 < ξ := hξ.1
  have hξ0 : 0 < ξ := by linarith
  have hCk : 0 < C k := C_ge_one h1 h2 k hk1
  have hc : ρ ≤ ratio C k := by
    have hCk' : (0 : ℝ) < C k := by exact_mod_cast hCk
    rw [ratio, le_div_iff₀ hCk']; exact hEv k (by omega)
  set x := ξ ^ C k with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
  have hxc : x ^ ratio C k < (⌊ξ ^ C (k + 1)⌋₊ : ℝ) + 1 := by
    rw [hx, pow_ratio hξ0 hCk]; exact Nat.lt_floor_add_one _
  have hw := fract_le_of_window (θ := θ) hx1 (by linarith) hθ0 hθ1 hxc
    (hII k (by omega))
  set p : ℝ := (⌊x⌋₊ : ℝ) with hp
  have hp1 : 1 ≤ p := by have := Nat.floor_pos.2 hx1; rw [hp]; exact_mod_cast this
  have hA : p ^ μ ≤ p ^ ((1 - θ) * ratio C k - 1) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (theta_mu_le hθ1 hμ hc)
  have hA0 : 0 < p ^ μ := by positivity
  have hc1 : (1 : ℝ) ≤ ratio C k := by linarith
  calc Int.fract x ≤ 2 / (ratio C k * p ^ ((1 - θ) * ratio C k - 1)) := hw
    _ ≤ 2 / p ^ μ := by
        apply div_le_div_of_nonneg_left (by norm_num) hA0
        nlinarith
    _ = 2 * p ^ (-μ) := by
        rw [Real.rpow_neg (by linarith), div_eq_mul_inv]

/-- **Saito Lemma 5.2 at records** (no lower-chain hypothesis): at every large record the BHP
window holds. -/
theorem window_at_record_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) {C : ℕ → ℕ} (h1 : 1 ≤ C 1)
    (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, ρ * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) :
    ∃ k₀, ∀ m ≥ k₀, IsRecord C ξ m → (⌊ξ ^ C (m + 1)⌋₊ : ℝ) ≤
      (⌊ξ ^ C m⌋₊ : ℝ) ^ ratio C m + (⌊ξ ^ C m⌋₊ : ℝ) ^ (θ * ratio C m) := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  by_contra hcon
  push_neg at hcon
  obtain ⟨X, hX⟩ := bhp_step_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hξ0 : 0 < ξ := by linarith
  have hCge := C_ge_one h1 h2
  set p : ℕ → ℕ := fun k => ⌊ξ ^ C k⌋₊ with hp
  set k₁' := max K₀ 1 with hk₁'
  obtain ⟨M1, hM1⟩ := eventually_atTop.1
    ((floor_tendsto h1 h2 hξ1).eventually_ge_atTop (X : ℝ))
  obtain ⟨m, hm, hrec, hviol⟩ := hcon (max M1 (k₁' + 1))
  have hmM1 : M1 ≤ m := by omega
  have hmk : k₁' + 1 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmK : K₀ ≤ m := by omega
  -- the chain
  have hratio : ∀ k ≥ K₀, 1 ≤ k → ρ ≤ ratio C k := by
    intro k hk hk1
    have hCk : (0 : ℝ) < C k := by exact_mod_cast hCge k hk1
    rw [ratio, le_div_iff₀ hCk]; exact hEv k hk
  have hX' : ∀ q k : ℕ, ∃ q' : ℕ, X ≤ q → K₀ ≤ k → 1 ≤ k → (q'.Prime ∧
      (q : ℝ) ^ ratio C k ≤ q' ∧ (q' : ℝ) ≤ (q : ℝ) ^ ratio C k + (q : ℝ) ^ (θ * ratio C k) ∧
      (q' : ℝ) + 1 < ((q : ℝ) + 1) ^ ratio C k) := by
    intro q k
    by_cases h : X ≤ q ∧ K₀ ≤ k ∧ 1 ≤ k
    · obtain ⟨q', hq'⟩ := hX q h.1 (ratio C k) (hratio k h.2.1 h.2.2)
      exact ⟨q', fun _ _ _ => hq'⟩
    · exact ⟨0, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose nxt hnxt using hX'
  let r : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (p m) (fun n r => nxt r (m + n)) n
  have hr0 : r 0 = p m := rfl
  have hrs : ∀ n, r (n + 1) = nxt (r n) (m + n) := fun n => rfl
  have hpmX : X ≤ p m := by exact_mod_cast hM1 m hmM1
  have hrX : ∀ n, X ≤ r n ∧ (r n).Prime := by
    intro n
    induction n with
    | zero => exact ⟨hpmX, hξS.2 m hm1⟩
    | succ n ih =>
      obtain ⟨hpr, hlo, -, -⟩ := hnxt (r n) (m + n) ih.1 (by omega) (by omega)
      refine ⟨?_, by rw [hrs]; exact hpr⟩
      rw [hrs]
      have hq1 : (1 : ℝ) ≤ (Nat.cast (r n) : ℝ) := by exact_mod_cast ih.2.one_lt.le
      have : ((r n : ℕ) : ℝ) ≤ ((r n : ℕ) : ℝ) ^ ratio C (m + n) := by
        calc ((r n : ℕ) : ℝ) = ((r n : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1
              (by linarith [hratio (m + n) (by omega) (by omega)])
      have : ((r n : ℕ) : ℝ) ≤ nxt (r n) (m + n) := le_trans this hlo
      exact le_trans ih.1 (by exact_mod_cast this)
  set q : ℕ → ℕ := fun j => r (j - m) with hq
  have hqs : ∀ j ≥ m, q (j + 1) = nxt (q j) j := by
    intro j hj
    simp only [hq, show j + 1 - m = (j - m) + 1 by omega, hrs, show m + (j - m) = j by omega]
  have hstep : ∀ j ≥ m, ((q j : ℕ) : ℝ) ^ ratio C j ≤ ((q (j + 1) : ℕ) : ℝ) ∧
      ((q (j + 1) : ℕ) : ℝ) ≤ ((q j : ℕ) : ℝ) ^ ratio C j + ((q j : ℕ) : ℝ) ^ (θ * ratio C j) ∧
      ((q (j + 1) : ℕ) : ℝ) + 1 < (((q j : ℕ) : ℝ) + 1) ^ ratio C j := by
    intro j hj
    rw [hqs j hj]
    obtain ⟨-, a, b, c⟩ := hnxt (q j) j (hrX (j - m)).1 (by omega) (by omega)
    exact ⟨a, b, c⟩
  have hCpos : ∀ k ≥ m, 0 < C k := fun k hk => hCge k (by omega)
  have hrat_eq : ∀ k ≥ m, ratio C k = ((C (k + 1) : ℕ) : ℝ) / (C k : ℕ) := fun k _ => rfl
  obtain ⟨ζ, hζ0, hζfl, hζU⟩ := exists_of_nested (q := q) (k₀ := m) hCpos
    (by simp only [hq, Nat.sub_self, hr0]; exact (hξS.2 m hm1).one_lt.le)
    (fun j hj => root_le_root (Nat.cast_nonneg _) (hCpos j hj) (hCpos (j + 1) (by omega))
      (hstep j hj).1)
    (fun j hj => root_lt_root' (by positivity) (by positivity) (hCpos (j + 1) (by omega))
      (hCpos j hj) (hstep j hj).2.2)
  have hqm : q m = p m := by simp [hq, hr0]
  -- `ζ < ξ`
  have hq1lt : q (m + 1) + 1 ≤ p (m + 1) := by
    have h := (hstep m le_rfl).2.1
    rw [hqm] at h
    have : ((q (m + 1) : ℕ) : ℝ) < p (m + 1) := lt_of_le_of_lt h (hviol)
    exact_mod_cast this
  have hζξ : ζ < ξ := by
    have hU := hζU (m + 1) (by omega)
    have h2' : root (((q (m + 1) : ℕ) : ℝ) + 1) (C (m + 1)) ≤ root (ξ ^ C (m + 1)) (C (m + 1)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have : ((q (m + 1) + 1 : ℕ) : ℝ) ≤ p (m + 1) := by exact_mod_cast hq1lt
      push_cast at this
      exact le_trans this (Nat.floor_le (by positivity))
    have h3' : root (ξ ^ C (m + 1)) (C (m + 1)) = ξ :=
      Real.pow_rpow_inv_natCast hξ0.le (hCpos (m + 1) (by omega)).ne'
    linarith
  -- `ζ^(C m) ≥ p m`
  have hζm : (p m : ℝ) ≤ ζ ^ C m := by
    have := hζfl m le_rfl
    rw [hqm] at this
    rw [← this]; exact Nat.floor_le (by positivity)
  have hpm2 : (2 : ℝ) ≤ p m := by exact_mod_cast (hξS.2 m hm1).two_le
  have hζ1 : 1 < ζ := by
    by_contra h
    push_neg at h
    have : ζ ^ C m ≤ 1 := pow_le_one₀ hζ0.le h
    linarith
  -- closeness: `C m (ξ − ζ) < 1`
  have hclose : (C m : ℝ) * (ξ - ζ) < 1 := by
    have hge := pow_sub_pow_ge hζ0 hζξ.le (C m)
    have hlt : ξ ^ C m < (p m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpow1 : (1 : ℝ) ≤ ζ ^ (C m - 1) := one_le_pow₀ hζ1.le
    have hd : 0 ≤ ξ - ζ := by linarith
    have hCm0 : (0 : ℝ) ≤ C m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow1 (mul_nonneg hCm0 hd)]
  -- the floors of `ζ`
  have hfloor : ∀ k ≥ 1, ⌊ζ ^ C k⌋₊ = p k ∨ ⌊ζ ^ C k⌋₊ = q k ∧ m ≤ k := by
    intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · left
      rw [Nat.floor_eq_iff (by positivity)]
      refine ⟨?_, lt_of_lt_of_le (pow_lt_pow_left₀ hζξ hζ0.le (by have := hCge k hk; omega))
        (Nat.lt_floor_add_one _).le⟩
      have h1' : root (p k) (C k) ≤ root (p m) (C m) := hrec k hk hkm.le
      have h2' : root (p m) (C m) ≤ ζ := by
        have := Real.rpow_le_rpow (by positivity) hζm
          (inv_nonneg.2 (Nat.cast_nonneg (C m)))
        rwa [Real.pow_rpow_inv_natCast hζ0.le (hCpos m le_rfl).ne'] at this
      have h3' := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_trans h1' h2')
        (C k)
      rwa [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by have := hCge k hk; omega)]
        at h3'
    · right
      exact ⟨hζfl k hkm, hkm⟩
  have hζS : ζ ∈ millsSet C := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rcases hfloor k hk with h | ⟨h, hkm⟩
    · rw [h]; exact hξS.2 k hk
    · rw [h]; exact (hrX (k - m)).2
  exact absurd (hξ.2 hζS) (not_le.2 hζξ)


/-- Decay at large records: `|ξ^(C m) − round| ≤ 4 ξ^(−(151/400) C m)`. -/
theorem record_decay_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) {C : ℕ → ℕ} (h1 : 1 ≤ C 1)
    (h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1)) {K₀ : ℕ}
    (hEv : ∀ k ≥ K₀, ρ * C k ≤ C (k + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet C) ξ) :
    ∃ k₀, ∀ m ≥ k₀, IsRecord C ξ m →
      |ξ ^ C m - (round (ξ ^ C m) : ℝ)| ≤ 4 * ξ ^ (-(μ * C m)) := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  obtain ⟨k₀, hk₀⟩ := window_at_record_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1 h1 h2 hEv hξ
  have hξ1 : 1 < ξ := hξ.1.1
  have hξ0 : 0 < ξ := by linarith
  refine ⟨max k₀ (max K₀ 1), fun m hm hrec => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hCk : 0 < C m := C_ge_one h1 h2 m hm1
  have hc : ρ ≤ ratio C m := by
    have hCk' : (0 : ℝ) < C m := by exact_mod_cast hCk
    rw [ratio, le_div_iff₀ hCk']; exact hEv m (by omega)
  set x := ξ ^ C m with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
  have hxc : x ^ ratio C m < (⌊ξ ^ C (m + 1)⌋₊ : ℝ) + 1 := by
    rw [hx, pow_ratio hξ0 hCk]; exact Nat.lt_floor_add_one _
  have hw := fract_le_of_window (θ := θ) hx1 (by linarith) hθ0 hθ1 hxc
    (hk₀ m (by omega) hrec)
  set p : ℝ := (⌊x⌋₊ : ℝ) with hp
  have hp1 : 1 ≤ p := by have := Nat.floor_pos.2 hx1; rw [hp]; exact_mod_cast this
  have hA : p ^ μ ≤ p ^ ((1 - θ) * ratio C m - 1) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (theta_mu_le hθ1 hμ hc)
  have hA0 : 0 < p ^ μ := by positivity
  have hf : Int.fract x ≤ 2 * p ^ (-μ) := by
    calc Int.fract x ≤ 2 / (ratio C m * p ^ ((1 - θ) * ratio C m - 1)) := hw
      _ ≤ 2 / p ^ μ := by
          apply div_le_div_of_nonneg_left (by norm_num) hA0
          nlinarith
      _ = 2 * p ^ (-μ) := by
          rw [Real.rpow_neg (by linarith), div_eq_mul_inv]
  have hxfl : x ≤ 2 * p := by
    have := Nat.lt_floor_add_one x; rw [hp]; linarith
  have hround : |x - (round x : ℝ)| ≤ Int.fract x := by
    have := round_le x ⌊x⌋
    rwa [← Int.fract, abs_of_nonneg (Int.fract_nonneg x)] at this
  have hpow : p ^ (-μ) ≤ 2 * x ^ (-μ) := by
    have hxpos : 0 < x := by linarith
    have h1' : p ^ (-μ) ≤ (x / 2) ^ (-μ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h2' : (x / 2) ^ (-μ) = 2 ^ μ * x ^ (-μ) := by
      rw [Real.div_rpow hxpos.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    have h3' : (2 : ℝ) ^ μ ≤ 2 := by
      calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
        _ = 2 := Real.rpow_one 2
    rw [h2'] at h1'
    have : 0 ≤ x ^ (-μ) := by positivity
    nlinarith
  have hxe : x ^ (-μ) = ξ ^ (-(μ * C m)) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; ring_nf
  calc |x - (round x : ℝ)| ≤ Int.fract x := hround
    _ ≤ 2 * p ^ (-μ) := hf
    _ ≤ 2 * (2 * x ^ (-μ)) := by linarith
    _ = 4 * ξ ^ (-(μ * C m)) := by rw [hxe]; ring

/-- **Step 1 (records give a Pisot power).**  Decay at records (`window_at_record_theta` + Saito (5.17))
and Dubickas 2022 Lemma 6 along the records give `ξ^g` Pisot with `g ∣ C m` at large records. -/
theorem records_pisot_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) (hρ3 : ρ < 3)
    (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) (halg : IsAlgebraic ℚ ξ) :
    ∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g) ∧ 2 ≤ (minpoly ℚ (ξ ^ g)).natDegree ∧
      ∃ K, ∀ m ≥ K, IsRecord (shiftC j s) ξ m → g ∣ shiftC j s m := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  classical
  set C := shiftC j s with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  obtain ⟨K₀, hK₀⟩ := shiftC_ratio_ev (s := s) (j := j) hj1 hρ3
  have hξS := hξ.1
  have hξ1 : 1 < ξ := hξS.1
  have hnot := not_intCast_pow h1 h2 h5 hξS
  have hCge := C_ge_one h1 h2
  obtain ⟨k₀, hk₀⟩ := record_decay_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1 h1 h2 hK₀ hξ
  -- decay along any infinite family of large records gives a Pisot power dividing it
  have key : ∀ P : ℕ → Prop, (∃ᶠ m in atTop, P m) → (∀ m, P m → k₀ + 1 ≤ m ∧ IsRecord C ξ m) →
      ∃ g', 1 ≤ g' ∧ IsPisot (ξ ^ g') ∧ ∃ m, P m ∧ g' ∣ C m := by
    intro P hP hPr
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hP
    have hφ1 : ∀ n, 1 ≤ φ n := fun n => by have := (hPr _ (hφP n)).1; omega
    have hsm : StrictMono (fun n => C (φ n)) := fun a b hab =>
      C_strictMonoOn h1 h2 (hφ1 a) (hφ hab)
    obtain ⟨g', hg', hpis', hdiv', -⟩ := exists_pisot_of_decay_subseq' hD halg hξ1 hsm
      (hCge _ (hφ1 0)) hμ0 (by norm_num)
      (Eventually.of_forall fun n => hk₀ _ (by have := (hPr _ (hφP n)).1; omega)
        (hPr _ (hφP n)).2) (fun n t => hnot _ (hφ1 n) t)
    obtain ⟨n, hn⟩ := hdiv'.exists
    exact ⟨g', hg', hpis', φ n, hφP n, hn⟩
  have hfr : ∃ᶠ m in atTop, k₀ + 1 ≤ m ∧ IsRecord C ξ m :=
    (frequently_record h1 h2 hξ hnot).and_eventually (eventually_ge_atTop _) |>.mono
      fun m h => ⟨h.2, h.1⟩
  have hex : ∃ g, 1 ≤ g ∧ IsPisot (ξ ^ g) := by
    obtain ⟨g', hg', hp', -⟩ := key _ hfr (fun m h => h)
    exact ⟨g', hg', hp'⟩
  set g := Nat.find hex with hg
  obtain ⟨hg1, hpis⟩ := Nat.find_spec hex
  have hgmin : ∀ g' < g, ¬ (1 ≤ g' ∧ IsPisot (ξ ^ g')) := fun g' h => Nat.find_min hex h
  have hdiv : ∃ K, ∀ m ≥ K, IsRecord C ξ m → g ∣ C m := by
    by_contra hcon
    push_neg at hcon
    have hP : ∃ᶠ m in atTop, (k₀ + 1 ≤ m ∧ IsRecord C ξ m) ∧ ¬ g ∣ C m := by
      rw [frequently_atTop]
      intro a
      obtain ⟨m, hm, hr, hnd⟩ := hcon (max a (k₀ + 1))
      exact ⟨m, by omega, ⟨by omega, hr⟩, hnd⟩
    obtain ⟨g', hg', hp', m, ⟨⟨hmk, -⟩, hnd⟩, hgm⟩ := key _ hP (fun m h => h.1)
    have hgcd := isPisot_pow_gcd hξ1 (by omega) (by omega) hpis hp'
    have hle : Nat.gcd g g' ≤ g := Nat.gcd_le_left _ (by omega)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hgmin _ hlt ⟨Nat.gcd_pos_of_pos_left _ (by omega), hgcd⟩
    · exact hnd (dvd_trans (heq ▸ Nat.gcd_dvd_right g g') hgm)
  obtain ⟨K, hK⟩ := hdiv
  obtain ⟨m, hm⟩ := (hfr.and_eventually (eventually_ge_atTop K)).exists
  have hgm := hK m hm.2 hm.1.2
  refine ⟨g, hg1, hpis, ?_, K, hK⟩
  refine pisot_two_le_natDegree hpis fun t ht => ?_
  have h := (show (ξ ^ g) ^ (C m / g) = ξ ^ C m by rw [← pow_mul, Nat.mul_div_cancel' hgm])
  rw [ht] at h
  exact hnot m (by omega) (t ^ (C m / g)) (by rw [← h]; push_cast; ring)

/-- **Step 3 (degree `≤ 3`, no Baker).**  Decay `151/400` at records, records with bounded gaps,
and the orbit `n ↦ 3n − d` (Mignotte/Smyth: the dominant other conjugates are one real or one
complex pair; `a_r² → −1` along records is incompatible with `a_(r+t)² = a_r^(2·3^t) v^(3^t−1)`,
`v^(3^t−1) ≠ 1`). -/
theorem card_le_two_of_records_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) (hρ3 : ρ < 3)
    (hμ3 : 1 / 3 < μ)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) {g : ℕ} (hg1 : 1 ≤ g)
    (hpis : IsPisot (ξ ^ g)) (hdeg : 2 ≤ (minpoly ℚ (ξ ^ g)).natDegree)
    {K : ℕ} (hK : ∀ m ≥ K, IsRecord (shiftC j s) ξ m → g ∣ shiftC j s m)
    {T K' : ℕ} (hT : ∀ m ≥ K', ∃ r, m < r ∧ r ≤ m + T ∧ IsRecord (shiftC j s) ξ r) :
    Multiset.card (otherConj (ξ ^ g)) ≤ 2 := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  classical
  set C := shiftC j s with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  obtain ⟨K₀, hK₀⟩ := shiftC_ratio_ev (s := s) (j := j) hj1 hρ3
  have hξ1 : 1 < ξ := hξ.1.1
  have hξ0 : 0 < ξ := by linarith
  obtain ⟨k₀, hk₀⟩ := record_decay_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1 h1 h2 hK₀ hξ
  set n : ℕ → ℕ := fun m => C m / g with hn
  set K1 := K + K' + k₀ + 1 with hK1
  have hgn : ∀ m ≥ K1, IsRecord C ξ m → g * n m = C m := fun m hm hr =>
    Nat.mul_div_cancel' (hK m (by omega) hr)
  have hrel : ∀ k r, K1 ≤ k → IsRecord C ξ k → IsRecord C ξ r → k < r →
      (g : ℤ) * n r = 3 ^ (r - k) * (g * n k) - s * (3 ^ (r - k) - 1) := by
    intro k r hk hkr hrr hlt
    have a : ((g * n k : ℕ) : ℤ) = 3 ^ (k + j) + s := by
      rw [hgn k hk hkr]; exact shiftC_cast hj1 (by omega)
    have b : ((g * n r : ℕ) : ℤ) = 3 ^ (r + j) + s := by
      rw [hgn r (by omega) hrr]; exact shiftC_cast hj1 (by omega)
    push_cast at a b
    rw [b, a, show r + j = (r - k) + (k + j) by omega, pow_add]; ring
  have hnt : Tendsto n atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b * g + 1, fun m hm => ?_⟩
    have := le_C h1 h2 m (by omega)
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  obtain ⟨c, hc, hfr⟩ := DominantPair.lower_along_records hpis hdeg hnt
    (T := T) (K' := K1) (fun m hm => hT m (by omega)) hs hrel
  have hround := hnt.eventually (norm_conjPowSum_eq_round hpis)
  have hfr2 : ∃ᶠ m in atTop, c * conjMax (ξ ^ g) ^ n m ≤ ‖conjPowSum (ξ ^ g) (n m)‖ ∧
      ‖conjPowSum (ξ ^ g) (n m)‖ ≤ 4 * ((ξ ^ g) ^ (-(μ * n m)) : ℝ) := by
    refine ((hfr.and_eventually hround).and_eventually (eventually_ge_atTop K1)).mono ?_
    rintro m ⟨⟨⟨hrec, hlo⟩, hr⟩, hm⟩
    refine ⟨hlo, ?_⟩
    have hgm := hgn m hm hrec
    have hpow : (ξ ^ g) ^ n m = ξ ^ C m := by rw [← pow_mul, hgm]
    have hrp : ((ξ ^ g) ^ (-(μ * n m)) : ℝ) =
        ξ ^ (-(μ * C m)) := by
      rw [← Real.rpow_natCast ξ g, ← Real.rpow_mul hξ0.le, ← hgm]
      push_cast; ring_nf
    rw [hr, hpow, hrp]
    exact hk₀ m (by omega) hrec
  have hL := card_mul_le_of_lower hpis (by norm_num) hc (hnt.frequently hfr2)
  have : (Multiset.card (otherConj (ξ ^ g)) : ℝ) < 3 := by
    by_contra hc3
    push_neg at hc3
    nlinarith [mul_le_mul_of_nonneg_right hc3 hμ0.le]
  exact_mod_cast (show (Multiset.card (otherConj (ξ ^ g)) : ℝ) ≤ 2 by
    have h3 : (Multiset.card (otherConj (ξ ^ g))) < 3 := by exact_mod_cast this
    exact_mod_cast (show Multiset.card (otherConj (ξ ^ g)) ≤ 2 by omega))

/-- **All large indices are records** for the E+ exponents, if `ξ` is algebraic. -/
theorem eventually_record_shift_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) (hρ3 : ρ < 3)
    (hD : Dubickas2022)
    {s : ℤ} {j : ℕ} (hs : s ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + s) (hj2 : s ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast (millsSet (shiftC j s)) ξ) (halg : IsAlgebraic ℚ ξ)
    (hμ3 : 1 / 3 < μ ∨ ∀ g : ℕ, 1 ≤ g → IsPisot (ξ ^ g) → (minpoly ℚ (ξ ^ g)).natDegree ≤ 3) :
    ∃ K, ∀ m ≥ K, IsRecord (shiftC j s) ξ m := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  obtain ⟨g, hg1, hpis, hdeg, K, hK⟩ := records_pisot_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1 hρ3 hD hj1 hj2 hξ halg
  obtain ⟨T, K', hT⟩ := record_gap_bounded hj1 hj2 hξ hg1 hpis hK
  have hc2 : Multiset.card (otherConj (ξ ^ g)) ≤ 2 := by
    rcases hμ3 with hμ3 | hd3
    · exact card_le_two_of_records_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1 hρ3 hμ3 hs hj1 hj2 hξ hg1 hpis
        hdeg hK hT
    · have := card_otherConj_add_one hpis.2.1.tower_top
      have := hd3 g hg1 hpis
      omega
  exact eventually_record_of_card_le_two hs hj1 hj2 hξ hg1 hpis hc2 hK hT

/-- The degree bound for the E+ exponents: decay of `‖ξ^(C k)‖` at rate `151/400` along all
large `k`, with `ξ^g` Pisot and `g ∣ C k`, gives `(ℓ − 1)·151/400 ≤ 1` (no Baker). -/
theorem card_mul_le_shift_theta {μ : ℝ} {e : ℤ} {j : ℕ} (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + e) (he : e ≠ 0)
    {ξ : ℝ} (hξ1 : 1 < ξ) {g : ℕ} (hg1 : 1 ≤ g) (hpis : IsPisot (ξ ^ g))
    (hdeg2 : 2 ≤ (minpoly ℚ (ξ ^ g)).natDegree) {sq : ℕ → ℕ} {k₃ : ℕ} (hk₃ : 1 ≤ k₃)
    (hsq : ∀ k, sq k = shiftC j e (k + k₃)) {k₄ : ℕ} (hk₄ : ∀ k ≥ k₄, g ∣ sq k)
    (hdecay : ∀ᶠ k in atTop, |ξ ^ sq k - (round (ξ ^ sq k) : ℝ)| ≤
      4 * ξ ^ (-(μ * sq k))) :
    ((Multiset.card (otherConj (ξ ^ g)) : ℝ)) * μ ≤ 1 := by
  have hξ0 : 0 < ξ := by linarith
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set n : ℕ → ℕ := fun k => sq (k + k₄) / g with hn
  have hgn : ∀ k, g * n k = sq (k + k₄) := fun k => Nat.mul_div_cancel' (hk₄ _ (by omega))
  have hcast : ∀ k, ((g : ℤ) * n k) = 3 ^ (k + k₄ + k₃ + j) + e := by
    intro k
    have := hgn k
    rw [hsq] at this
    have h := shiftC_cast hj1 (k := k + k₄ + k₃) (by omega)
    rw [← h]; exact_mod_cast this
  have hstep : ∀ k, (g : ℤ) * (3 * n k - n (k + 1)) = 2 * e := by
    intro k
    have a := hcast k
    have b := hcast (k + 1)
    rw [show k + 1 + k₄ + k₃ + j = (k + k₄ + k₃ + j) + 1 by ring, pow_succ] at b
    linear_combination 3 * a - b
  set d : ℤ := 3 * n 0 - n 1 with hd
  have hrec : ∀ k, (n (k + 1) : ℤ) = 3 * n k - d := by
    intro k
    have h := hstep k
    rw [← hstep 0] at h
    have := mul_left_cancel₀ hg0 h
    linarith
  have hd0 : d ≠ 0 := by
    intro h0
    have := hstep 0
    rw [← hd, h0, mul_zero] at this
    exact he (by linarith)
  have hnt : Tendsto n atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b * g, fun a ha => ?_⟩
    have h1 := hcast a
    have h3 : (a : ℤ) + 1 ≤ 3 ^ (a + k₄ + k₃ + j) + e := by
      have hp : (3 : ℤ) ^ (a + k₄ + k₃ + j) = 3 ^ (j + 1) * 3 ^ (a + k₄ + k₃ - 1) := by
        rw [← pow_add]; congr 1; omega
      have hq : (a : ℤ) + 1 ≤ 3 ^ (a + k₄ + k₃ - 1) := by
        have : a + 1 ≤ 3 ^ (a + k₄ + k₃ - 1) := by
          calc a + 1 ≤ 3 ^ a := Nat.lt_pow_self (by norm_num)
            _ ≤ 3 ^ (a + k₄ + k₃ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast this
      have h31 : (1 : ℤ) ≤ 3 ^ (j + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have : (b : ℤ) * g < (g : ℤ) * n a + 1 := by
      have : (b * g : ℕ) ≤ a := ha
      push_cast at this
      linarith
    have hgpos : (0 : ℤ) < g := by exact_mod_cast (show 0 < g by omega)
    have : (b : ℤ) ≤ n a := by
      by_contra hlt
      push_neg at hlt
      have : (n a : ℤ) + 1 ≤ b := hlt
      nlinarith
    exact_mod_cast this
  have hdec : ∀ᶠ k in atTop, ‖conjPowSum (ξ ^ g) (n k)‖ ≤
      4 * ((ξ ^ g) ^ (-(μ * n k)) : ℝ) := by
    have h1 := hnt.eventually (norm_conjPowSum_eq_round hpis)
    have h2 := (tendsto_add_atTop_nat k₄).eventually hdecay
    filter_upwards [h1, h2] with k hk1 hk2
    have hpow : (ξ ^ g) ^ n k = ξ ^ sq (k + k₄) := by rw [← pow_mul, hgn]
    have hrp : ((ξ ^ g) ^ (-(μ * n k)) : ℝ) =
        ξ ^ (-(μ * sq (k + k₄))) := by
      rw [← Real.rpow_natCast ξ g, ← Real.rpow_mul hξ0.le, ← hgn]
      push_cast; ring_nf
    rw [hk1, hpow, hrp]
    exact hk2
  exact card_mul_le_of_orbit hpis hdeg2 hnt hd0 hrec (by norm_num) hdec

/-- **Saito's Type B for the E+ exponents, from BHP and Dubickas 2022 Lemma 6 only.** -/
theorem saitoTypeB_shift_theta {θ ρ μ : ℝ} (hP : PrimesShortInterval θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hμ0 : 0 < μ) (hμ : μ ≤ (1 - θ) * ρ - 1) (hρ2 : 2 < ρ) (hμ1 : μ ≤ 1) (hρ3 : ρ < 3)
    (hD : Dubickas2022)
    {e : ℤ} {j : ℕ} (he : e ≠ 0) (hj1 : 1 ≤ (3 : ℤ) ^ (j + 1) + e) (hj2 : e ≤ (3 : ℤ) ^ (j + 1))
    {ξ : ℝ} (hξ : IsLeast {A : ℝ | 1 < A ∧ ∀ k ≥ 1, (⌊A ^ shiftC j e k⌋₊).Prime} ξ)
    (hμ3 : 1 / 3 < μ ∨ (IsAlgebraic ℚ ξ →
      ∀ g : ℕ, 1 ≤ g → IsPisot (ξ ^ g) → (minpoly ℚ (ξ ^ g)).natDegree ≤ 3)) :
    Transcendental ℚ ξ ∨
      ∃ g : ℕ, 1 ≤ g ∧ IsPisot (ξ ^ g) ∧ (minpoly ℚ (ξ ^ g)).natDegree = 3 ∧
        ∃ K : ℕ, ∀ k ≥ K, (29 : ℝ) / 10 * shiftC j e k ≤ shiftC j e (k + 1) →
          g ∣ shiftC j e k ∧ powTrace (ξ ^ g) (shiftC j e k / g) = (⌊ξ ^ shiftC j e k⌋₊ : ℂ) := by
  have hρ1 := theta_one_lt hθ0 hθ1 hμ0 hμ
  by_cases htr : Transcendental ℚ ξ
  · exact Or.inl htr
  right
  have halg : IsAlgebraic ℚ ξ := not_not.1 htr
  set C := shiftC j e with hCdef
  have h1 : 1 ≤ C 1 := shiftC_pos hj1 le_rfl
  have h2 : ∀ k ≥ 1, 2 * C k ≤ C (k + 1) := fun k hk => shiftC_two_mul_le hj1 hj2 hk
  have h5 : ∀ m ≥ 1, ∃ k > m, C m ∣ C k ∧ (29 : ℝ) / 10 * C k ≤ C (k + 1) :=
    fun m hm => shiftC_B5 hj1 hj2 hm
  set K₀ := 19 * e.natAbs + 1 with hK₀def
  have hK₀ : ∀ k ≥ K₀, (29 : ℝ) / 10 * C k ≤ C (k + 1) := fun k hk =>
    shiftC_ratio hj1 (by omega) (by omega)
  obtain ⟨K₀ρ, hK₀ρ⟩ := shiftC_ratio_ev (s := e) (j := j) hj1 hρ3
  have hξS : ξ ∈ millsSet C := hξ.1
  have hξ1 : 1 < ξ := hξ.1.1
  have hξ0 : 0 < ξ := by linarith
  have hnot := not_intCast_pow h1 h2 h5 hξS
  obtain ⟨Kr, hKr⟩ := eventually_record_shift_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1 hρ3 hD he hj1 hj2 hξ halg (hμ3.imp_right (· halg))
  have hlow : ∀ k ≥ Kr + 1, root ⌊ξ ^ C k⌋₊ (C k) ≤ root ⌊ξ ^ C (k + 1)⌋₊ (C (k + 1)) :=
    fun k hk => hKr (k + 1) (by omega) k (by omega) (by omega)
  obtain ⟨k₀, hII⟩ := window_of_least_theta hP hθ0 hθ1 hμ0 hμ hρ2 hμ1 h1 h2 hK₀ρ hξ hnot hlow
  obtain ⟨k₂, hfr⟩ := eventually_fract_le_theta hθ0 hθ1 hμ0 hμ hρ2 hμ1 h1 h2 hK₀ρ hξS hII
  have hCge := C_ge_one h1 h2
  -- the decay along `s k = C (k + k₃)`
  set k₃ := k₂ + 1 with hk₃
  set s : ℕ → ℕ := fun k => C (k + k₃) with hs
  have hsmono : StrictMono s := by
    intro a b hab
    exact C_strictMonoOn h1 h2 (by omega) (by omega)
  have hs0 : 0 < s 0 := hCge _ (by omega)
  have hflo := floor_tendsto h1 h2 hξ1
  have hdecay : ∀ᶠ k in atTop, |ξ ^ s k - (round (ξ ^ s k) : ℝ)| ≤
      4 * ξ ^ (-(μ * s k)) := by
    filter_upwards [eventually_ge_atTop 0] with k _
    set x := ξ ^ s k with hx
    have hx1 : 1 ≤ x := one_le_pow₀ hξ1.le
    have hfl1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      have := Nat.floor_pos.2 hx1; exact_mod_cast this
    have hxfl : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one x; linarith
    have hround : |x - (round x : ℝ)| ≤ Int.fract x := by
      have := round_le x ⌊x⌋
      rwa [← Int.fract, abs_of_nonneg (Int.fract_nonneg x)] at this
    have hf := hfr (k + k₃) (by omega)
    -- `⌊x⌋^(−t) ≤ 2^t x^(−t) ≤ 2 x^(−t)`
    have hpow : (⌊x⌋₊ : ℝ) ^ (-μ) ≤ 2 * x ^ (-μ) := by
      have hxpos : 0 < x := by linarith
      have h1' : (⌊x⌋₊ : ℝ) ^ (-μ) ≤ (x / 2) ^ (-μ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have h2' : (x / 2) ^ (-μ) = 2 ^ μ * x ^ (-μ) := by
        rw [Real.div_rpow hxpos.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        field_simp
      have h3' : (2 : ℝ) ^ μ ≤ 2 := by
        calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
          _ = 2 := Real.rpow_one 2
      rw [h2'] at h1'
      have : 0 ≤ x ^ (-μ) := by positivity
      nlinarith
    have hxe : x ^ (-μ) = ξ ^ (-(μ * s k)) := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; ring_nf
    calc |x - (round x : ℝ)| ≤ Int.fract x := hround
      _ ≤ 2 * (⌊x⌋₊ : ℝ) ^ (-μ) := hf
      _ ≤ 2 * (2 * x ^ (-μ)) := by linarith
      _ = 4 * ξ ^ (-(μ * s k)) := by rw [hxe]; ring
  have hnot' : ∀ k, ∀ t : ℤ, ξ ^ s k ≠ (t : ℝ) := fun k t => hnot _ (by omega) t
  obtain ⟨g, hg1, hpis, hgdiv, hdeg2⟩ :=
    exists_pisot_of_decay_subseq' hD halg hξ1 hsmono hs0 hμ0 (by norm_num)
      hdecay hnot'
  obtain ⟨k₄, hk₄⟩ := eventually_atTop.1 hgdiv
  have hcard : ((Multiset.card (otherConj (ξ ^ g)) : ℝ)) * μ ≤ 1 :=
    card_mul_le_shift_theta hj1 he hξ1 hg1 hpis hdeg2 (k₃ := k₃) (by omega) (fun k => rfl) hk₄ hdecay
  -- `g ∣ C k` for `k ≥ k₅`
  set k₅ := k₄ + k₃ with hk₅
  have hgC : ∀ k ≥ k₅, g ∣ C k := by
    intro k hk
    have := hk₄ (k - k₃) (by omega)
    simpa [hs, show k - k₃ + k₃ = k by omega] using this
  have hpowg : ∀ k ≥ k₅, (ξ ^ g) ^ (C k / g) = ξ ^ C k := by
    intro k hk
    rw [← pow_mul, Nat.mul_div_cancel' (hgC k hk)]
  -- eventually the fractional part is `< 1/2`
  obtain ⟨k₆, hk₆⟩ := eventually_atTop.1
    (hflo.eventually_ge_atTop ((16 : ℝ) ^ μ⁻¹))
  have hhalf : ∀ k ≥ max k₆ k₂, Int.fract (ξ ^ C k) < 1 / 2 := by
    intro k hk
    have hf := hfr k (le_trans (le_max_right _ _) hk)
    have hbig := hk₆ k (le_trans (le_max_left _ _) hk)
    have hpos : (0 : ℝ) < (16 : ℝ) ^ μ⁻¹ := by positivity
    have : (⌊ξ ^ C k⌋₊ : ℝ) ^ (-μ) ≤ 1 / 16 := by
      calc (⌊ξ ^ C k⌋₊ : ℝ) ^ (-μ)
          ≤ ((16 : ℝ) ^ μ⁻¹) ^ (-μ) :=
            Real.rpow_le_rpow_of_nonpos hpos hbig (by linarith)
        _ = 1 / 16 := by
            rw [← Real.rpow_mul (by norm_num), show μ⁻¹ * -μ = -1 by field_simp]
            norm_num
    linarith
  -- the degree is `3`
  have hβ := hpis
  have hcardle : Multiset.card (otherConj (ξ ^ g)) ≤ 2 := by
    rcases hμ3 with hμ3 | hd3
    swap
    · have := card_otherConj_add_one hpis.2.1.tower_top
      have := hd3 halg g hg1 hpis
      omega
    by_contra hc
    push_neg at hc
    have : (3 : ℝ) ≤ (Multiset.card (otherConj (ξ ^ g)) : ℝ) := by exact_mod_cast hc
    nlinarith [mul_le_mul_of_nonneg_right this hμ0.le]
  have hcard1 := card_otherConj_add_one (hpis.2.1.tower_top)
  have hdeg3 : (minpoly ℚ (ξ ^ g)).natDegree = 3 := by
    rcases (show (minpoly ℚ (ξ ^ g)).natDegree = 2 ∨ (minpoly ℚ (ξ ^ g)).natDegree = 3 by
      omega) with h | h
    · exfalso
      refine not_natDegree_two hpis h (n := fun k => C k / g) (K := max (max k₅ k₆) (k₂ + 1))
        ?_ ?_ ?_ ?_
      · intro k hk
        show (⌊(ξ ^ g) ^ (C k / g)⌋₊).Prime
        rw [hpowg k (by omega)]
        exact hξS.2 k (by omega)
      · intro k hk
        show Int.fract ((ξ ^ g) ^ (C k / g)) < 1 / 2
        rw [hpowg k (by omega)]
        exact hhalf k (by omega)
      · intro M
        obtain ⟨b, hb, hdvd, -⟩ := h5 (M + k₅ + 1) (by omega)
        refine ⟨M + k₅ + 1, by omega, b, hb, ?_, ?_⟩
        · obtain ⟨e, he⟩ := hdvd
          refine ⟨e, ?_⟩
          have hg := hgC (M + k₅ + 1) (by omega)
          obtain ⟨u, hu⟩ := hg
          rw [he, hu, Nat.mul_div_cancel_left _ (by omega), mul_assoc,
            Nat.mul_div_cancel_left _ (by omega)]
        · have hlt := C_strictMonoOn h1 h2 (a := M + k₅ + 1) (b := b) (by omega) hb
          obtain ⟨u, hu⟩ := hgC (M + k₅ + 1) (by omega)
          obtain ⟨v, hv⟩ := hgC b (by omega)
          rw [hu, hv] at hlt ⊢
          rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
          exact Nat.lt_of_mul_lt_mul_left hlt
      · -- `C k / g → ∞`
        rw [tendsto_atTop_atTop]
        intro b
        refine ⟨max k₅ (b * g + 1), fun a ha => ?_⟩
        have hCa : a ≤ C a := le_C h1 h2 a (by omega)
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
    · exact h
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (powTrace_eq_floor hpis)
  refine ⟨g, hg1, hpis, hdeg3, max (max k₅ k₆) (max k₂ (N₀ * g + 1)), fun k hk _ => ⟨hgC k
    (by omega), ?_⟩⟩
  have hN : N₀ ≤ C k / g := by
    have := le_C h1 h2 k (by omega)
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have := hN₀ (C k / g) hN (by rw [hpowg k (by omega)]; exact hhalf k (by omega))
  rw [this, hpowg k (by omega)]



end LeanFormalizations.Mills.SaitoTypeB

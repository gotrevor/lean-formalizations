/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.FLUpper
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.FLLower
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.BuchstabBin

/-!
# The lower half of the fundamental lemma (phase E5, step 3(d); session B)

Buchstab from `w = 2`: `N ≤ S⁻(N, z) + Σ_{p<z} S⁺(N/p+1, p)`.  Each `S⁺(M_p, p)` is bounded by
`siftMax_le_fl`: `S⁺(M, w) ≤ M V(w)(1 + 2θ) + 2(C M^{1/3} log M)²`, `θ = e^K e^{−2 log M/log w}`.
The main terms telescope (`sum_Vw_div`).  With `u = log N / log p ≥ s` the Rankin error is
`L V(p) θ_p / p ≤ A e^{K+2} u e^{−2u} / p ≤ A e^{K+2} e^{−s} (log p / L) / p`, and
`Σ_{p<z} log p / p ≤ log z + B` (Mertens' first theorem) — no dyadic decomposition.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open Filter Topology Finset

lemma mertensP_eq_div_Vw (M w : ℕ) : (M : ℝ) / mertensP (w - 1) = M * Vw w := by
  rw [mertensP_eq_inv, div_inv_eq_mul]; rfl

/-- **Uniform upper fundamental lemma, additive form**: for `M ≥ M₀`, `w ≥ 2` and
`θ = e^K e^{−2 log M/log w} ≤ 1/2`, `S⁺(M, w) ≤ M V(w)(1 + 2θ) + 2(C M^{1/3} log M)²`. -/
theorem siftMax_le_fl : ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M w : ℕ, 2 ≤ w → M₀ ≤ M →
    Real.exp rankK * Real.exp (-(2 * Real.log M / Real.log w)) ≤ 1 / 2 →
    (siftMax M w : ℝ) ≤ M * Vw w * (1 + 2 * (Real.exp rankK *
      Real.exp (-(2 * Real.log M / Real.log w)))) +
      2 * ((M : ℝ) ^ (1 / 3 : ℝ) * (C * Real.log M)) ^ 2 := by
  obtain ⟨C, hC, ξ₀, hξ₀⟩ := mertensP_le_log
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hξ : ∀ᶠ N : ℕ in atTop, ξ₀ ≤ ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ :=
    (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp hN)).eventually_ge_atTop ξ₀
  have h12 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 12 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).comp hN).eventually_ge_atTop 2
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hξ.and h12).and (eventually_ge_atTop 2))
  refine ⟨C, hC, M₀, fun N w hw hNM hθ => ?_⟩
  obtain ⟨⟨hξN, h12⟩, hN2⟩ := hM₀ N hNM
  set ξ := ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊
  set L := Real.log N
  set θ := Real.exp rankK * Real.exp (-(2 * L / Real.log w)) with hθdef
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < L := Real.log_pos hN1
  set t := (N : ℝ) ^ (1 / 3 : ℝ)
  set q := (N : ℝ) ^ (1 / 4 : ℝ)
  have htq : t = (N : ℝ) ^ (1 / 12 : ℝ) * q := by
    show (N : ℝ) ^ (1 / 3 : ℝ) = _
    rw [← Real.rpow_add hNpos]; norm_num
  have hq1 : 1 ≤ q := Real.one_le_rpow hN1.le (by norm_num)
  have ht2 : 2 ≤ t := by nlinarith
  have htpos : 0 < t := by linarith
  have hξlow : t / 2 ≤ ξ := by have := Nat.sub_one_lt_floor t; linarith
  have hξ1 : 1 ≤ ξ := by
    have : (1 : ℝ) ≤ ξ := by linarith
    exact_mod_cast this
  have hξpos : (0 : ℝ) < ξ := by exact_mod_cast hξ1
  have hξq : q ≤ ξ := by nlinarith
  have hlogξ : L / 4 ≤ Real.log ξ := by
    have h := Real.log_le_log (by linarith) hξq
    rw [Real.log_rpow hNpos] at h; linarith
  have hξt : (ξ : ℝ) ≤ t := Nat.floor_le htpos.le
  have hlogξL : Real.log ξ ≤ L := by
    have h := Real.log_le_log hξpos hξt
    rw [Real.log_rpow hNpos] at h; linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hηN : Real.exp rankK * (ξ : ℝ) ^ (-(8 / Real.log w)) ≤ θ := by
    rw [hθdef]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    rw [Real.rpow_def_of_pos hξpos, Real.exp_le_exp, mul_neg, neg_le_neg_iff, ← mul_div_assoc,
      div_le_div_iff_of_pos_right hlogw]
    linarith
  have hU := siftMax_mul_le N (w := w) (ξ := ξ) hw hξ1
  have hS0 : (0 : ℝ) ≤ siftMax N w := Nat.cast_nonneg _
  have hθ0 : 0 ≤ θ := by positivity
  have hSD : (siftMax N w : ℝ) * (1 - θ) ≤ N * Vw w + selE w ξ ^ 2 := by
    rw [← mertensP_eq_div_Vw]
    refine le_trans ?_ hU
    exact mul_le_mul_of_nonneg_left (by linarith) hS0
  have hE : selE w ξ ≤ t * (C * L) := by
    calc selE w ξ ≤ ξ * mertensP ξ := selE_le w ξ
      _ ≤ t * (C * L) := by
        apply mul_le_mul hξt _ (mertensP_pos _).le htpos.le
        exact (hξ₀ ξ hξN).trans (mul_le_mul_of_nonneg_left hlogξL hC.le)
  have hE2 : selE w ξ ^ 2 ≤ (t * (C * L)) ^ 2 := pow_le_pow_left₀ (selE_nonneg _ _) hE 2
  have hV : 0 ≤ Vw w := (LeanFormalizations.Mertens.primeProd_pos _).le
  have hX : 0 ≤ (N : ℝ) * Vw w := mul_nonneg hNpos.le hV
  -- `S ≤ (X + E²)/(1 − θ) ≤ (X + E²)(1 + 2θ)`
  have h1 : (1 : ℝ) ≤ (1 - θ) * (1 + 2 * θ) := by nlinarith
  have hE20 := sq_nonneg (t * (C * L))
  nlinarith [mul_le_mul_of_nonneg_right hSD (show 0 ≤ 1 + 2 * θ by linarith)]

/-- `V(p) ≤ A / log p` for every `p ≥ 2`. -/
theorem Vw_le_div_log : ∃ A : ℝ, 0 < A ∧ ∀ p : ℕ, 2 ≤ p → Vw p ≤ A / Real.log p := by
  obtain ⟨A₁, A₂, hA₂, hA⟩ := primeProd_log_bounds
  refine ⟨max (2 * A₁) 1, by positivity, fun p hp => ?_⟩
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  rw [le_div_iff₀ hlogp]
  rcases eq_or_lt_of_le hp with h | h
  · subst h
    rw [Vw_two, one_mul, Nat.cast_ofNat]
    have : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith [le_max_right (2 * A₁) 1]
  · have hp1 : 2 ≤ p - 1 := by omega
    obtain ⟨-, hup⟩ := hA (p - 1) hp1
    have hpos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p - 1 by omega)
    have hlog2 : Real.log p ≤ 2 * Real.log ((p - 1 : ℕ) : ℝ) := by
      rw [← Real.log_rpow hpos]
      apply Real.log_le_log (by positivity)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have : (p : ℝ) = ((p - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have h3 : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp1
      rw [this]; nlinarith
    have hV0 : 0 ≤ Vw p := (LeanFormalizations.Mertens.primeProd_pos _).le
    have : Vw p * Real.log p ≤ 2 * A₁ := by
      have := mul_le_mul_of_nonneg_left hlog2 hV0
      unfold Vw at *; nlinarith
    exact this.trans (le_max_left _ _)

/-- `u e^{−2u} ≤ 4 e^{−s} / u` for `u ≥ s > 0`. -/
lemma mul_exp_neg_two_le {u s : ℝ} (hs : 0 < s) (hu : s ≤ u) :
    u * Real.exp (-2 * u) ≤ 4 * Real.exp (-s) / u := by
  have hu0 : 0 < u := by linarith
  rw [le_div_iff₀ hu0]
  have h1 := Real.add_one_le_exp (u / 2)
  have h2 : u ^ 2 ≤ 4 * Real.exp u := by
    have : Real.exp (u / 2) ^ 2 = Real.exp u := by rw [← Real.exp_nat_mul]; ring_nf
    nlinarith [Real.exp_pos (u / 2)]
  have h3 : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by rw [← Real.exp_add]; ring_nf
  have h4 : Real.exp (-u) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have he := Real.exp_pos (-2 * u)
  nlinarith [mul_le_mul_of_nonneg_right h2 he.le]

/-- **The Rankin error sum**: `Σ_{p<z} L (V(p)/p) e^{−2L/log p} ≤ 4A e^{−s}(log z + B)/L`
when `log z ≤ L/s`. -/
theorem rankin_error_sum {A : ℝ} (hA : ∀ p : ℕ, 2 ≤ p → Vw p ≤ A / Real.log p)
    {s L : ℝ} (hs : 0 < s) (hL : 0 < L) {z : ℕ} (hz : 2 ≤ z) (hzL : Real.log z ≤ L / s) :
    ∑ p ∈ (Ico 2 z).filter Nat.Prime, L * (Vw p / p) * Real.exp (-2 * (L / Real.log p)) ≤
      4 * A * Real.exp (-s) * (Real.log z + mertB) / L := by
  have hterm : ∀ p ∈ (Ico 2 z).filter Nat.Prime,
      L * (Vw p / p) * Real.exp (-2 * (L / Real.log p)) ≤
        4 * A * Real.exp (-s) / L * (Real.log p / p) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    obtain ⟨hp2, hpz⟩ := mem_Ico.mp hpI
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : 0 < Real.log p := Real.log_pos hp1
    have hlogpz : Real.log p ≤ Real.log z :=
      Real.log_le_log hp0 (by exact_mod_cast hpz.le)
    have hu : s ≤ L / Real.log p := by
      rw [le_div_iff₀ hlogp]; rw [le_div_iff₀ hs] at hzL; nlinarith
    have hk := mul_exp_neg_two_le hs hu
    have hV := hA p hp2
    have hV0 : 0 ≤ Vw p := (LeanFormalizations.Mertens.primeProd_pos _).le
    have hA0 : 0 ≤ A := by
      have := div_nonneg hV0 hlogp.le
      have h := hV.trans' hV0
      rwa [le_div_iff₀ hlogp, zero_mul] at h
    set u := L / Real.log p with hudef
    have hLu : L = u * Real.log p := by rw [hudef]; field_simp
    have he := Real.exp_pos (-2 * u)
    calc L * (Vw p / p) * Real.exp (-2 * u)
        ≤ L * (A / Real.log p / p) * Real.exp (-2 * u) := by gcongr
      _ = A / p * (u * Real.exp (-2 * u)) := by rw [hLu]; field_simp
      _ ≤ A / p * (4 * Real.exp (-s) / u) := by gcongr
      _ = 4 * A * Real.exp (-s) / L * (Real.log p / p) := by
          rw [hLu]; field_simp
  have hsub : (Ico 2 z).filter Nat.Prime ⊆ (range z).filter Nat.Prime := by
    intro p hp; simp only [mem_filter, mem_Ico, mem_range] at hp ⊢; exact ⟨hp.1.2, hp.2⟩
  have hc : 0 ≤ 4 * A * Real.exp (-s) / L := by
    have hA0 : 0 ≤ A := by
      have h := hA 2 le_rfl
      rw [Vw_two, Nat.cast_ofNat, le_div_iff₀ (Real.log_pos (by norm_num)), one_mul] at h
      linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
    positivity
  calc _ ≤ ∑ p ∈ (Ico 2 z).filter Nat.Prime, 4 * A * Real.exp (-s) / L * (Real.log p / p) :=
        sum_le_sum hterm
    _ = 4 * A * Real.exp (-s) / L * ∑ p ∈ (Ico 2 z).filter Nat.Prime, Real.log p / p := by
        rw [mul_sum]
    _ ≤ 4 * A * Real.exp (-s) / L * ∑ p ∈ (range z).filter Nat.Prime, Real.log p / p := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_) hc
        have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
        exact div_nonneg (Real.log_nonneg this.le) (by linarith)
    _ ≤ 4 * A * Real.exp (-s) / L * (Real.log z + mertB) :=
        mul_le_mul_of_nonneg_left (sum_log_div_le hz) hc
    _ = _ := by ring

lemma siftMin_two (N : ℕ) : siftMin N 2 = N := by
  obtain ⟨lo, r, hr⟩ := exists_sift_eq_siftMin N 2
  rw [← hr, sift_two]

lemma Vw_le_one (w : ℕ) : Vw w ≤ 1 := by
  unfold Vw LeanFormalizations.Mertens.primeProd
  refine prod_le_one (fun p hp => (LeanFormalizations.Mertens.one_sub_inv_pos_of_prime
    (mem_filter.mp hp).2).le) fun p hp => ?_
  have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  linarith

/-- The uniform upper bound, as a property of `(C, M₀)`. -/
def UpperFL (C : ℝ) (M₀ : ℕ) : Prop := ∀ M w : ℕ, 2 ≤ w → M₀ ≤ M →
    Real.exp rankK * Real.exp (-(2 * Real.log M / Real.log w)) ≤ 1 / 2 →
    (siftMax M w : ℝ) ≤ M * Vw w * (1 + 2 * (Real.exp rankK *
      Real.exp (-(2 * Real.log M / Real.log w)))) +
      2 * ((M : ℝ) ^ (1 / 3 : ℝ) * (C * Real.log M)) ^ 2

/-- **The finite lower bound**: Buchstab from `2` with `siftMax_le_fl` on every term. -/
theorem siftMin_ge_finite {C A : ℝ} {M₀ : ℕ} (hC0 : 0 ≤ C) (hfl : UpperFL C M₀)
    (hA : ∀ p : ℕ, 2 ≤ p → Vw p ≤ A / Real.log p) {s : ℝ} (hs : 1 ≤ s)
    (hsK : Real.exp rankK * Real.exp (2 - 2 * s) ≤ 1 / 2) {N z : ℕ} (hN2 : 2 ≤ N) (hz : 2 ≤ z)
    (hzN : Real.log z ≤ Real.log N / s) (hM : (M₀ : ℝ) ≤ N / z) :
    (N : ℝ) * Vw z - 8 * A * Real.exp (rankK + 2) * Real.exp (-s) * (Real.log z + mertB) * N /
        Real.log N ^ 2 - 2 * z - 2 * z * ((N : ℝ) ^ (1 / 3 : ℝ) * (C * Real.log N)) ^ 2 ≤
      siftMin N z := by
  set L := Real.log N with hLdef
  set P := (Ico 2 z).filter Nat.Prime
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < L := Real.log_pos hN1
  have hs0 : 0 < s := by linarith
  set κ := Real.exp (rankK + 2)
  have hκ : 0 < κ := Real.exp_pos _
  set Er := 2 * ((N : ℝ) ^ (1 / 3 : ℝ) * (C * L)) ^ 2
  have hEr : 0 ≤ Er := by positivity
  -- per-prime bound
  have hper : ∀ p ∈ P, (siftMax (N / p + 1) p : ℝ) ≤
      N / p * Vw p + 2 * κ * (N / L) * (L * (Vw p / p) * Real.exp (-2 * (L / Real.log p))) +
        2 + Er := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    obtain ⟨hp2, hpz⟩ := mem_Ico.mp hpI
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : 0 < Real.log p := Real.log_pos hp1
    set M := N / p + 1
    have hMr : (N : ℝ) / p ≤ M := by
      have := real_div_le_nat_div_add_one N p hpp.pos; push_cast [M]; linarith
    have hMr' : (M : ℝ) ≤ N / p + 1 := by
      have : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
      push_cast [M]; linarith
    have hMN : M ≤ N := by
      have : N / p < N := Nat.div_lt_self (by omega) hpp.one_lt
      omega
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.succ_pos (N / p)
    have hzr : (p : ℝ) ≤ z := by exact_mod_cast hpz.le
    have hM0 : M₀ ≤ M := by
      have : (M₀ : ℝ) ≤ M := by
        refine hM.trans (le_trans ?_ hMr)
        exact div_le_div_of_nonneg_left hNpos.le hp0 hzr
      exact_mod_cast this
    have hlogM : L - Real.log p ≤ Real.log M := by
      have := Real.log_le_log (by positivity) hMr
      rwa [Real.log_div hNpos.ne' hp0.ne'] at this
    have hlogpz : Real.log p ≤ Real.log z := Real.log_le_log hp0 hzr
    have hu : s ≤ L / Real.log p := by
      rw [le_div_iff₀ hlogp]; rw [le_div_iff₀ hs0] at hzN; nlinarith
    set θ := Real.exp rankK * Real.exp (-(2 * Real.log M / Real.log p)) with hθdef
    have hcore : 2 * (L / Real.log p) - 2 ≤ 2 * Real.log M / Real.log p := by
      have : 2 * (L - Real.log p) / Real.log p ≤ 2 * Real.log M / Real.log p :=
        div_le_div_of_nonneg_right (by linarith) hlogp.le
      have h2 : 2 * (L - Real.log p) / Real.log p = 2 * (L / Real.log p) - 2 := by
        field_simp
      linarith
    have e1 : θ = Real.exp (rankK + -(2 * Real.log M / Real.log p)) := by
      rw [hθdef, Real.exp_add]
    have hθκ : θ ≤ κ * Real.exp (-2 * (L / Real.log p)) := by
      rw [e1, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hθhalf : θ ≤ 1 / 2 := by
      refine le_trans ?_ hsK
      rw [e1, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hθ0 : 0 ≤ θ := by positivity
    have h := hfl M p hp2 hM0 hθhalf
    have hV0 : 0 ≤ Vw p := (LeanFormalizations.Mertens.primeProd_pos _).le
    have hV1 := Vw_le_one p
    have hlogML : Real.log M ≤ L := Real.log_le_log hMpos (by exact_mod_cast hMN)
    have hlogM0 : 0 ≤ Real.log M := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast Nat.le_add_left 1 (N / p)
      exact Real.log_nonneg this
    have hcube : (M : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow hMpos.le (by exact_mod_cast hMN) (by norm_num)
    have hE : 2 * ((M : ℝ) ^ (1 / 3 : ℝ) * (C * Real.log M)) ^ 2 ≤ Er := by
      have h1 : 0 ≤ (M : ℝ) ^ (1 / 3 : ℝ) * (C * Real.log M) := by positivity
      have h2 : (M : ℝ) ^ (1 / 3 : ℝ) * (C * Real.log M) ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (C * L) :=
        mul_le_mul hcube (mul_le_mul_of_nonneg_left hlogML hC0) (by positivity) (by positivity)
      have := pow_le_pow_left₀ h1 h2 2
      linarith
    have hmain : (M : ℝ) * Vw p * (1 + 2 * θ) ≤ N / p * Vw p + 2 * (N / p * Vw p * θ) + 2 := by
      have := mul_le_mul_of_nonneg_right hMr' (mul_nonneg hV0 (show 0 ≤ 1 + 2 * θ by linarith))
      have hNp : 0 ≤ (N : ℝ) / p * Vw p := by positivity
      nlinarith
    have hid : 2 * κ * (N / L) * (L * (Vw p / p) * Real.exp (-2 * (L / Real.log p))) =
        2 * (N / p * Vw p * (κ * Real.exp (-2 * (L / Real.log p)))) := by
      field_simp
    have hNp : 0 ≤ (N : ℝ) / p * Vw p := by positivity
    have := mul_le_mul_of_nonneg_left hθκ hNp
    linarith
  -- Buchstab from 2
  have hB := siftMin_buchstab N (w := 2) (z := z) hz
  rw [siftMin_two] at hB
  have hBr : (N : ℝ) ≤ siftMin N z + ∑ p ∈ P, (siftMax (N / p + 1) p : ℝ) := by
    exact_mod_cast hB
  have hsum := sum_le_sum hper
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, sum_const] at hsum
  have htel : ∑ p ∈ P, (N : ℝ) / p * Vw p = N * (1 - Vw z) := by
    rw [← sum_Vw_div z hz, mul_sum]
    refine sum_congr rfl fun p _ => by ring
  have hR := rankin_error_sum hA hs0 hL hz hzN
  have hcard : (P.card : ℝ) ≤ z := by
    have : P.card ≤ z := (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  rw [htel] at hsum
  simp only [nsmul_eq_mul] at hsum
  have hNL : 0 ≤ 2 * κ * (N / L) := by positivity
  have hR' := mul_le_mul_of_nonneg_left hR hNL
  have hid2 : 2 * κ * (N / L) * (4 * A * Real.exp (-s) * (Real.log z + mertB) / L) =
      8 * A * κ * Real.exp (-s) * (Real.log z + mertB) * N / L ^ 2 := by
    field_simp; ring
  have h2 : (P.card : ℝ) * 2 ≤ 2 * z := by linarith
  have h3 : (P.card : ℝ) * Er ≤ z * Er := mul_le_mul_of_nonneg_right hcard hEr
  nlinarith

lemma tendsto_log_cube_div_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log N ^ 3 / (N : ℝ) ^ a) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) ha).tendsto_div_nhds_zero
  refine (h.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  simp only [Function.comp]
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The finite lower bound, normalised by `log N / N`. -/
theorem aSeq_ge_finite {C A : ℝ} {M₀ : ℕ} (hC0 : 0 ≤ C) (hfl : UpperFL C M₀)
    (hA : ∀ p : ℕ, 2 ≤ p → Vw p ≤ A / Real.log p) {s : ℝ} (hs : 4 ≤ s)
    (hsK : Real.exp rankK * Real.exp (2 - 2 * s) ≤ 1 / 2) {N z : ℕ} (hN3 : 3 ≤ N) (hz2 : 2 ≤ z)
    (hzle : (z : ℝ) ≤ (N : ℝ) ^ (1 / s)) (hMN : (M₀ : ℝ) ≤ (N : ℝ) ^ (1 - 1 / s)) :
    Real.log N / mertensP (z - 1) -
      8 * A * Real.exp (rankK + 2) * Real.exp (-s) * ((Real.log z + mertB) / Real.log N) -
      (2 + 2 * C ^ 2) * (Real.log N ^ 3 / (N : ℝ) ^ (1 / 12 : ℝ)) ≤
      siftMin N z * Real.log N / N := by
  have hs0 : 0 < s := by linarith
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log N := ⟨_, rfl⟩
  rw [← hLdef]
  have hL1 : 1 ≤ L := by
    rw [hLdef, show (1 : ℝ) = Real.log (Real.exp 1) by simp]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hL : 0 < L := by linarith
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hzN : Real.log z ≤ L / s := by
    have h := Real.log_le_log hzpos hzle
    rw [Real.log_rpow hNpos, ← hLdef] at h; linarith [show 1 / s * L = L / s by ring]
  have hMz : (M₀ : ℝ) ≤ N / z := by
    refine hMN.trans ?_
    rw [le_div_iff₀ hzpos]
    calc (N : ℝ) ^ (1 - 1 / s) * z ≤ (N : ℝ) ^ (1 - 1 / s) * (N : ℝ) ^ (1 / s) :=
          mul_le_mul_of_nonneg_left hzle (by positivity)
      _ = N := by rw [← Real.rpow_add hNpos]; simp
  have hfin := siftMin_ge_finite hC0 hfl hA (by linarith) hsK (by omega) hz2
    (by rw [← hLdef]; exact hzN) hMz
  rw [← hLdef] at hfin
  obtain ⟨t, htdef⟩ : ∃ t, t = (N : ℝ) ^ (1 / 12 : ℝ) := ⟨_, rfl⟩
  rw [← htdef]
  have ht1 : 1 ≤ t := htdef ▸ Real.one_le_rpow hN1.le (by norm_num)
  have htpos : 0 < t := by linarith
  have ht12 : t ^ 12 = N := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
  have hz3 : (z : ℝ) ≤ t ^ 3 := by
    refine hzle.trans ?_
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1.le (by
      rw [div_le_iff₀ hs0]; norm_num; linarith)
  have h13 : (N : ℝ) ^ (1 / 3 : ℝ) = t ^ 4 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
  rw [h13] at hfin
  have hVz : L / mertensP (z - 1) = L * Vw z := by
    rw [mertensP_eq_inv, div_inv_eq_mul]; rfl
  rw [hVz, le_div_iff₀ hNpos]
  have hLt : L ^ 3 / t * N = L ^ 3 * t ^ 11 := by
    rw [← ht12]; field_simp
  obtain ⟨c, hc⟩ : ∃ c, c = 8 * A * Real.exp (rankK + 2) * Real.exp (-s) := ⟨_, rfl⟩
  rw [← hc]
  have hfinL := mul_le_mul_of_nonneg_right hfin hL.le
  have e1 : c * ((Real.log z + mertB) / L) * N =
      8 * A * Real.exp (rankK + 2) * Real.exp (-s) * (Real.log z + mertB) * N / L ^ 2 * L := by
    rw [hc]; field_simp
  have he2 : 2 * (z : ℝ) * L ≤ 2 * L ^ 3 * t ^ 11 := by
    have : (z : ℝ) ≤ t ^ 11 := hz3.trans (pow_le_pow_right₀ ht1 (by norm_num))
    have : L ≤ L ^ 3 := by nlinarith
    nlinarith [pow_pos htpos 11]
  have he3 : 2 * (z : ℝ) * (t ^ 4 * (C * L)) ^ 2 * L ≤ 2 * C ^ 2 * (L ^ 3 * t ^ 11) := by
    have h8 : (z : ℝ) * t ^ 8 ≤ t ^ 11 := by
      have := mul_le_mul_of_nonneg_right hz3 (pow_pos htpos 8).le
      linarith [show t ^ 3 * t ^ 8 = t ^ 11 by ring]
    have hC2 : 0 ≤ 2 * C ^ 2 * L ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left h8 hC2
    linarith [show 2 * (z : ℝ) * (t ^ 4 * (C * L)) ^ 2 * L = 2 * C ^ 2 * L ^ 3 * (z * t ^ 8) by ring]
  linear_combination hfinL + he2 + he3 - e1 - (2 + 2 * C ^ 2) * hLt

/-- **Lower fundamental lemma at a level** (`s ≥ 4`, `e^K e^{2−2s} ≤ 1/2`). -/
theorem aLow_ge_rate {C A : ℝ} {M₀ : ℕ} (hC0 : 0 ≤ C) (hfl : UpperFL C M₀)
    (hA : ∀ p : ℕ, 2 ≤ p → Vw p ≤ A / Real.log p) {s : ℝ} (hs : 4 ≤ s)
    (hsK : Real.exp rankK * Real.exp (2 - 2 * s) ≤ 1 / 2) :
    mertC * s - 8 * A * Real.exp (rankK + 2) * Real.exp (-s) * (1 / s) ≤ aLow s := by
  have hs0 : 0 < s := by linarith
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hN
  have hzr : Tendsto (fun N : ℕ => (Real.log ⌊(N : ℝ) ^ (1 / s)⌋₊ + mertB) / Real.log N) atTop
      (𝓝 (1 / s)) := by
    have := (tendsto_log_floor_rpow_div (a := 1 / s) (by positivity)).add
      (hlog.const_div_atTop mertB)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards with N
    rw [add_div]
  have hg := ((tendsto_log_div_mertensP hs0).sub
    (hzr.const_mul (8 * A * Real.exp (rankK + 2) * Real.exp (-s)))).sub
      ((tendsto_log_cube_div_rpow (a := 1 / 12) (by norm_num)).const_mul (2 + 2 * C ^ 2))
  rw [mul_zero, sub_zero] at hg
  have hgap : 0 < 1 - 1 / s := by
    rw [sub_pos, div_lt_one hs0]; linarith
  have hz2 : ∀ᶠ N : ℕ in atTop, 2 ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ :=
    (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by positivity)).comp hN)).eventually_ge_atTop 2
  have hM : ∀ᶠ N : ℕ in atTop, (M₀ : ℝ) ≤ (N : ℝ) ^ (1 - 1 / s) :=
    ((tendsto_rpow_atTop hgap).comp hN).eventually_ge_atTop _
  set lim := mertC * s - 8 * A * Real.exp (rankK + 2) * Real.exp (-s) * (1 / s)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hev := hg.eventually (lt_mem_nhds (show lim - δ < lim by linarith))
  have : lim - δ ≤ aLow s := by
    refine le_liminf_of_le (aSeq_cobdd hs0) ?_
    filter_upwards [hz2, hM, eventually_ge_atTop 3, hev] with N hz2 hMN hN3 h2
    exact h2.le.trans (aSeq_ge_finite hC0 hfl hA hs hsK hN3 hz2
      (Nat.floor_le (by positivity)) hMN)
  linarith

/-- **The lower half of the fundamental lemma**: `a(s) ≥ e^{−γ}s − M e^{−s}` for `s ≥ 2`. -/
theorem aLow_ge_fl' : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 2 ≤ s → mertC * s - M * Real.exp (-s) ≤ aLow s := by
  obtain ⟨C, hC, M₀, hfl⟩ := siftMax_le_fl
  obtain ⟨A, hA0, hA⟩ := Vw_le_div_log
  set s₁ := max 4 ((rankK + 2 + Real.log 2) / 2)
  have hs₁ : 4 ≤ s₁ := le_max_left _ _
  set c := 8 * A * Real.exp (rankK + 2)
  have hc : 0 ≤ c := by positivity
  refine ⟨max c (mertC * s₁ * Real.exp s₁), le_max_of_le_left hc, fun s hs => ?_⟩
  have he := Real.exp_pos (-s)
  have hmC := mertC_pos
  rcases le_or_gt s₁ s with h | h
  · have hsK : Real.exp rankK * Real.exp (2 - 2 * s) ≤ 1 / 2 := by
      have hh : rankK + (2 - 2 * s) ≤ -Real.log 2 := by
        have := le_max_right 4 ((rankK + 2 + Real.log 2) / 2); linarith
      rw [← Real.exp_add]
      calc Real.exp (rankK + (2 - 2 * s)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hh
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have h1 := aLow_ge_rate hC.le hfl hA (hs₁.trans h) hsK
    have h2 : c * Real.exp (-s) * (1 / s) ≤ c * Real.exp (-s) := by
      have : 1 / s ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact mul_le_of_le_one_right (by positivity) this
    have h3 : c * Real.exp (-s) ≤ max c (mertC * s₁ * Real.exp s₁) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) he.le
    linarith
  · have h0 := aLow_nonneg' (show (0 : ℝ) < s by linarith)
    have : mertC * s ≤ mertC * s₁ * Real.exp s₁ * Real.exp (-s) := by
      rw [mul_assoc, ← Real.exp_add]
      have : mertC * s ≤ mertC * s₁ := by nlinarith
      exact this.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by linarith)))
    have h3 : mertC * s₁ * Real.exp s₁ * Real.exp (-s) ≤
        max c (mertC * s₁ * Real.exp s₁) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) he.le
    linarith

end LeanFormalizations.Erdos385.LinearSieve

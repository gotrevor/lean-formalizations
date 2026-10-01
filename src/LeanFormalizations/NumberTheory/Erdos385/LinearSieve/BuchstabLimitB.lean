/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.BuchstabLimitA

/-!
# The upper Buchstab inequality in the limit (phase E5, step 2, `b` side)

Mirror of `BuchstabBin`/`BuchstabLimitA`.  `eventually_bin_ge`: one bin of
`Σ S⁻(N/p − 1, p)` is `≥ max(a(σ)−δ,0)(1−δ)/(1+δ)·t'/(t'−1)·(log(t'/t)−δ)·N/log N` for
`σ < t − 1` (now `p ≤ M^{1/σ}`, the sub-problem is sifted *less* than at level `σ`).
-/

namespace LeanFormalizations.Erdos385.LinearSieve
open Filter Topology Finset

lemma sum_Ico_inv_ge (w z : ℕ) (h : w ≤ z) :
    LeanFormalizations.Mertens.primeRecipSum z - LeanFormalizations.Mertens.primeRecipSum w -
      (z : ℝ)⁻¹ ≤ ∑ p ∈ (Ico w z).filter Nat.Prime, (p : ℝ)⁻¹ := by
  rw [primeRecipSum_sub w z h]
  have hsub : (Ioc w z).filter Nat.Prime ⊆ insert z ((Ico w z).filter Nat.Prime) := by
    intro p hp
    simp only [mem_filter, mem_Ico, mem_insert, mem_Ioc] at hp ⊢
    rcases eq_or_lt_of_le hp.1.2 with h | h
    · left; exact h
    · right; exact ⟨⟨hp.1.1.le, h⟩, hp.2⟩
  have : ∑ p ∈ (Ioc w z).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      ∑ p ∈ insert z ((Ico w z).filter Nat.Prime), (p : ℝ)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hz' : z ∉ (Ico w z).filter Nat.Prime := by simp
  rw [sum_insert hz'] at this
  linarith

lemma eventually_sum_window_ge {t t' δ : ℝ} (ht : 0 < t) (htt' : t ≤ t') (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Real.log (t' / t) - δ ≤
      ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ (1 / t)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by positivity)).comp hN)
  have hinv : ∀ᶠ N : ℕ in atTop, ((⌊(N : ℝ) ^ (1 / t)⌋₊ : ℕ) : ℝ)⁻¹ ≤ δ / 2 :=
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hz)).eventually
      (ge_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))
  have hwin := (tendsto_primeRecip_window ht htt').eventually
    (le_mem_nhds (show Real.log (t' / t) - δ / 2 < Real.log (t' / t) by linarith))
  filter_upwards [hinv, hwin, hz.eventually_ge_atTop 1, eventually_ge_atTop 1] with N h1 h2 h3 h4
  have hle : ⌊(N : ℝ) ^ (1 / t')⌋₊ ≤ ⌊(N : ℝ) ^ (1 / t)⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h4)
      (one_div_le_one_div_of_le ht htt'))
  have := sum_Ico_inv_ge _ _ hle
  linarith

lemma nat_div_sub_one_ge (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 2 ≤ ((N / p - 1 : ℕ) : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 := real_div_le_nat_div_add_one N p hp
  rcases Nat.eq_zero_or_pos (N / p) with h0 | hpos
  · rw [h0] at h1 ⊢; simp at h1 ⊢; linarith
  · rw [Nat.cast_sub hpos]; push_cast; linarith

set_option maxHeartbeats 800000 in
/-- **One bin, lower form.**  For `1 < t ≤ t'`, `0 < σ < t − 1`, `0 < δ < 1`, eventually
`Σ_{⌊N^{1/t'}⌋ ≤ p < ⌊N^{1/t}⌋} S⁻(N/p − 1, p) ≥
  max(a(σ)−δ, 0)·(1−δ)/(1+δ)·t'/(t'−1)·(log(t'/t)−δ)·N/log N`. -/
theorem eventually_bin_ge {t t' σ δ : ℝ} (ht : 1 < t) (htt' : t ≤ t') (hσ0 : 0 < σ)
    (hσ : σ < t - 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ N : ℕ in atTop, max (aLow σ - δ) 0 * ((1 - δ) / (1 + δ)) * (t' / (t' - 1)) *
      (Real.log (t' / t) - δ) * (N / Real.log N) ≤
      ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime,
        (siftMin (N / p - 1) p : ℝ) := by
  have ht0 : 0 < t := by linarith
  have ht'0 : 0 < t' := by linarith
  have ht'1 : 0 < t' - 1 := by linarith
  set A := max (aLow σ - δ) 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  have hF1 : ∀ᶠ M : ℕ in atTop, aLow σ - δ < aSeq σ M :=
    eventually_lt_of_lt_liminf (show aLow σ - δ < aLow σ by linarith)
      (isBoundedUnder_of ⟨0, aSeq_nonneg σ⟩)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp hF1
  have hgap : 0 < t - 1 - σ := by linarith
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hgap).eventually_ge_atTop (2 : ℝ))
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : 0 < 1 - 1 / t := by rw [sub_pos, div_lt_one ht0]; exact ht
  have hF2 : ∀ᶠ N : ℕ in atTop,
      max (max ((M₁ : ℝ) + 3) (2 / δ)) 4 ≤ (N : ℝ) ^ (1 - 1 / t) :=
    ((tendsto_rpow_atTop he).comp hN).eventually_ge_atTop _
  have hF3 : ∀ᶠ N : ℕ in atTop, max (2 * P₀) 4 ≤ (N : ℝ) ^ (1 / t') :=
    ((tendsto_rpow_atTop (by positivity)).comp hN).eventually_ge_atTop _
  have hF5 : ∀ᶠ N : ℕ in atTop, Real.log 2 ≤ δ * (1 - 1 / t') * Real.log N := by
    have : 0 < δ * (1 - 1 / t') := by
      have : 1 / t' < 1 := by rw [div_lt_one ht'0]; linarith
      nlinarith
    exact ((Real.tendsto_log_atTop.comp hN).const_mul_atTop this).eventually_ge_atTop _
  have hF4 := eventually_sum_window_ge ht0 htt' hδ
  filter_upwards [hF2, hF3, hF4, hF5, eventually_ge_atTop 2] with N h2 h3 h4 h5 hN2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  set K := A * ((1 - δ) / (1 + δ)) * (t' / (t' - 1)) * (N / Real.log N) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ (1 - δ) / (1 + δ) := div_nonneg (by linarith) (by linarith)
    positivity
  have hterm : ∀ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime,
      K * (p : ℝ)⁻¹ ≤ (siftMin (N / p - 1) p : ℝ) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hpI
    have hp0 : 0 < p := hpp.pos
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
    have hpz : (p : ℝ) ≤ (N : ℝ) ^ (1 / t) :=
      (by exact_mod_cast hhi.le : (p : ℝ) ≤ ⌊(N : ℝ) ^ (1 / t)⌋₊).trans (Nat.floor_le (by positivity))
    have hpw : (N : ℝ) ^ (1 / t') / 2 ≤ p := by
      have := Nat.sub_one_lt_floor ((N : ℝ) ^ (1 / t'))
      have : ((⌊(N : ℝ) ^ (1 / t')⌋₊ : ℕ) : ℝ) ≤ p := by exact_mod_cast hlo
      have h4' : (4 : ℝ) ≤ (N : ℝ) ^ (1 / t') := (le_max_right _ _).trans h3
      linarith
    set x : ℝ := (N : ℝ) / p with hx
    have hxN : (N : ℝ) ^ (1 - 1 / t) ≤ x := by
      rw [Real.rpow_sub hNpos, Real.rpow_one, hx]
      exact div_le_div_of_nonneg_left hNpos.le hpr hpz
    have hx1 : (M₁ : ℝ) + 3 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans (h2.trans hxN)
    have hxδ : 2 / δ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans (h2.trans hxN)
    have hx4 : 4 ≤ x := (le_max_right _ _).trans (h2.trans hxN)
    set M : ℕ := N / p - 1 with hM
    have hMlo : x - 2 ≤ M := nat_div_sub_one_ge N p hp0
    have hMhi : (M : ℝ) ≤ x := by
      rw [hM]
      calc ((N / p - 1 : ℕ) : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
        _ ≤ x := Nat.cast_div_le
    have hMM₁ : M₁ ≤ M := by
      have : (M₁ : ℝ) ≤ M := by linarith
      exact_mod_cast this
    have hPp : (P₀ : ℝ) ≤ p := by
      have : 2 * (P₀ : ℝ) ≤ (N : ℝ) ^ (1 / t') := (le_max_left _ _).trans h3
      linarith
    have hpow := hP₀ p hPp
    -- p^σ ≤ M
    have hpσ : (p : ℝ) ^ σ ≤ M := by
      have hpt : (p : ℝ) ^ t ≤ N := by
        calc (p : ℝ) ^ t ≤ ((N : ℝ) ^ (1 / t)) ^ t := Real.rpow_le_rpow hpr.le hpz ht0.le
          _ = N := by rw [← Real.rpow_mul hNpos.le, one_div_mul_cancel ht0.ne', Real.rpow_one]
      have hsplit : (p : ℝ) ^ (t - 1) = (p : ℝ) ^ (t - 1 - σ) * (p : ℝ) ^ σ := by
        rw [← Real.rpow_add hpr]; ring_nf
      have hx' : (p : ℝ) ^ (t - 1) ≤ x := by
        rw [hx, le_div_iff₀ hpr, Real.rpow_sub_one hpr.ne', div_mul_cancel₀ _ hpr.ne']
        exact hpt
      have hσp : 0 ≤ (p : ℝ) ^ σ := by positivity
      have : 2 * (p : ℝ) ^ σ ≤ x := by
        calc 2 * (p : ℝ) ^ σ ≤ (p : ℝ) ^ (t - 1 - σ) * (p : ℝ) ^ σ :=
              mul_le_mul_of_nonneg_right hpow hσp
          _ = (p : ℝ) ^ (t - 1) := hsplit.symm
          _ ≤ x := hx'
      linarith
    have hfl : p ≤ ⌊(M : ℝ) ^ (1 / σ)⌋₊ := by
      apply Nat.le_floor
      calc (p : ℝ) = ((p : ℝ) ^ σ) ^ (1 / σ) := by
            rw [← Real.rpow_mul hpr.le, mul_one_div_cancel hσ0.ne', Real.rpow_one]
        _ ≤ (M : ℝ) ^ (1 / σ) := Real.rpow_le_rpow (by positivity) hpσ (by positivity)
    have hsm : (siftMin M ⌊(M : ℝ) ^ (1 / σ)⌋₊ : ℝ) ≤ siftMin M p := by
      exact_mod_cast siftMin_anti_z M hfl
    have hMpos : (0 : ℝ) < M := by linarith
    have hM2 : (2 : ℝ) ≤ M := by linarith
    have hlogMpos : 0 < Real.log M := Real.log_pos (by linarith)
    -- liminf bound
    have ha : A * M / Real.log M ≤ siftMin M ⌊(M : ℝ) ^ (1 / σ)⌋₊ := by
      rw [div_le_iff₀ hlogMpos]
      rcases le_total (aLow σ - δ) 0 with hneg | hpos
      · rw [hA, max_eq_right hneg]; simp; positivity
      · rw [hA, max_eq_left hpos]
        have := (hM₁ M hMM₁).le
        unfold aSeq at this
        rw [le_div_iff₀ hMpos] at this
        linarith
    -- log M ≤ (1 + δ)(1 − 1/t') log N
    have hlogM : Real.log M ≤ (1 + δ) * ((1 - 1 / t') * Real.log N) := by
      have h1 : Real.log M ≤ Real.log x := Real.log_le_log hMpos hMhi
      have h2' : Real.log x ≤ (1 - 1 / t') * Real.log N + Real.log 2 := by
        have hpw' : 0 < (N : ℝ) ^ (1 / t') / 2 := by positivity
        have := Real.log_le_log hpw' hpw
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos] at this
        rw [hx, Real.log_div hNpos.ne' hpr.ne']
        linarith
      have e : (1 + δ) * ((1 - 1 / t') * Real.log N) =
          (1 - 1 / t') * Real.log N + δ * (1 - 1 / t') * Real.log N := by ring
      rw [e]; linarith
    have hfrac : K * (p : ℝ)⁻¹ ≤ A * M / Real.log M := by
      have hMx : (1 - δ) * x ≤ M := by
        have : 2 ≤ δ * x := by rw [div_le_iff₀ hδ] at hxδ; linarith
        nlinarith
      have hcoef : t' / (t' - 1) = 1 / (1 - 1 / t') := by field_simp
      have hb : 0 < (1 - 1 / t') := by
        have : 1 / t' < 1 := by rw [div_lt_one ht'0]; linarith
        linarith
      rw [le_div_iff₀ hlogMpos]
      have hKp : K * (p : ℝ)⁻¹ = A * (1 - δ) * x / ((1 + δ) * ((1 - 1 / t') * Real.log N)) := by
        rw [hK, hx, hcoef]; field_simp
      rw [hKp]
      have hden : 0 < (1 + δ) * ((1 - 1 / t') * Real.log N) := by positivity
      calc A * (1 - δ) * x / ((1 + δ) * ((1 - 1 / t') * Real.log N)) * Real.log M
          ≤ A * (1 - δ) * x / ((1 + δ) * ((1 - 1 / t') * Real.log N)) *
              ((1 + δ) * ((1 - 1 / t') * Real.log N)) := by
            refine mul_le_mul_of_nonneg_left hlogM ?_
            have : 0 ≤ 1 - δ := by linarith
            have : 0 ≤ x := by linarith
            positivity
        _ = A * ((1 - δ) * x) := by field_simp
        _ ≤ A * M := mul_le_mul_of_nonneg_left hMx hA0
    exact hfrac.trans (ha.trans hsm)
  calc max (aLow σ - δ) 0 * ((1 - δ) / (1 + δ)) * (t' / (t' - 1)) * (Real.log (t' / t) - δ) *
        (N / Real.log N) = K * (Real.log (t' / t) - δ) := by rw [hK]; ring
    _ ≤ K * ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left h4 hK0
    _ = ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime, K * (p : ℝ)⁻¹ := by
        rw [mul_sum]
    _ ≤ _ := sum_le_sum hterm

/-- Lower bin weights at slack `δ`. -/
noncomputable def binD (s h δ : ℝ) (i : ℕ) : ℝ :=
  max (aLow (s + i * h - 1 - h) - δ) 0 * ((1 - δ) / (1 + δ)) *
    ((s + (i + 1) * h) / (s + (i + 1) * h - 1)) *
    (Real.log ((s + (i + 1) * h) / (s + i * h)) - δ)

/-- **Finite upper Buchstab, limsup form, at slack `δ`.** -/
theorem bUp_le_bins_delta {s s' : ℝ} (hs : 2 ≤ s) (hss' : s < s') {k : ℕ} (hk : 0 < k)
    (hh : (s' - s) / k < 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    bUp s ≤ bUp s' - ∑ i ∈ range k, binD s ((s' - s) / k) δ i := by
  set h := (s' - s) / k with hhdef
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < h := div_pos (by linarith) hkr
  set t : ℕ → ℝ := fun i => s + i * h with ht
  have htk : t k = s' := by simp only [ht, hhdef]; field_simp; ring
  have ht0 : t 0 = s := by simp [ht]
  have htge : ∀ i, s ≤ t i := fun i => by
    simp only [ht]; have : (0 : ℝ) ≤ i * h := by positivity
    linarith
  have htmono : ∀ i, t i ≤ t (i + 1) := fun i => by simp only [ht]; push_cast; nlinarith
  set D := ∑ i ∈ range k, binD s h δ i with hD
  have hbins : ∀ᶠ N : ℕ in atTop, ∀ i ∈ range k, binD s h δ i * (N / Real.log N) ≤
      (∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t (i + 1))⌋₊ ⌊(N : ℝ) ^ (1 / t i)⌋₊).filter Nat.Prime,
        (siftMin (N / p - 1) p : ℝ)) := by
    refine (eventually_all_finset _).mpr fun i _ => ?_
    have := eventually_bin_ge (t := t i) (t' := t (i + 1)) (σ := t i - 1 - h)
      (by linarith [htge i]) (htmono i) (by linarith [htge i]) (by linarith) hδ hδ1
    refine this.mono fun N hN => le_trans (le_of_eq ?_) hN
    simp only [binD, ht]; push_cast; ring
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hev : ∀ᶠ N : ℕ in atTop, bSeq s' N < bUp s' + ε / 2 :=
    eventually_lt_of_limsup_lt (show bUp s' < bUp s' + ε / 2 by linarith)
      (bSeq_bdd (by linarith))
  have key : ∀ᶠ N : ℕ in atTop, bSeq s N ≤ bUp s' + ε / 2 - D := by
    filter_upwards [hbins, hev, eventually_ge_atTop 2] with N hb ha hN2
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hNpos : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos (by linarith)
    set w : ℕ → ℕ := fun i => ⌊(N : ℝ) ^ (1 / t i)⌋₊ with hw
    have hwa : Antitone w := by
      refine antitone_nat_of_succ_le fun i => Nat.floor_le_floor ?_
      exact Real.rpow_le_rpow_of_exponent_le (by linarith)
        (one_div_le_one_div_of_le (by linarith [htge i]) (htmono i))
    have hbuch := siftMax_buchstab N (hwa (Nat.zero_le k))
    have hchain := sum_Ico_antitone_chain (fun p => (siftMin (N / p - 1) p : ℝ)) w hwa k
    have hsum : D * (N / Real.log N) ≤
        (∑ p ∈ (Ico (w k) (w 0)).filter Nat.Prime, (siftMin (N / p - 1) p : ℝ)) := by
      rw [hchain, hD, sum_mul]
      exact sum_le_sum hb
    have hbuchR : (siftMax N (w 0) : ℝ) +
        ∑ p ∈ (Ico (w k) (w 0)).filter Nat.Prime, (siftMin (N / p - 1) p : ℝ) ≤
        siftMax N (w k) := by
      exact_mod_cast hbuch
    have hw0 : w 0 = ⌊(N : ℝ) ^ (1 / s)⌋₊ := by simp [hw, ht0]
    have hwk : w k = ⌊(N : ℝ) ^ (1 / s')⌋₊ := by simp only [hw]; rw [htk]
    rw [hw0, hwk] at hbuchR hsum
    have ha' : bSeq s' N < bUp s' + ε / 2 := ha
    unfold bSeq at ha' ⊢
    rw [div_lt_iff₀ hNpos] at ha'
    rw [div_le_iff₀ hNpos]
    have e1 : D * (N / Real.log N) * Real.log N = D * N := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hbuchR hlog.le, mul_le_mul_of_nonneg_right hsum hlog.le]
  have := limsup_le_of_le (isCoboundedUnder_le_of_le atTop (bSeq_nonneg s)) key
  change bUp s ≤ bUp s' + ε / 2 - D at this
  linarith

/-- **Finite upper Buchstab, limsup form** (`δ → 0`, `log x ≥ 1 − 1/x`). -/
theorem bUp_le_bins {s s' : ℝ} (hs : 2 ≤ s) (hss' : s < s') {k : ℕ} (hk : 0 < k)
    (hh : (s' - s) / k < 1) :
    bUp s ≤ bUp s' - ∑ i ∈ range k, aLow (s + i * ((s' - s) / k) - 1 - (s' - s) / k) *
      ((s' - s) / k) / (s + (i + 1) * ((s' - s) / k) - 1) := by
  set h := (s' - s) / k with hhdef
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < h := div_pos (by linarith) hkr
  have hcont : ContinuousAt (fun δ : ℝ => ∑ i ∈ range k, binD s h δ i) 0 := by
    unfold binD
    refine tendsto_finsetSum _ fun i _ => ?_
    have h1 : ContinuousAt (fun δ : ℝ => (1 - δ) / (1 + δ)) 0 :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    exact (((continuous_const.sub continuous_id).max continuous_const).continuousAt.mul h1).mul
      continuousAt_const |>.mul (continuousAt_const.sub continuousAt_id)
  have hlim : Tendsto (fun δ : ℝ => ∑ i ∈ range k, binD s h δ i) (𝓝[Set.Ioo 0 1] 0)
      (𝓝 (∑ i ∈ range k, binD s h 0 i)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hne : (𝓝[Set.Ioo (0 : ℝ) 1] 0).NeBot := left_nhdsWithin_Ioo_neBot zero_lt_one
  have hge : ∑ i ∈ range k, binD s h 0 i ≤ bUp s' - bUp s :=
    le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => by
      have := bUp_le_bins_delta hs hss' hk hh hδ.1 hδ.2
      linarith)
  have hterm : ∀ i ∈ range k, aLow (s + i * h - 1 - h) * h / (s + (i + 1) * h - 1) ≤
      binD s h 0 i := by
    intro i _
    have hi : (0 : ℝ) ≤ i * h := by positivity
    have harg : 0 < s + i * h - 1 - h := by linarith
    have ha0 : 0 ≤ aLow (s + i * h - 1 - h) := aLow_nonneg' harg
    have ht1 : 0 < s + (i + 1) * h - 1 := by nlinarith
    have ht0 : 0 < s + i * h := by linarith
    have ht' : 0 < s + (i + 1) * h := by nlinarith
    have hlog : h / (s + (i + 1) * h) ≤ Real.log ((s + (i + 1) * h) / (s + i * h)) := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < (s + (i + 1) * h) / (s + i * h) by positivity)
      have e : 1 - ((s + (i + 1) * h) / (s + i * h))⁻¹ = h / (s + (i + 1) * h) := by
        rw [inv_div]; field_simp; ring
      linarith
    unfold binD
    simp only [sub_zero, max_eq_left ha0, add_zero, div_one, mul_one]
    calc aLow (s + i * h - 1 - h) * h / (s + (i + 1) * h - 1)
        = aLow (s + i * h - 1 - h) * ((s + (i + 1) * h) / (s + (i + 1) * h - 1)) *
            (h / (s + (i + 1) * h)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  have := sum_le_sum hterm
  linarith

end LeanFormalizations.Erdos385.LinearSieve

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Rough
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.BuchstabLimitB

/-!
# Forward Buchstab for rough numbers in the limit (phase E5, `phi_buchstab`)

`phiL_buchstab`: `φ(s) + ∫_s^{s'} φ(t−1)/(t−1) ≤ φ(s')`, `φ = liminf Φ(N, N^{1/s}) log N / N`.
Same mechanism as `buchstab_limit_b'` (`BuchstabLimitB.lean`), with the exact forward identity
`rough_buchstab` in place of `siftMax_buchstab`.  `phiS`/`phiL` are `RoughOmega.phiSeq`/`phiLow`
up to `rfl`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve
open Filter Topology Finset

/-- The normalised rough-number sequence (= `RoughOmega.phiSeq`, by `rfl`). -/
noncomputable def phiS (s : ℝ) (N : ℕ) : ℝ :=
  (rough N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) * Real.log N / N

/-- Its liminf (= `RoughOmega.phiLow`, by `rfl`). -/
noncomputable def phiL (s : ℝ) : ℝ := liminf (phiS s) atTop

lemma rough_anti_z (N : ℕ) {z z' : ℕ} (h : z ≤ z') : rough N z' ≤ rough N z :=
  sift_anti_z 1 N _ h

lemma phiS_nonneg (s : ℝ) (N : ℕ) : 0 ≤ phiS s N := by
  unfold phiS
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg this
    positivity

lemma phiS_le_bSeq (s : ℝ) (N : ℕ) : phiS s N ≤ bSeq s N := by
  unfold phiS bSeq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg this
  have h : (rough N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ siftMax N ⌊(N : ℝ) ^ (1 / s)⌋₊ := by
    exact_mod_cast rough_le_siftMax _ _
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hlog) (by positivity)

lemma phiS_cobdd {s : ℝ} (hs : 0 < s) : IsCoboundedUnder (· ≥ ·) atTop (phiS s) := by
  obtain ⟨B, hB⟩ := bSeq_bdd hs
  exact isCoboundedUnder_ge_of_eventually_le atTop
    ((eventually_map.mp hB).mono fun N h => (phiS_le_bSeq s N).trans h)

lemma phiL_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ phiL s :=
  le_liminf_of_le (phiS_cobdd hs) (Eventually.of_forall (phiS_nonneg s))

lemma phiL_mono : MonotoneOn phiL (Set.Ioi 0) := by
  intro s hs s' hs' hss'
  have hs0 : (0 : ℝ) < s := hs
  refine liminf_le_liminf (Eventually.of_forall fun N => ?_)
    (isBoundedUnder_of ⟨0, phiS_nonneg s⟩) (phiS_cobdd hs')
  unfold phiS
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg h1
  have hfl : ⌊(N : ℝ) ^ (1 / s')⌋₊ ≤ ⌊(N : ℝ) ^ (1 / s)⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le h1 (one_div_le_one_div_of_le hs0 hss'))
  have : (rough N ⌊(N : ℝ) ^ (1 / s)⌋₊ : ℝ) ≤ rough N ⌊(N : ℝ) ^ (1 / s')⌋₊ := by
    exact_mod_cast rough_anti_z N hfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hlog) (by positivity)

set_option maxHeartbeats 800000 in
/-- **One bin, lower form.**  For `1 < t ≤ t'`, `0 < σ < t − 1`, `0 < δ < 1`, eventually
`Σ Φ(N/p, p) ≥
  max(a(σ)−δ, 0)·(1−δ)/(1+δ)·t'/(t'−1)·(log(t'/t)−δ)·N/log N`. -/
theorem eventually_rough_bin_ge {t t' σ δ : ℝ} (ht : 1 < t) (htt' : t ≤ t') (hσ0 : 0 < σ)
    (hσ : σ < t - 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ N : ℕ in atTop, max (phiL σ - δ) 0 * ((1 - δ) / (1 + δ)) * (t' / (t' - 1)) *
      (Real.log (t' / t) - δ) * (N / Real.log N) ≤
      ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime,
        (rough (N / p) p : ℝ) := by
  have ht0 : 0 < t := by linarith
  have ht'0 : 0 < t' := by linarith
  have ht'1 : 0 < t' - 1 := by linarith
  set A := max (phiL σ - δ) 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  have hF1 : ∀ᶠ M : ℕ in atTop, phiL σ - δ < phiS σ M :=
    eventually_lt_of_lt_liminf (show phiL σ - δ < phiL σ by linarith)
      (isBoundedUnder_of ⟨0, phiS_nonneg σ⟩)
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
      K * (p : ℝ)⁻¹ ≤ (rough (N / p) p : ℝ) := by
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
    set M : ℕ := N / p with hM
    have hMlo : x - 2 ≤ M := by
      have := real_div_le_nat_div_add_one N p hp0; rw [hM]; linarith
    have hMhi : (M : ℝ) ≤ x := by
      rw [hM]; exact Nat.cast_div_le
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
    have hsm : (rough M ⌊(M : ℝ) ^ (1 / σ)⌋₊ : ℝ) ≤ rough M p := by
      exact_mod_cast rough_anti_z M hfl
    have hMpos : (0 : ℝ) < M := by linarith
    have hM2 : (2 : ℝ) ≤ M := by linarith
    have hlogMpos : 0 < Real.log M := Real.log_pos (by linarith)
    -- liminf bound
    have ha : A * M / Real.log M ≤ rough M ⌊(M : ℝ) ^ (1 / σ)⌋₊ := by
      rw [div_le_iff₀ hlogMpos]
      rcases le_total (phiL σ - δ) 0 with hneg | hpos
      · rw [hA, max_eq_right hneg]; simp; positivity
      · rw [hA, max_eq_left hpos]
        have := (hM₁ M hMM₁).le
        unfold phiS at this
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
  calc max (phiL σ - δ) 0 * ((1 - δ) / (1 + δ)) * (t' / (t' - 1)) * (Real.log (t' / t) - δ) *
        (N / Real.log N) = K * (Real.log (t' / t) - δ) := by rw [hK]; ring
    _ ≤ K * ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left h4 hK0
    _ = ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime, K * (p : ℝ)⁻¹ := by
        rw [mul_sum]
    _ ≤ _ := sum_le_sum hterm

/-- Rough-number bin weights at slack `δ`. -/
noncomputable def binE (s h δ : ℝ) (i : ℕ) : ℝ :=
  max (phiL (s + i * h - 1 - h) - δ) 0 * ((1 - δ) / (1 + δ)) *
    ((s + (i + 1) * h) / (s + (i + 1) * h - 1)) *
    (Real.log ((s + (i + 1) * h) / (s + i * h)) - δ)

/-- **Finite forward Buchstab for rough numbers, liminf form, at slack `δ`.** -/
theorem phiL_ge_bins_delta {s s' : ℝ} (hs : 2 ≤ s) (hss' : s < s') {k : ℕ} (hk : 0 < k)
    (hh : (s' - s) / k < 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    phiL s + ∑ i ∈ range k, binE s ((s' - s) / k) δ i ≤ phiL s' := by
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
  set D := ∑ i ∈ range k, binE s h δ i with hD
  have hbins : ∀ᶠ N : ℕ in atTop, ∀ i ∈ range k, binE s h δ i * (N / Real.log N) ≤
      (∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t (i + 1))⌋₊ ⌊(N : ℝ) ^ (1 / t i)⌋₊).filter Nat.Prime,
        (rough (N / p) p : ℝ)) := by
    refine (eventually_all_finset _).mpr fun i _ => ?_
    have := eventually_rough_bin_ge (t := t i) (t' := t (i + 1)) (σ := t i - 1 - h)
      (by linarith [htge i]) (htmono i) (by linarith [htge i]) (by linarith) hδ hδ1
    refine this.mono fun N hN => le_trans (le_of_eq ?_) hN
    simp only [binE, ht]; push_cast; ring
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hev : ∀ᶠ N : ℕ in atTop, phiL s - ε / 2 < phiS s N :=
    eventually_lt_of_lt_liminf (show phiL s - ε / 2 < phiL s by linarith)
      (isBoundedUnder_of ⟨0, phiS_nonneg s⟩)
  have key : ∀ᶠ N : ℕ in atTop, phiL s - ε / 2 + D ≤ phiS s' N := by
    filter_upwards [hbins, hev, eventually_ge_atTop 2] with N hb ha hN2
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hNpos : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos (by linarith)
    set w : ℕ → ℕ := fun i => ⌊(N : ℝ) ^ (1 / t i)⌋₊ with hw
    have hwa : Antitone w := by
      refine antitone_nat_of_succ_le fun i => Nat.floor_le_floor ?_
      exact Real.rpow_le_rpow_of_exponent_le (by linarith)
        (one_div_le_one_div_of_le (by linarith [htge i]) (htmono i))
    have hbuch := rough_buchstab N (hwa (Nat.zero_le k))
    have hchain := sum_Ico_antitone_chain (fun p => (rough (N / p) p : ℝ)) w hwa k
    have hsum : D * (N / Real.log N) ≤
        (∑ p ∈ (Ico (w k) (w 0)).filter Nat.Prime, (rough (N / p) p : ℝ)) := by
      rw [hchain, hD, sum_mul]
      exact sum_le_sum hb
    have hbuchR : (rough N (w k) : ℝ) = rough N (w 0) +
        ∑ p ∈ (Ico (w k) (w 0)).filter Nat.Prime, (rough (N / p) p : ℝ) := by
      exact_mod_cast hbuch
    have hw0 : w 0 = ⌊(N : ℝ) ^ (1 / s)⌋₊ := by simp [hw, ht0]
    have hwk : w k = ⌊(N : ℝ) ^ (1 / s')⌋₊ := by simp only [hw]; rw [htk]
    rw [hw0, hwk] at hbuchR hsum
    have ha' : phiL s - ε / 2 < phiS s N := ha
    unfold phiS at ha' ⊢
    rw [lt_div_iff₀ hNpos] at ha'
    rw [le_div_iff₀ hNpos, hbuchR]
    have e1 : D * (N / Real.log N) * Real.log N = D * N := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hsum hlog.le]
  have := le_liminf_of_le (phiS_cobdd (by linarith : (0 : ℝ) < s')) key
  change phiL s - ε / 2 + D ≤ phiL s' at this
  linarith

theorem phiL_ge_bins {s s' : ℝ} (hs : 2 ≤ s) (hss' : s < s') {k : ℕ} (hk : 0 < k)
    (hh : (s' - s) / k < 1) :
    phiL s + ∑ i ∈ range k, phiL (s + i * ((s' - s) / k) - 1 - (s' - s) / k) *
      ((s' - s) / k) / (s + (i + 1) * ((s' - s) / k) - 1) ≤ phiL s' := by
  set h := (s' - s) / k with hhdef
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < h := div_pos (by linarith) hkr
  have hcont : ContinuousAt (fun δ : ℝ => ∑ i ∈ range k, binE s h δ i) 0 := by
    unfold binE
    refine tendsto_finsetSum _ fun i _ => ?_
    have h1 : ContinuousAt (fun δ : ℝ => (1 - δ) / (1 + δ)) 0 :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    exact (((continuous_const.sub continuous_id).max continuous_const).continuousAt.mul h1).mul
      continuousAt_const |>.mul (continuousAt_const.sub continuousAt_id)
  have hlim : Tendsto (fun δ : ℝ => ∑ i ∈ range k, binE s h δ i) (𝓝[Set.Ioo 0 1] 0)
      (𝓝 (∑ i ∈ range k, binE s h 0 i)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hne : (𝓝[Set.Ioo (0 : ℝ) 1] 0).NeBot := left_nhdsWithin_Ioo_neBot zero_lt_one
  have hge : ∑ i ∈ range k, binE s h 0 i ≤ phiL s' - phiL s :=
    le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => by
      have := phiL_ge_bins_delta hs hss' hk hh hδ.1 hδ.2
      linarith)
  have hterm : ∀ i ∈ range k, phiL (s + i * h - 1 - h) * h / (s + (i + 1) * h - 1) ≤
      binE s h 0 i := by
    intro i _
    have hi : (0 : ℝ) ≤ i * h := by positivity
    have harg : 0 < s + i * h - 1 - h := by linarith
    have ha0 : 0 ≤ phiL (s + i * h - 1 - h) := phiL_nonneg harg
    have ht1 : 0 < s + (i + 1) * h - 1 := by nlinarith
    have ht0 : 0 < s + i * h := by linarith
    have ht' : 0 < s + (i + 1) * h := by nlinarith
    have hlog : h / (s + (i + 1) * h) ≤ Real.log ((s + (i + 1) * h) / (s + i * h)) := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < (s + (i + 1) * h) / (s + i * h) by positivity)
      have e : 1 - ((s + (i + 1) * h) / (s + i * h))⁻¹ = h / (s + (i + 1) * h) := by
        rw [inv_div]; field_simp; ring
      linarith
    unfold binE
    simp only [sub_zero, max_eq_left ha0, add_zero, div_one, mul_one]
    calc phiL (s + i * h - 1 - h) * h / (s + (i + 1) * h - 1)
        = phiL (s + i * h - 1 - h) * ((s + (i + 1) * h) / (s + (i + 1) * h - 1)) *
            (h / (s + (i + 1) * h)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  have := sum_le_sum hterm
  linarith

/-- **Forward Buchstab for rough numbers in the limit**:
`φ(s) + ∫_s^{s'} φ(t−1)/(t−1) dt ≤ φ(s')` for `2 ≤ s ≤ s'`. -/
theorem phiL_buchstab {s s' : ℝ} (hs : 2 ≤ s) (hss' : s ≤ s') :
    phiL s + ∫ t in s..s', phiL (t - 1) / (t - 1) ≤ phiL s' := by
  rcases eq_or_lt_of_le hss' with rfl | hlt
  · simp
  set I := ∫ t in s..s', phiL (t - 1) / (t - 1)
  have hA0 : ∀ x : ℝ, 0 < x → 0 ≤ phiL x := fun x hx => phiL_nonneg hx
  have hh : Tendsto (fun k : ℕ => (s' - s) / k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun k : ℕ => (1 - 3 * ((s' - s) / k) / (s - 1)) *
      (I - 4 * ((s' - s) / k) * phiL s')) atTop
      (𝓝 ((1 - 3 * 0 / (s - 1)) * (I - 4 * 0 * phiL s'))) :=
    ((tendsto_const_nhds.sub ((tendsto_const_nhds.mul hh).div_const _)).mul
      (tendsto_const_nhds.sub ((tendsto_const_nhds.mul hh).mul tendsto_const_nhds)))
  simp only [mul_zero, zero_div, sub_zero, zero_mul, one_mul] at hR
  have hev : ∀ᶠ k : ℕ in atTop, (1 - 3 * ((s' - s) / k) / (s - 1)) *
      (I - 4 * ((s' - s) / k) * phiL s') ≤ phiL s' - phiL s := by
    filter_upwards [hh.eventually (ge_mem_nhds (show (0:ℝ) < 1 / 4 by norm_num)),
      eventually_ge_atTop 1] with k hk1 hk
    have h1 := phiL_ge_bins hs hlt (k := k) hk (by linarith)
    have h2 := riemann_delay_ge phiL_mono hA0 hs hlt (k := k) hk hk1
    linarith
  have := le_of_tendsto hR hev
  linarith

end LeanFormalizations.Erdos385.LinearSieve

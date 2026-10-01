/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.BuchstabLimit
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Bounded

/-!
# One bin of the limit Buchstab sum (phase E5, step 2)

`eventually_bin_le`: for `1 < t ≤ t'` and any level `σ > t' − 1`, eventually
`Σ_{⌊N^{1/t'}⌋ ≤ p < ⌊N^{1/t}⌋} S⁺(N/p+1, p) ≤ (b(σ)+δ)(1+δ)·t/(t−1)·(log(t'/t)+δ)·N/log N`.
Each sub-problem has length `M = N/p + 1 ≤ p^σ` (so its sifting limit `p` beats `⌊M^{1/σ}⌋`) and
`log M ≥ (1 − 1/t) log N`; the limsup `b(σ)` then bounds every term with ONE threshold.
-/

namespace LeanFormalizations.Erdos385.LinearSieve
open Filter Topology Finset

/-- Real-vs-natural division: `N/p ≤ ⌊N/p⌋ + 1`. -/
lemma real_div_le_nat_div_add_one (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
  have h := Nat.div_add_mod N p
  have hm := Nat.mod_lt N hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hp']
  have : (N : ℝ) = p * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) := by exact_mod_cast h.symm
  have hm' : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast hm
  nlinarith

/-- **One bin of the limit Buchstab sum.**  For `1 < t ≤ t'`, `σ > t' − 1`, eventually
`Σ_{⌊N^{1/t'}⌋ ≤ p < ⌊N^{1/t}⌋} S⁺(N/p + 1, p) ≤ (b(σ)+δ)(1+δ) t/(t−1) (log(t'/t)+δ) N/log N`. -/
theorem eventually_bin_le {t t' σ δ : ℝ} (ht : 1 < t) (htt' : t ≤ t') (hσ : t' - 1 < σ)
    (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime,
      (siftMax (N / p + 1) p : ℝ)) ≤
      (bUp σ + δ) * (1 + δ) * (t / (t - 1)) * (Real.log (t' / t) + δ) * (N / Real.log N) := by
  have ht0 : 0 < t := by linarith
  have ht'0 : 0 < t' := by linarith
  have hσ0 : 0 < σ := by linarith
  set B := bUp σ + δ with hB
  -- F1: the limsup bound at level σ
  have hF1 : ∀ᶠ M : ℕ in atTop, bSeq σ M < B :=
    eventually_lt_of_limsup_lt (show bUp σ < B by linarith) (bSeq_bdd hσ0)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp hF1
  have hB0 : 0 ≤ B := (bSeq_nonneg σ M₁).trans (hM₁ M₁ le_rfl).le
  -- P₀: p ≥ P₀ ⇒ 2^{t'+1} ≤ p^{σ - t' + 1}
  have hgap : 0 < σ - t' + 1 := by linarith
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hgap).eventually_ge_atTop ((2 : ℝ) ^ (t' + 1)))
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : 0 < 1 - 1 / t := by rw [sub_pos, div_lt_one ht0]; exact ht
  have hF2 : ∀ᶠ N : ℕ in atTop, max (max ((M₁ : ℝ) + 1) (1 / δ)) 2 ≤ (N : ℝ) ^ (1 - 1 / t) :=
    ((tendsto_rpow_atTop he).comp hN).eventually_ge_atTop _
  have hF3 : ∀ᶠ N : ℕ in atTop, max (2 * P₀) 4 ≤ (N : ℝ) ^ (1 / t') :=
    ((tendsto_rpow_atTop (by positivity)).comp hN).eventually_ge_atTop _
  have hF4 := eventually_sum_window_le ht0 htt' hδ
  filter_upwards [hF2, hF3, hF4, eventually_ge_atTop 2] with N h2 h3 h4 hN2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  set K := B * (1 + δ) * (t / (t - 1)) * (N / Real.log N) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < t - 1 := by linarith
    positivity
  have hterm : ∀ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime,
      (siftMax (N / p + 1) p : ℝ) ≤ K * (p : ℝ)⁻¹ := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hpI
    have hp0 : 0 < p := hpp.pos
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
    -- p ≤ N^{1/t}
    have hpz : (p : ℝ) ≤ (N : ℝ) ^ (1 / t) :=
      (by exact_mod_cast hhi.le : (p : ℝ) ≤ ⌊(N : ℝ) ^ (1 / t)⌋₊).trans (Nat.floor_le (by positivity))
    -- p ≥ N^{1/t'}/2
    have hpw : (N : ℝ) ^ (1 / t') / 2 ≤ p := by
      have := Nat.sub_one_lt_floor ((N : ℝ) ^ (1 / t'))
      have : ((⌊(N : ℝ) ^ (1 / t')⌋₊ : ℕ) : ℝ) ≤ p := by exact_mod_cast hlo
      have h4' : (4 : ℝ) ≤ (N : ℝ) ^ (1 / t') := (le_max_right _ _).trans h3
      linarith
    -- x = N/p ≥ N^{1-1/t}
    set x : ℝ := (N : ℝ) / p with hx
    have hxN : (N : ℝ) ^ (1 - 1 / t) ≤ x := by
      rw [Real.rpow_sub hNpos, Real.rpow_one, hx]
      exact div_le_div_of_nonneg_left hNpos.le hpr hpz
    have hx1 : (M₁ : ℝ) + 1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans (h2.trans hxN)
    have hxδ : 1 / δ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans (h2.trans hxN)
    have hx2 : 2 ≤ x := (le_max_right _ _).trans (h2.trans hxN)
    set M : ℕ := N / p + 1 with hM
    have hMlo : x ≤ M := by rw [hM]; push_cast; exact real_div_le_nat_div_add_one N p hp0
    have hMhi : (M : ℝ) ≤ x + 1 := by
      rw [hM]; push_cast; have := Nat.cast_div_le (α := ℝ) (m := N) (n := p); linarith
    have hMM₁ : M₁ ≤ M := by
      have : (M₁ : ℝ) ≤ M := by linarith
      exact_mod_cast this
    -- ⌊M^{1/σ}⌋ ≤ p
    have hPp : (P₀ : ℝ) ≤ p := by
      have : 2 * (P₀ : ℝ) ≤ (N : ℝ) ^ (1 / t') := (le_max_left _ _).trans h3
      linarith
    have hpow := hP₀ p hPp
    have hMσ : (M : ℝ) ≤ (p : ℝ) ^ σ := by
      have hNle : (N : ℝ) ≤ (2 * p) ^ t' := by
        have h2p : (N : ℝ) ^ (1 / t') ≤ 2 * p := by linarith
        calc (N : ℝ) = ((N : ℝ) ^ (1 / t')) ^ t' := by
              rw [← Real.rpow_mul hNpos.le, one_div_mul_cancel ht'0.ne', Real.rpow_one]
          _ ≤ (2 * p) ^ t' := Real.rpow_le_rpow (by positivity) h2p ht'0.le
      have hsplit : (p : ℝ) ^ σ = (p : ℝ) ^ (σ - t' + 1) * ((p : ℝ) ^ t' / p) := by
        rw [← Real.rpow_sub_one hpr.ne', ← Real.rpow_add hpr]; ring_nf
      have hmul : ((2 : ℝ) * p) ^ t' = 2 ^ t' * (p : ℝ) ^ t' :=
        Real.mul_rpow (by norm_num) hpr.le
      have h2t : (2 : ℝ) ^ (t' + 1) = 2 ^ t' * 2 := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
      have hq : 0 ≤ (p : ℝ) ^ t' / p := by positivity
      calc (M : ℝ) ≤ x + 1 := hMhi
        _ ≤ 2 * x := by linarith
        _ = 2 * N / p := by rw [hx]; ring
        _ ≤ 2 * (2 ^ t' * (p : ℝ) ^ t') / p := by
            rw [← hmul]; gcongr
        _ = (2 : ℝ) ^ (t' + 1) * ((p : ℝ) ^ t' / p) := by rw [h2t]; ring
        _ ≤ (p : ℝ) ^ (σ - t' + 1) * ((p : ℝ) ^ t' / p) := mul_le_mul_of_nonneg_right hpow hq
        _ = _ := hsplit.symm
    have hfl : ⌊(M : ℝ) ^ (1 / σ)⌋₊ ≤ p := by
      apply Nat.floor_le_of_le
      calc (M : ℝ) ^ (1 / σ) ≤ ((p : ℝ) ^ σ) ^ (1 / σ) :=
            Real.rpow_le_rpow (by positivity) hMσ (by positivity)
        _ = p := by rw [← Real.rpow_mul hpr.le, mul_one_div_cancel hσ0.ne', Real.rpow_one]
    have hsm : (siftMax M p : ℝ) ≤ siftMax M ⌊(M : ℝ) ^ (1 / σ)⌋₊ := by
      exact_mod_cast siftMax_anti_z M hfl
    -- the limsup bound at M
    have hMpos : (0 : ℝ) < M := by linarith
    have hlogM : (1 - 1 / t) * Real.log N ≤ Real.log M := by
      have := Real.log_le_log (by positivity) (hxN.trans hMlo)
      rwa [Real.log_rpow hNpos] at this
    have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by positivity) hlogM
    have hb : (siftMax M ⌊(M : ℝ) ^ (1 / σ)⌋₊ : ℝ) ≤ B * M / Real.log M := by
      have := (hM₁ M hMM₁).le
      unfold bSeq at this
      rw [div_le_iff₀ hMpos] at this
      rw [le_div_iff₀ hlogMpos]; linarith
    have hfrac : B * M / Real.log M ≤ K * (p : ℝ)⁻¹ := by
      have ht1 : 0 < t - 1 := by linarith
      have hMx : (M : ℝ) ≤ (1 + δ) * x := by
        have : 1 ≤ δ * x := by rw [div_le_iff₀ hδ] at hxδ; linarith
        nlinarith
      have hcoef : 1 - 1 / t = (t - 1) / t := by field_simp
      rw [div_le_iff₀ hlogMpos]
      have hstep : B * M ≤ B * ((1 + δ) * (N / p)) := mul_le_mul_of_nonneg_left hMx hB0
      have hlog' : (t - 1) / t * Real.log N ≤ Real.log M := by rwa [← hcoef]
      have hR : B * (1 + δ) * (t / (t - 1)) * (N / Real.log N) * (p : ℝ)⁻¹ * Real.log M ≥
          B * (1 + δ) * (t / (t - 1)) * (N / Real.log N) * (p : ℝ)⁻¹ * ((t - 1) / t * Real.log N) :=
        mul_le_mul_of_nonneg_left hlog' (by positivity)
      have hEq : B * (1 + δ) * (t / (t - 1)) * (N / Real.log N) * (p : ℝ)⁻¹ * ((t - 1) / t * Real.log N)
          = B * ((1 + δ) * (N / p)) := by field_simp
      linarith
    exact hsm.trans (hb.trans hfrac)
  calc (∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime,
        (siftMax (N / p + 1) p : ℝ))
      ≤ ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime, K * (p : ℝ)⁻¹ :=
        sum_le_sum hterm
    _ = K * ∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t')⌋₊ ⌊(N : ℝ) ^ (1 / t)⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
        rw [mul_sum]
    _ ≤ K * (Real.log (t' / t) + δ) := mul_le_mul_of_nonneg_left h4 hK0
    _ = _ := by rw [hK]; ring

lemma bUp_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ bUp σ := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨M, hM⟩ := (eventually_lt_of_limsup_lt (show bUp σ < bUp σ + δ by linarith)
    (bSeq_bdd hσ)).exists
  have := bSeq_nonneg σ M
  exact lt_of_le_of_lt this hM

/-- Telescoping a sum over `Ico (w k) (w 0)` into the bins `Ico (w (i+1)) (w i)`. -/
lemma sum_Ico_antitone_chain (f : ℕ → ℝ) (w : ℕ → ℕ) (hw : Antitone w) (k : ℕ) :
    ∑ p ∈ (Ico (w k) (w 0)).filter Nat.Prime, f p =
      ∑ i ∈ range k, ∑ p ∈ (Ico (w (i + 1)) (w i)).filter Nat.Prime, f p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, sum_filter, sum_filter, sum_filter,
      ← sum_Ico_consecutive _ (hw (Nat.le_succ k)) (hw (Nat.zero_le k)), add_comm]

/-- Bin weights at slack `δ`. -/
noncomputable def binC (s h δ : ℝ) (i : ℕ) : ℝ :=
  (bUp (s + (i + 1) * h - 1 + h) + δ) * (1 + δ) * ((s + i * h) / (s + i * h - 1)) *
    (Real.log ((s + (i + 1) * h) / (s + i * h)) + δ)

/-- **Finite Buchstab, liminf form, at slack `δ`.** -/
theorem aLow_ge_bins_delta {s s' : ℝ} (hs : 2 ≤ s) (hss' : s < s') {k : ℕ} (hk : 0 < k)
    {δ : ℝ} (hδ : 0 < δ) :
    aLow s' - ∑ i ∈ range k, binC s ((s' - s) / k) δ i ≤ aLow s := by
  set h := (s' - s) / k with hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < h := div_pos (by linarith) hkr
  set t : ℕ → ℝ := fun i => s + i * h with ht
  have htk : t k = s' := by simp only [ht, hh]; field_simp; ring
  have ht0 : t 0 = s := by simp [ht]
  have htge : ∀ i, s ≤ t i := fun i => by
    simp only [ht]; have : (0 : ℝ) ≤ i * h := by positivity
    linarith
  have htmono : ∀ i, t i ≤ t (i + 1) := fun i => by simp only [ht]; push_cast; nlinarith
  set C := ∑ i ∈ range k, binC s h δ i with hC
  -- all bins eventually
  have hbins : ∀ᶠ N : ℕ in atTop, ∀ i ∈ range k,
      (∑ p ∈ (Ico ⌊(N : ℝ) ^ (1 / t (i + 1))⌋₊ ⌊(N : ℝ) ^ (1 / t i)⌋₊).filter Nat.Prime,
        (siftMax (N / p + 1) p : ℝ)) ≤ binC s h δ i * (N / Real.log N) := by
    refine (eventually_all_finset _).mpr fun i _ => ?_
    have := eventually_bin_le (t := t i) (t' := t (i + 1)) (σ := t (i + 1) - 1 + h)
      (by linarith [htge i]) (htmono i) (by linarith) hδ
    refine this.mono fun N hN => hN.trans (le_of_eq ?_)
    simp only [binC, ht]; push_cast; ring
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hev := eventually_lt_of_lt_liminf (show aLow s' - ε / 2 < aLow s' by linarith)
    (isBoundedUnder_of ⟨0, aSeq_nonneg s'⟩)
  have key : ∀ᶠ N : ℕ in atTop, aLow s' - ε / 2 - C ≤ aSeq s N := by
    filter_upwards [hbins, hev, eventually_ge_atTop 2] with N hb ha hN2
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hNpos : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos (by linarith)
    set w : ℕ → ℕ := fun i => ⌊(N : ℝ) ^ (1 / t i)⌋₊ with hw
    have hwa : Antitone w := by
      refine antitone_nat_of_succ_le fun i => Nat.floor_le_floor ?_
      exact Real.rpow_le_rpow_of_exponent_le (by linarith)
        (one_div_le_one_div_of_le (by linarith [htge i]) (htmono i))
    have hbuch := siftMin_buchstab N (hwa (Nat.zero_le k))
    have hchain := sum_Ico_antitone_chain (fun p => (siftMax (N / p + 1) p : ℝ)) w hwa k
    have hsum : (∑ p ∈ (Ico (w k) (w 0)).filter Nat.Prime, (siftMax (N / p + 1) p : ℝ)) ≤
        C * (N / Real.log N) := by
      rw [hchain, hC, sum_mul]
      exact sum_le_sum hb
    have hbuchR : (siftMin N (w k) : ℝ) ≤ siftMin N (w 0) +
        ∑ p ∈ (Ico (w k) (w 0)).filter Nat.Prime, (siftMax (N / p + 1) p : ℝ) := by
      exact_mod_cast hbuch
    have hw0 : w 0 = ⌊(N : ℝ) ^ (1 / s)⌋₊ := by simp [hw, ht0]
    have hwk : w k = ⌊(N : ℝ) ^ (1 / s')⌋₊ := by simp only [hw]; rw [htk]
    rw [hw0, hwk] at hbuchR hsum
    have ha' : aLow s' - ε / 2 < aSeq s' N := ha
    unfold aSeq at ha' ⊢
    rw [lt_div_iff₀ hNpos] at ha'
    rw [le_div_iff₀ hNpos]
    have e1 : C * (N / Real.log N) * Real.log N = C * N := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hbuchR hlog.le, mul_le_mul_of_nonneg_right hsum hlog.le]
  have := le_liminf_of_le (aSeq_cobdd (by linarith : (0 : ℝ) < s)) key
  change aLow s' - ε / 2 - C ≤ aLow s at this
  linarith [hε]

/-- **Finite Buchstab, liminf form** (`δ → 0`, `log(1+x) ≤ x`). -/
theorem aLow_ge_bins {s s' : ℝ} (hs : 2 ≤ s) (hss' : s < s') {k : ℕ} (hk : 0 < k) :
    aLow s' - ∑ i ∈ range k, bUp (s + (i + 2) * ((s' - s) / k) - 1) * ((s' - s) / k) /
      (s + i * ((s' - s) / k) - 1) ≤ aLow s := by
  set h := (s' - s) / k with hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < h := div_pos (by linarith) hkr
  have hcont : Continuous (fun δ : ℝ => ∑ i ∈ range k, binC s h δ i) := by
    unfold binC; fun_prop
  have hlim : Tendsto (fun δ : ℝ => ∑ i ∈ range k, binC s h δ i) (𝓝[>] 0)
      (𝓝 (∑ i ∈ range k, binC s h 0 i)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hge : aLow s' - aLow s ≤ ∑ i ∈ range k, binC s h 0 i :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => by
      have := aLow_ge_bins_delta hs hss' hk (δ := δ) hδ
      linarith)
  have hterm : ∀ i ∈ range k, binC s h 0 i ≤
      bUp (s + (i + 2) * h - 1) * h / (s + i * h - 1) := by
    intro i _
    have hi : (0 : ℝ) ≤ i * h := by positivity
    have ht1 : 0 < s + i * h - 1 := by linarith
    have ht0 : 0 < s + i * h := by linarith
    have hb : 0 ≤ bUp (s + (i + 2) * h - 1) := bUp_nonneg (by nlinarith)
    have hlog : Real.log ((s + (i + 1) * h) / (s + i * h)) ≤ h / (s + i * h) := by
      have := Real.log_le_sub_one_of_pos (show 0 < (s + (i + 1) * h) / (s + i * h) by
        apply div_pos <;> nlinarith)
      have e : (s + (i + 1) * h) / (s + i * h) - 1 = h / (s + i * h) := by field_simp; ring
      linarith
    have harg : s + (i + 1) * h - 1 + h = s + (i + 2) * h - 1 := by ring
    unfold binC
    simp only [harg, add_zero, mul_one]
    calc bUp (s + (i + 2) * h - 1) * ((s + i * h) / (s + i * h - 1)) *
          Real.log ((s + (i + 1) * h) / (s + i * h))
        ≤ bUp (s + (i + 2) * h - 1) * ((s + i * h) / (s + i * h - 1)) * (h / (s + i * h)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = bUp (s + (i + 2) * h - 1) * h / (s + i * h - 1) := by field_simp
  have := sum_le_sum hterm
  linarith

end LeanFormalizations.Erdos385.LinearSieve

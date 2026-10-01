/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.LargeValues
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Floor

/-!
# Erdős #385 power saving: `LargeValueBoundP` from a large-value count (phase E9b)

`largeValueBoundP_of_count`: `LargeValueBoundP δ` from
* `LargeValueCount δ`: `1`-separated points `1 ≤ |t| ≤ 8X` with `|P(1+it)| ≥ u ≥ Z^{−η₀}` number
  `≤ C (log Z)^C u^{−1/2}` (the analytic leaf; `NearOneLargeValues` at `P = √Z`);
* `PrimePFloor δ` (proved from Richert in `Floor.lean`): `|P| ≤ K/T₁`, `T₁ = exp((log Z)^{1/4})`.

The near-set integral is `≤ Σ_s 2|P(τ_s)|` (`integral_nearSet_le_sum`), the count of `s` with
`|P(τ_s)| > u` is `≤ 4 C (log Z)^C u^{−1/2}` (`card_filter_le_four_mul`), and the layer cake
(`sum_le_of_count`) gives `≤ 16 C (log Z)^C √(K/T₁) ≤ 1/log² Z`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex LeanFormalizations.Literature Erdos385.Parseval

/-- **Large-value count for the short prime sum** (the analytic leaf).  Believed (70%): with
`√Z·P(1+it) = Σ Λ(n) n^{−it} g₀(n/√Z) + O(Z^{1/4} log Z)` (`primeP_decomp`, `g₀ = cutoffDiv g`
smooth), and the Mellin main term `≪_k |t|^{−k}` (`mellin_one_sub_mul_I_decay`), a point with
`|P| ≥ u = Z^{−η'}` and `|t| ≥ u^{−1/4}` has VK-sum deviation `≥ (√Z)^{1−2η'−o(1)}`, so
`NearOneLargeValues` (`T = 16Z ≤ (√Z)^4·16`) counts them by `≪ Z^{B'η'^{3/2}} log^C Z ≤ u^{−1/2}`
once `η' ≤ η₀ = 1/(16B'²)`; points with `|t| < u^{−1/4}` number `≤ 2u^{−1/4} + 2`. -/
def LargeValueCount (δ : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Admissible δ g → ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop, ∀ u : ℝ,
    Z ^ (-η₀) ≤ u → ∀ T : Finset ℝ, Separated T →
      (∀ t ∈ T, 1 ≤ |t| ∧ |t| ≤ 8 * paramX δ Z ∧ u ≤ ‖primeP g Z (1 + t * I)‖) →
      (T.card : ℝ) ≤ C * Real.log Z ^ C * u ^ (-(1 / 2 : ℝ))

/-- `8 C (log Z)^C ≤ Z^c` eventually. -/
lemma ev_log_rpow_le {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ Z : ℝ in atTop, 8 * C * Real.log Z ^ C ≤ Z ^ c := by
  have h := (isLittleO_log_rpow_rpow_atTop C hc).bound (show (0 : ℝ) < 1 / (8 * C + 1) by
    positivity)
  filter_upwards [h, eventually_ge_atTop 1] with Z hZ hZ1
  have hl : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hZ
  have hz : 0 ≤ Z ^ c := by positivity
  calc 8 * C * Real.log Z ^ C ≤ 8 * C * (1 / (8 * C + 1) * Z ^ c) :=
        mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = 8 * C / (8 * C + 1) * Z ^ c := by ring
    _ ≤ 1 * Z ^ c := by
        apply mul_le_mul_of_nonneg_right _ hz
        rw [div_le_one (by positivity)]; linarith
    _ = Z ^ c := one_mul _

/-- `A (log Z)^{C+2} exp(−(log Z)^{1/4}/2) ≤ 1` eventually. -/
lemma ev_log_exp_le {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∀ᶠ Z : ℝ in atTop,
      A * Real.log Z ^ (C + 2) * Real.exp (-(Real.log Z ^ (1 / 4 : ℝ)) / 2) ≤ 1 := by
  have hy : Tendsto (fun Z : ℝ => Real.log Z ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 * (C + 2)) (1 / 2)
    (by norm_num)).comp hy).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (A + 1) by positivity))
  filter_upwards [h, eventually_ge_atTop 1] with Z hZ hZ1
  have hl : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  simp only [Function.comp] at hZ
  have e : (Real.log Z ^ (1 / 4 : ℝ)) ^ (4 * (C + 2)) = Real.log Z ^ (C + 2) := by
    rw [← Real.rpow_mul hl]; ring_nf
  have e2 : Real.exp (-(1 / 2) * Real.log Z ^ (1 / 4 : ℝ)) =
      Real.exp (-(Real.log Z ^ (1 / 4 : ℝ)) / 2) := by ring_nf
  rw [e, e2] at hZ
  have hpos : 0 ≤ Real.log Z ^ (C + 2) * Real.exp (-(Real.log Z ^ (1 / 4 : ℝ)) / 2) := by
    positivity
  calc A * Real.log Z ^ (C + 2) * Real.exp (-(Real.log Z ^ (1 / 4 : ℝ)) / 2)
      = A * (Real.log Z ^ (C + 2) * Real.exp (-(Real.log Z ^ (1 / 4 : ℝ)) / 2)) := by ring
    _ ≤ (A + 1) * (1 / (A + 1)) := by
        apply mul_le_mul (by linarith) hZ.le hpos (by positivity)
    _ = 1 := by field_simp

/-- `exp((log Z)^{1/4}) + 2 ≤ Z^{c₀}/2` eventually. -/
lemma ev_exp_le_rpow {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∀ᶠ Z : ℝ in atTop, Real.exp (Real.log Z ^ (1 / 4 : ℝ)) + 2 ≤ Z ^ c₀ / 2 := by
  have h34 : Tendsto (fun Z : ℝ => Real.log Z ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [h34.eventually_ge_atTop (2 / c₀), eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by positivity : 0 < c₀ / 2)).eventually_ge_atTop 4] with Z h3 hZ1 h4
  have hZ0 : 0 < Z := by linarith
  have hl : 0 < Real.log Z := Real.log_pos hZ1
  have hsplit : Real.log Z ^ (1 / 4 : ℝ) * Real.log Z ^ (3 / 4 : ℝ) = Real.log Z := by
    rw [← Real.rpow_add hl]; norm_num
  have h14 : Real.log Z ^ (1 / 4 : ℝ) ≤ c₀ / 2 * Real.log Z := by
    have hp : 0 ≤ Real.log Z ^ (1 / 4 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h3 hp
    rw [hsplit] at this
    have e : Real.log Z ^ (1 / 4 : ℝ) * (2 / c₀) = 2 / c₀ * Real.log Z ^ (1 / 4 : ℝ) := by ring
    rw [e] at this
    have e2 : Real.log Z ^ (1 / 4 : ℝ) = c₀ / 2 * (2 / c₀ * Real.log Z ^ (1 / 4 : ℝ)) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hexp : Real.exp (Real.log Z ^ (1 / 4 : ℝ)) ≤ Z ^ (c₀ / 2) := by
    rw [Real.rpow_def_of_pos hZ0]
    exact Real.exp_le_exp.2 (by linarith)
  have hsq : Z ^ c₀ = Z ^ (c₀ / 2) * Z ^ (c₀ / 2) := by
    rw [← Real.rpow_add hZ0]; ring_nf
  rw [hsq]
  nlinarith

lemma sqrt_div_exp {K y : ℝ} (hK : 0 ≤ K) :
    √(K / Real.exp y) = √K * Real.exp (-y / 2) := by
  have h : K / Real.exp y = (√K * Real.exp (-y / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK, ← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  rw [h, Real.sqrt_sq (by positivity)]

set_option maxHeartbeats 1600000 in
/-- **`LargeValueBoundP` from the count and the VK floor.** -/
theorem largeValueBoundP_of_count {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hC : LargeValueCount δ) (hF : PrimePFloor δ) : LargeValueBoundP δ := by
  refine ⟨1, one_pos, fun c₀ hc₀ _ g hg => ?_⟩
  obtain ⟨η₀, C, hη₀, hC0, hcount⟩ := hC g hg
  obtain ⟨K, hK⟩ := hF g hg
  obtain ⟨η, hηdef⟩ : ∃ η, η = min η₀ c₀ := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min hη₀ hc₀
  have hηη₀ : η ≤ η₀ := by rw [hηdef]; exact min_le_left _ _
  have hηc₀ : η ≤ c₀ := by rw [hηdef]; exact min_le_right _ _
  obtain ⟨K', hK'⟩ : ∃ K', K' = |K| + 1 := ⟨_, rfl⟩
  have hK'0 : 0 < K' := by rw [hK']; positivity
  refine ⟨η, hη, ?_⟩
  filter_upwards [hcount, hK, ev_log_rpow_le hC0 (half_pos hc₀),
    ev_log_exp_le (A := 16 * C * √K') (by positivity) hC0, ev_exp_le_rpow hc₀,
    eventually_ge_atTop (16 : ℝ)] with Z hcnt hflr hE1 hE2 hE3 hZ16 S hS hSv
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hX : 1 ≤ paramX δ Z := by unfold paramX; nlinarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log Z := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  rw [← hL] at hE1 hE2 hcnt ⊢
  rw [← hL] at hflr hE3
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = Real.exp (L ^ (1 / 4 : ℝ)) := ⟨_, rfl⟩
  rw [← hT1] at hflr hE3
  have hT10 : 0 < T1 := by rw [hT1]; exact Real.exp_pos _
  -- the count at level `u ≥ Z^{-η}` and the card
  have hZη : Z ^ (-η₀) ≤ Z ^ (-η) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hZη0 : 0 < Z ^ (-η) := by positivity
  have hpowη : (Z ^ (-η)) ^ (-(1 / 2 : ℝ)) = Z ^ (η / 2) := by
    rw [← Real.rpow_mul hZ0.le]; ring_nf
  have hsrange : ∀ s ∈ S, Z ^ c₀ / 2 ≤ |s| ∧ |s| ≤ 7 * paramX δ Z := fun s hs =>
    ⟨(hSv s hs).1, (hSv s hs).2.1⟩
  have hcardS : (S.card : ℝ) ≤ C * L ^ C * Z ^ (η / 2) := by
    rw [← hpowη]
    exact hcnt _ hZη S hS fun s hs => ⟨by linarith [(hsrange s hs).1, hT10],
      by linarith [(hsrange s hs).2], (hSv s hs).2.2.le⟩
  refine ⟨?_, ?_⟩
  · -- the card
    have h1 : Z ^ (η / 2) ≤ Z ^ (c₀ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    have hsq : Z ^ c₀ = Z ^ (c₀ / 2) * Z ^ (c₀ / 2) := by
      rw [← Real.rpow_add hZ0]; ring_nf
    have hCL : 0 ≤ C * L ^ C := by positivity
    calc (S.card : ℝ) ≤ C * L ^ C * Z ^ (η / 2) := hcardS
      _ ≤ C * L ^ C * Z ^ (c₀ / 2) := mul_le_mul_of_nonneg_left h1 hCL
      _ ≤ Z ^ (c₀ / 2) / 8 * Z ^ (c₀ / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Z ^ c₀ / 8 := by rw [hsq]; ring
  · -- the integral
    set w : ℝ → ℝ := fun t => ‖primeP g Z (1 + t * I)‖ with hw
    have hwc : Continuous w := (continuous_primeP g Z).norm
    choose τ hτm hτmax using fun s => exists_max_Icc hwc s
    have hτ1 : ∀ s ∈ S, |τ s - s| ≤ 1 := fun s _ => by
      have := hτm s; rw [Set.mem_Icc] at this; rw [abs_le]; constructor <;> linarith
    have hτabs : ∀ s ∈ S, |s| - 1 ≤ |τ s| ∧ |τ s| ≤ |s| + 1 := fun s hs => by
      have h := hτ1 s hs
      constructor
      · have := abs_sub_abs_le_abs_sub s (τ s); rw [abs_sub_comm] at h; linarith
      · have := abs_sub_abs_le_abs_sub (τ s) s; linarith
    have hτlo : ∀ s ∈ S, T1 ≤ |τ s| := fun s hs => by
      linarith [(hτabs s hs).1, (hsrange s hs).1]
    have hτhi : ∀ s ∈ S, |τ s| ≤ 8 * paramX δ Z := fun s hs => by
      linarith [(hτabs s hs).2, (hsrange s hs).2]
    obtain ⟨V, hV⟩ : ∃ V, V = K' / T1 := ⟨_, rfl⟩
    have hV0 : 0 < V := by rw [hV]; positivity
    have hvV : ∀ s ∈ S, w (τ s) ≤ V := fun s hs => by
      have := hflr (τ s) (hτlo s hs) (hτhi s hs)
      rw [hV]
      refine this.trans (div_le_div_of_nonneg_right ?_ hT10.le)
      rw [hK']; linarith [le_abs_self K]
    have hN : ∀ u, 0 < u → u ≤ V → ((S.filter fun s => u < w (τ s)).card : ℝ) ≤
        (4 * (C * L ^ C)) * u ^ (-(1 / 2 : ℝ)) := by
      intro u hu _
      by_cases hZu : Z ^ (-η) ≤ u
      · have := card_filter_le_four_mul hS τ hτ1 (fun s => u < w (τ s))
          (B := C * L ^ C * u ^ (-(1 / 2 : ℝ))) fun T hT hTm =>
            hcnt u (hZη.trans hZu) T hT fun t ht => by
              obtain ⟨s, hs, rfl, hp⟩ := hTm t ht
              exact ⟨by linarith [hτlo s hs, Real.one_le_exp (show 0 ≤ L ^ (1 / 4 : ℝ) by
                positivity), hT1], hτhi s hs, hp.le⟩
        linarith
      · push_neg at hZu
        have hmono : (Z ^ (-η)) ^ (-(1 / 2 : ℝ)) ≤ u ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hu hZu.le (by norm_num)
        rw [hpowη] at hmono
        have hc1 : ((S.filter fun s => u < w (τ s)).card : ℝ) ≤ S.card := by
          exact_mod_cast Finset.card_filter_le _ _
        have hCL : 0 ≤ C * L ^ C := by positivity
        have : C * L ^ C * Z ^ (η / 2) ≤ C * L ^ C * u ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmono hCL
        have hu0 : 0 ≤ C * L ^ C * u ^ (-(1 / 2 : ℝ)) := by positivity
        linarith
    have hlay := sum_le_of_count S (fun s => w (τ s)) hV0 (fun s _ => norm_nonneg _) hvV hN
    have hint := integral_nearSet_le_sum hwc (fun t => norm_nonneg _) S τ
      fun s _ t ht => hτmax s t ht
    rw [← Finset.mul_sum] at hint
    have hsqV : √V = √K' * Real.exp (-(L ^ (1 / 4 : ℝ)) / 2) := by
      rw [hV, hT1]; exact sqrt_div_exp hK'0.le
    have hLC : L ^ (C + 2) = L ^ C * L ^ 2 := by
      rw [Real.rpow_add (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hL20 : 0 < L ^ 2 := by positivity
    calc (∫ t in nearSet S 1, w t) ≤ 2 * ∑ s ∈ S, w (τ s) := hint
      _ ≤ 2 * (2 * (4 * (C * L ^ C)) * √V) := by linarith
      _ = 16 * C * √K' * L ^ C * Real.exp (-(L ^ (1 / 4 : ℝ)) / 2) := by rw [hsqV]; ring
      _ ≤ 1 / L ^ 2 := by
          rw [le_div_iff₀ hL20]
          calc 16 * C * √K' * L ^ C * Real.exp (-(L ^ (1 / 4 : ℝ)) / 2) * L ^ 2
              = 16 * C * √K' * L ^ (C + 2) * Real.exp (-(L ^ (1 / 4 : ℝ)) / 2) := by
                rw [hLC]; ring
            _ ≤ 1 := hE2

end LeanFormalizations.Erdos385

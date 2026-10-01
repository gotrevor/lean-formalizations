/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import PrimeNumberTheoremAnd.ZetaConj
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.ZeroDetect
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.FiberCount

/-!
# Erdős #385 power saving: `LargeValueCount` from local zero detection (phase E9b)

`largeValueCount_of_zeroDetect`: `LocalZeroDetect` + `NearOneZeroDensity` ⇒ `LargeValueCount δ`.

Route (85%).  `P = √Z`, `u ∈ [Z^{−η₀}, 1]`, `η := log(2/u)/log P` (so `P u/2 = P^{1−η}`,
`η ≤ 2η₀ + log 2/log P ≤ 1/16`).  Points with `|t| < max(R', A P^{η/3} log P)`,
`R' = 2√(Km/u)` (`dev_lower`'s threshold) are `1`-separated in a short interval: `≪ u^{−1/2}`
and `≪ P^{η/3} log P ≤ u^{−1/2} log P`.  Every other point has `‖vkDev‖ ≥ P^{1−η}`
(`dev_lower`), hence (`LocalZeroDetect`) a zero `ρ_t` with `Re ≥ σ := 1 − 2η − A log log P/log P`
and `|Im ρ_t − t| ≤ |t|/2`; replace `ρ_t` by `conj ρ_t` when `t < 0` (`riemannZeta_conj`), so
`0 < Im ≤ 2T`.  Fibres of `t ↦ ρ_t` have `≤ 2(A P^{η/3} log P + 1)` points (`1`-separation),
and `NearOneZeroDensity` at `(σ, 2T)`, `T = 8X ≤ 8Z`, bounds the image by
`C (16Z)^{B(1−σ)^{3/2}} log^C(16Z)`; `(1−σ)^{3/2} ≤ 2(2η)^{3/2} + 2(A log log P/log P)^{3/2}`, the
second term costing `O(1)` in the exponent, the first `P^{O(η^{3/2})} ≤ P^{η/6}` for `η ≤ η₀`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter Complex LeanFormalizations.Literature Erdos385.Parseval

/-- **The density exponent**: with `x = 2η`, `y = A log ℓ/ℓ`, `x + y ≤ s₀²`, `8B s₀ ≤ 1/6`:
`(12P²)^{B(x+y)^{3/2}} ≤ (P^η)^{1/6} ℓ^{4AB}`. -/
lemma zc_density_exp {B A P η y s₀ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hP : 1 < P)
    (hP12 : 12 * P ^ 2 ≤ P ^ 4) (hη : 0 ≤ η) (hy : 0 ≤ y) (hs₀ : 0 ≤ s₀) (hs₀1 : s₀ ≤ 1)
    (hsum : 2 * η + y ≤ s₀ ^ 2) (hBs : 8 * B * s₀ ≤ 1 / 6)
    (hyℓ : y * Real.log P = A * Real.log (Real.log P)) (hℓ : 0 < Real.log P) :
    (12 * P ^ 2) ^ (B * (2 * η + y) ^ ((3 : ℝ) / 2)) ≤
      (P ^ η) ^ ((1 : ℝ) / 6) * Real.log P ^ (4 * A * B) := by
  have hP0 : 0 < P := by linarith
  have hxy : 0 ≤ 2 * η + y := by linarith
  have h32 : (2 * η + y) ^ ((3 : ℝ) / 2) ≤ 2 * η * s₀ + y := by
    have e : (2 * η + y) ^ ((3 : ℝ) / 2) = (2 * η + y) * (2 * η + y) ^ ((1 : ℝ) / 2) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hxy (by norm_num),
        Real.rpow_one]
    have hs : (2 * η + y) ^ ((1 : ℝ) / 2) ≤ s₀ := by
      rw [← Real.sqrt_eq_rpow]
      calc √(2 * η + y) ≤ √(s₀ ^ 2) := Real.sqrt_le_sqrt hsum
        _ = s₀ := Real.sqrt_sq hs₀
    rw [e]
    calc (2 * η + y) * (2 * η + y) ^ ((1 : ℝ) / 2) ≤ (2 * η + y) * s₀ :=
          mul_le_mul_of_nonneg_left hs hxy
      _ = 2 * η * s₀ + y * s₀ := by ring
      _ ≤ 2 * η * s₀ + y := by nlinarith
  have hexp0 : 0 ≤ B * (2 * η + y) ^ ((3 : ℝ) / 2) := by positivity
  calc (12 * P ^ 2) ^ (B * (2 * η + y) ^ ((3 : ℝ) / 2))
      ≤ (P ^ 4) ^ (B * (2 * η + y) ^ ((3 : ℝ) / 2)) :=
        Real.rpow_le_rpow (by positivity) hP12 hexp0
    _ = P ^ (4 * (B * (2 * η + y) ^ ((3 : ℝ) / 2))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; norm_num
    _ ≤ P ^ (4 * (B * (2 * η * s₀ + y))) := by
        apply Real.rpow_le_rpow_of_exponent_le hP.le
        have := mul_le_mul_of_nonneg_left h32 hB
        linarith
    _ = P ^ (8 * B * s₀ * η) * P ^ (4 * B * y) := by
        rw [← Real.rpow_add hP0]; ring_nf
    _ ≤ P ^ (η / 6) * P ^ (4 * B * y) := by
        gcongr
        · exact hP.le
        · nlinarith
    _ = (P ^ η) ^ ((1 : ℝ) / 6) * Real.log P ^ (4 * A * B) := by
        have e1 : P ^ (η / 6) = (P ^ η) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_mul hP0.le]; ring_nf
        have e2 : P ^ (4 * B * y) = Real.log P ^ (4 * A * B) := by
          rw [Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos hℓ]
          congr 1
          have : Real.log P * (4 * B * y) = 4 * B * (y * Real.log P) := by ring
          rw [this, hyℓ]; ring
        rw [e1, e2]

/-- Zeros in a box `σ ≤ Re`, `0 < Im ≤ T'` (`σ ≥ 0`) are finitely many. -/
lemma zeroBox_finite {σ T' : ℝ} (hσ : 0 ≤ σ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T'}.Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1 + T')).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨h0, h1, h2, h3⟩
  refine ⟨?_, h0⟩
  have hre : ρ.re < 1 := by
    by_contra hc; push Not at hc
    exact riemannZeta_ne_zero_of_one_le_re hc h0
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + T' := by rw [abs_of_nonneg (by linarith), abs_of_pos h2]; linarith

set_option maxHeartbeats 2000000 in
/-- **The core count** at a fixed scale `P` and level `u`. -/
lemma zc_count_core {f : ℝ → ℂ} {A Km B C₀ s₀ P u η : ℝ} (hA : 0 ≤ A) (hKm : 0 < Km)
    (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hs₀ : 0 ≤ s₀) (hs₀2 : s₀ ^ 2 ≤ 1 / 2) (hBs : 8 * B * s₀ ≤ 1 / 6)
    (hP : 16 ≤ P) (hP12 : 12 * P ^ 2 ≤ P ^ 4) (hℓ1 : 1 ≤ Real.log P)
    (hlam : 0 ≤ Real.log (Real.log P)) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hη : 0 < η) (hηw : P ^ η = 2 / u)
    (hsum : 2 * η + A * Real.log (Real.log P) / Real.log P ≤ s₀ ^ 2)
    (hdens : ∀ σ T' : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 3 ≤ T' →
      ({ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T'}.ncard : ℝ) ≤
        C₀ * T' ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log T' ^ C₀)
    (hZd : ∀ t : ℝ, |t| ≤ P ^ 4 → A * P ^ (η / 3) * Real.log P ≤ |t| →
      P * u / 2 ≤ ‖vkDev f P t‖ →
      ∃ ρ : ℂ, riemannZeta ρ = 0 ∧
        1 - 2 * η - A * Real.log (Real.log P) / Real.log P ≤ ρ.re ∧
        |ρ.im - t| ≤ A * P ^ (η / 3) * Real.log P / 2)
    {T : Finset ℝ} (hT : Erdos385.Parseval.Separated T)
    (hTt : ∀ t ∈ T, |t| ≤ 8 * P ^ 2 ∧ (4 * Km ≤ u * t ^ 2 → P * u / 2 ≤ ‖vkDev f P t‖)) :
    (T.card : ℝ) ≤ (4 * √Km + 4 * A + 1 + 4 * (A + 1) * C₀ * 4 ^ C₀) *
      Real.log P ^ (1 + 4 * A * B + C₀) * √(1 / u) := by
  classical
  have hP0 : 0 < P := by linarith
  have hP1 : 1 < P := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log P := ⟨_, rfl⟩
  rw [← hℓ] at hℓ1 hlam hsum hZd ⊢
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨y, hy⟩ : ∃ y, y = A * Real.log ℓ / ℓ := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyℓ : y * ℓ = A * Real.log ℓ := by rw [hy]; field_simp
  rw [← hy] at hsum
  -- `p = P^{η/3}`, `v = u^{−1/2}`
  obtain ⟨p, hp⟩ : ∃ p, p = P ^ (η / 3) := ⟨_, rfl⟩
  rw [← hp] at hZd
  have hp1 : 1 ≤ p := by rw [hp]; exact Real.one_le_rpow hP1.le (by positivity)
  obtain ⟨v, hv⟩ : ∃ v, v = √(1 / u) := ⟨_, rfl⟩
  rw [← hv]
  have hv2 : v ^ 2 = 1 / u := by rw [hv, Real.sq_sqrt (by positivity)]
  have hv1 : 1 ≤ v := by
    rw [hv, Real.one_le_sqrt]; rw [le_div_iff₀ hu0]; linarith
  have hp3 : p ^ 3 = 2 / u := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; norm_num; exact hηw
  have hp2v : p ≤ 2 * v := by
    have h : p ^ 3 ≤ (2 * v) ^ 3 := by
      rw [hp3, show 2 / u = 2 * v ^ 2 by rw [hv2]; ring]
      nlinarith [pow_le_pow_right₀ hv1 (show 2 ≤ 3 by norm_num)]
    exact (pow_le_pow_iff_left₀ (by linarith) (by linarith) (by norm_num)).1 h
  obtain ⟨q, hq⟩ : ∃ q, q = (P ^ η) ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  have hpq : p * q ≤ 2 * v := by
    have e : p * q = √(2 / u) := by
      rw [hp, hq, show η / 3 = η * (1 / 3) by ring, Real.rpow_mul hP0.le,
        ← Real.rpow_add (by positivity), hηw, Real.sqrt_eq_rpow]; norm_num
    rw [e, show 2 / u = 2 * (1 / u) by ring, Real.sqrt_mul (by norm_num), ← hv]
    have : √2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  -- the small heights
  obtain ⟨R, hR⟩ : ∃ R, R = max (2 * √Km * v) (A * p * ℓ) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; exact le_max_of_le_left (by positivity)
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, T₁ = T.filter (fun t => |t| ≤ R) := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T₂, T₂ = T.filter (fun t => ¬ |t| ≤ R) := ⟨_, rfl⟩
  have hcard : (T.card : ℝ) = T₁.card + T₂.card := by
    rw [hT₁, hT₂]; exact_mod_cast (Finset.card_filter_add_card_filter_not _).symm
  have h1 : (T₁.card : ℝ) ≤ 2 * R + 1 :=
    sep_card_window (hT₁ ▸ separated_mono (Finset.filter_subset _ _) hT) (c := 0) hR0
      fun t ht => by rw [sub_zero]; rw [hT₁] at ht; exact (Finset.mem_filter.1 ht).2
  -- the zero box
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = 1 - 2 * η - y := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := by rw [hσ]; nlinarith
  have hσ12 : 1 / 2 ≤ σ := by rw [hσ]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
  have hfin := zeroBox_finite (σ := σ) (T' := 12 * P ^ 2) hσ0
  obtain ⟨S, hS⟩ : ∃ S, S = hfin.toFinset := ⟨_, rfl⟩
  have hW0 : 0 ≤ A * p * ℓ / 2 := by positivity
  have h2 : (T₂.card : ℝ) ≤ 2 * (2 * (A * p * ℓ / 2) + 1) * S.card := by
    refine sep_card_fiber' (hT₂ ▸ separated_mono (Finset.filter_subset _ _) hT) hW0
      fun t ht => ?_
    rw [hT₂] at ht
    obtain ⟨htT, htR⟩ := Finset.mem_filter.1 ht
    push Not at htR
    obtain ⟨ht8, hdev⟩ := hTt t htT
    have hKm : 4 * Km ≤ u * t ^ 2 := by
      have h2v : 2 * √Km * v < |t| := lt_of_le_of_lt (by rw [hR]; exact le_max_left _ _) htR
      have hsq : (2 * √Km * v) ^ 2 ≤ |t| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2v.le 2
      rw [mul_pow, mul_pow, Real.sq_sqrt hKm.le, hv2, sq_abs] at hsq
      have := mul_le_mul_of_nonneg_left hsq hu0.le
      rw [show u * (2 ^ 2 * Km * (1 / u)) = 4 * Km by field_simp; ring] at this
      linarith
    have hApl : A * p * ℓ ≤ |t| := (le_max_right _ _).trans (hR ▸ htR.le)
    obtain ⟨ρ, hρ0, hρre, hρim⟩ := hZd t (ht8.trans (by nlinarith)) hApl (hdev hKm)
    have hρre' : σ ≤ ρ.re := by rw [hσ, hy]; linarith
    have htpos : 0 < |t| := lt_of_le_of_lt hR0 htR
    have hW2 : A * p * ℓ / 2 ≤ |t| / 2 := by linarith only [hApl]
    have hP8 : 8 * P ^ 2 ≤ 12 * P ^ 2 := by nlinarith
    rcases le_or_gt 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0] at htpos hW2 ht8 ⊢
      have := abs_le.1 hρim
      refine ⟨ρ, hS ▸ hfin.mem_toFinset.2 ⟨hρ0, hρre', by linarith, by linarith⟩, ?_⟩
      rw [abs_sub_comm]; exact hρim
    · rw [abs_of_neg ht0] at htpos hW2 ht8 ⊢
      have := abs_le.1 hρim
      refine ⟨(starRingEnd ℂ) ρ, hS ▸ hfin.mem_toFinset.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [riemannZeta_conj, hρ0, map_zero]
      · simpa using hρre'
      · simp; linarith
      · simp; linarith
      · simp only [Complex.conj_im]
        rw [abs_le]; constructor <;> linarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  -- the density bound
  have hS1 : (S.card : ℝ) ≤ C₀ * q * ℓ ^ (4 * A * B) * (4 ^ C₀ * ℓ ^ C₀) := by
    have hnc : (S.card : ℝ) = ({ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧
        ρ.im ≤ 12 * P ^ 2}.ncard : ℝ) := by
      rw [hS, Set.ncard_eq_toFinset_card _ hfin]
    have h3 : (3 : ℝ) ≤ 12 * P ^ 2 := by nlinarith
    have hd := hdens σ (12 * P ^ 2) hσ12 hσ1 h3
    rw [show 1 - σ = 2 * η + y by rw [hσ]; ring] at hd
    have hs₀1 : s₀ ≤ 1 := by nlinarith
    have he := zc_density_exp hB hA hP1 hP12 hη.le hy0 hs₀ hs₀1 hsum hBs
      (by rw [← hℓ]; exact hyℓ) (by rw [← hℓ]; exact hℓ0)
    rw [← hq, ← hℓ] at he
    have hl12 : Real.log (12 * P ^ 2) ≤ 4 * ℓ := by
      calc Real.log (12 * P ^ 2) ≤ Real.log (P ^ 4) := Real.log_le_log (by positivity) hP12
        _ = 4 * ℓ := by rw [Real.log_pow, hℓ]; push_cast; ring
    have hl0 : 0 ≤ Real.log (12 * P ^ 2) := Real.log_nonneg (by nlinarith)
    have hlc : Real.log (12 * P ^ 2) ^ C₀ ≤ 4 ^ C₀ * ℓ ^ C₀ := by
      rw [← Real.mul_rpow (by norm_num) hℓ0.le]
      exact Real.rpow_le_rpow hl0 hl12 hC₀
    rw [hnc]
    calc _ ≤ C₀ * (12 * P ^ 2) ^ (B * (2 * η + y) ^ ((3 : ℝ) / 2)) *
          Real.log (12 * P ^ 2) ^ C₀ := hd
      _ ≤ C₀ * (q * ℓ ^ (4 * A * B)) * (4 ^ C₀ * ℓ ^ C₀) := by
          gcongr
      _ = _ := by ring
  -- assembly
  have hRle : R ≤ 2 * √Km * v + A * p * ℓ := by
    rw [hR]; exact max_le (by have : 0 ≤ A * p * ℓ := by positivity
                              linarith) (by have : 0 ≤ 2 * √Km * v := by positivity
                                            linarith)
  obtain ⟨E, hE⟩ : ∃ E, E = 1 + 4 * A * B + C₀ := ⟨_, rfl⟩
  rw [← hE]
  have hE1 : 1 ≤ E := by
    rw [hE]; have : 0 ≤ 4 * A * B := by positivity
    linarith
  have hℓE : ℓ ≤ ℓ ^ E := by
    calc ℓ = ℓ ^ (1 : ℝ) := (Real.rpow_one ℓ).symm
      _ ≤ ℓ ^ E := Real.rpow_le_rpow_of_exponent_le hℓ1 hE1
  have hℓE' : ℓ * ℓ ^ (4 * A * B) * ℓ ^ C₀ = ℓ ^ E := by
    rw [hE, Real.rpow_add hℓ0, Real.rpow_add hℓ0, Real.rpow_one]
  have hT2' : (T₂.card : ℝ) ≤ 4 * (A + 1) * C₀ * 4 ^ C₀ * ℓ ^ E * v := by
    have hc0 : 0 ≤ C₀ * 4 ^ C₀ * ℓ ^ (4 * A * B) * ℓ ^ C₀ := by positivity
    calc (T₂.card : ℝ) ≤ 2 * (2 * (A * p * ℓ / 2) + 1) * S.card := h2
      _ ≤ 2 * ((A + 1) * p * ℓ) * (C₀ * q * ℓ ^ (4 * A * B) * (4 ^ C₀ * ℓ ^ C₀)) := by
          gcongr
          · nlinarith [mul_le_mul hp1 hℓ1 zero_le_one (by linarith : (0:ℝ) ≤ p)]
      _ = 2 * (A + 1) * (p * q) * (C₀ * 4 ^ C₀ * (ℓ * ℓ ^ (4 * A * B) * ℓ ^ C₀)) := by ring
      _ ≤ 2 * (A + 1) * (2 * v) * (C₀ * 4 ^ C₀ * (ℓ * ℓ ^ (4 * A * B) * ℓ ^ C₀)) := by
          gcongr
      _ = 4 * (A + 1) * C₀ * 4 ^ C₀ * ℓ ^ E * v := by rw [hℓE']; ring
  have hT1' : (T₁.card : ℝ) ≤ (4 * √Km + 4 * A + 1) * ℓ ^ E * v := by
    have hApv : A * p * ℓ ≤ 2 * A * ℓ * v := by
      have := mul_le_mul_of_nonneg_left hp2v (by positivity : 0 ≤ A * ℓ)
      nlinarith
    have hv0 : 0 ≤ v := by linarith
    have hK0 : 0 ≤ 4 * √Km + 4 * A + 1 := by positivity
    calc (T₁.card : ℝ) ≤ 2 * R + 1 := h1
      _ ≤ 4 * √Km * v + 4 * A * ℓ * v + 1 := by nlinarith
      _ ≤ (4 * √Km + 4 * A + 1) * ℓ * v := by
          have a1 : 4 * √Km * v ≤ 4 * √Km * ℓ * v := by
            have := mul_le_mul_of_nonneg_left hℓ1 (by positivity : 0 ≤ 4 * √Km * v)
            nlinarith
          have a2 : 1 ≤ ℓ * v := by nlinarith
          nlinarith
      _ ≤ (4 * √Km + 4 * A + 1) * ℓ ^ E * v := by gcongr
  rw [hcard]
  nlinarith

/-- `A log log P + c ≤ ε log P` eventually. -/
lemma ev_loglog_small {A c ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ P : ℝ in atTop, A * Real.log (Real.log P) + c ≤ ε * Real.log P := by
  have hl := Real.tendsto_log_atTop
  have h1 := hl.eventually (Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < ε / (2 * (|A| + 1)) by positivity))
  have h2 := hl.eventually (eventually_ge_atTop (2 * |c| / ε + 1))
  filter_upwards [h1, h2] with P h1 h2
  simp only [id, Real.norm_eq_abs] at h1
  have hℓ0 : 0 < Real.log P := lt_of_lt_of_le (by positivity) h2
  rw [abs_of_pos hℓ0] at h1
  have hA : A * Real.log (Real.log P) ≤ (|A| + 1) * |Real.log (Real.log P)| := by
    calc A * Real.log (Real.log P) ≤ |A * Real.log (Real.log P)| := le_abs_self _
      _ = |A| * |Real.log (Real.log P)| := abs_mul _ _
      _ ≤ _ := by gcongr; linarith
  have hA2 : (|A| + 1) * |Real.log (Real.log P)| ≤ ε / 2 * Real.log P := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ |A| + 1)
    calc _ ≤ _ := this
      _ = ε / 2 * Real.log P := by field_simp
  have hc : c ≤ ε / 2 * Real.log P := by
    have : 2 * |c| / ε ≤ Real.log P := by linarith
    rw [div_le_iff₀ hε] at this
    nlinarith [le_abs_self c]
  linarith

/-- The density hypothesis with nonnegative constants. -/
lemma nearOneZeroDensity_nonneg (h2 : NearOneZeroDensity) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 3 ≤ T →
      ({ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T}.ncard : ℝ) ≤
        C * T ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log T ^ C := by
  obtain ⟨B, C, h⟩ := h2
  refine ⟨|B|, |C|, abs_nonneg _, abs_nonneg _, fun σ T h1 h2 h3 => (h σ T h1 h2 h3).trans ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hl1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3
  have hs : 0 ≤ (1 - σ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have e1 : T ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) ≤ T ^ (|B| * (1 - σ) ^ ((3 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (mul_le_mul_of_nonneg_right (le_abs_self B) hs)
  have e2 : Real.log T ^ C ≤ Real.log T ^ |C| :=
    Real.rpow_le_rpow_of_exponent_le hl1 (le_abs_self C)
  have p1 : 0 ≤ T ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) := by positivity
  have p2 : 0 ≤ Real.log T ^ C := by positivity
  calc C * T ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log T ^ C
      ≤ |C| * (T ^ (B * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log T ^ C) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (T ^ (|B| * (1 - σ) ^ ((3 : ℝ) / 2)) * Real.log T ^ |C|) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- **The large-value count from zeros.** -/
theorem largeValueCount_of_zeroDetect (hZ : LocalZeroDetect) (h2 : NearOneZeroDensity) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) : LargeValueCount δ := by
  intro g hg
  obtain ⟨hs, hcs, hsupp, -, -⟩ := cutoffDiv_facts hδ hδ' hg
  obtain ⟨A, P₀, hA, hZd⟩ := hZ (cutoffDiv g) hs hcs hsupp
  obtain ⟨B, C₀, hB, hC₀, hdens⟩ := nearOneZeroDensity_nonneg h2
  obtain ⟨Km, hKm, hdev⟩ := dev_lower hδ hδ' hg
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, s₀ = 1 / (48 * (B + 1)) := ⟨_, rfl⟩
  have hs₀0 : 0 < s₀ := by rw [hs₀]; positivity
  have hs₀4 : s₀ ≤ 1 / 48 := by
    rw [hs₀, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hBs : 8 * B * s₀ ≤ 1 / 6 := by
    rw [hs₀, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨K, hK⟩ : ∃ K, K = 4 * √Km + 4 * A + 1 + 4 * (A + 1) * C₀ * 4 ^ C₀ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = 1 + 4 * A * B + C₀ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  refine ⟨s₀ ^ 2 / 16, K + E, by positivity, by positivity, ?_⟩
  have hsq := Real.tendsto_sqrt_atTop
  filter_upwards [hdev, hsq.eventually (eventually_ge_atTop (max P₀ 16)),
    hsq.eventually (ev_loglog_small (A := A) (c := 2 * Real.log 2)
      (show 0 < s₀ ^ 2 / 2 by positivity)), eventually_ge_atTop (1 : ℝ)]
    with Z hdevZ hPZ hsmall hZ1 u hu hu1 T hT hTt
  obtain ⟨P, hP⟩ : ∃ P, P = √Z := ⟨_, rfl⟩
  rw [← hP] at hPZ hsmall hdevZ
  have hP16 : 16 ≤ P := le_trans (le_max_right _ _) hPZ
  have hPP₀ : P₀ ≤ P := le_trans (le_max_left _ _) hPZ
  have hP0 : 0 < P := by linarith
  have hZP : Z = P ^ 2 := by rw [hP, Real.sq_sqrt (by linarith)]
  have hℓZ : Real.log Z = 2 * Real.log P := by rw [hZP, Real.log_pow]; push_cast; ring
  have hℓ1 : 1 ≤ Real.log P := by
    rw [Real.le_log_iff_exp_le hP0]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hP16
  have hℓ0 : 0 < Real.log P := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  -- `η`
  obtain ⟨η, hη⟩ : ∃ η, η = Real.log (2 / u) / Real.log P := ⟨_, rfl⟩
  have hηw : P ^ η = 2 / u := by
    rw [Real.rpow_def_of_pos hP0, hη, mul_div_cancel₀ _ hℓ0.ne', Real.exp_log (by positivity)]
  have h2u : 1 < 2 / u := by rw [lt_div_iff₀ hu0]; linarith
  have hη0 : 0 < η := by rw [hη]; exact div_pos (Real.log_pos h2u) hℓ0
  have hlogu : -(s₀ ^ 2 / 16) * Real.log Z ≤ Real.log u := by
    have := Real.log_le_log (by positivity) hu
    rwa [Real.log_rpow (by linarith)] at this
  have hηb : η * Real.log P ≤ s₀ ^ 2 / 8 * Real.log P + Real.log 2 := by
    rw [hη, div_mul_cancel₀ _ hℓ0.ne', Real.log_div (by norm_num) hu0.ne']
    rw [hℓZ] at hlogu; linarith
  have hsm : A * Real.log (Real.log P) + 2 * Real.log 2 ≤ s₀ ^ 2 / 2 * Real.log P := hsmall
  have hsum : 2 * η + A * Real.log (Real.log P) / Real.log P ≤ s₀ ^ 2 := by
    rw [← mul_le_mul_iff_left₀ hℓ0, add_mul, div_mul_cancel₀ _ hℓ0.ne']
    nlinarith
  have hs₀sq : s₀ ^ 2 ≤ 1 / 48 ^ 2 := by
    have := pow_le_pow_left₀ hs₀0.le hs₀4 2; linarith [this]
  have hη16 : η ≤ 1 / 16 := by
    have : 0 ≤ A * Real.log (Real.log P) / Real.log P := by
      have : 0 ≤ Real.log (Real.log P) := Real.log_nonneg hℓ1
      positivity
    linarith
  have hlam : 0 ≤ Real.log (Real.log P) := Real.log_nonneg hℓ1
  have hPu : P ^ (1 - η) = P * u / 2 := by
    rw [Real.rpow_sub hP0, Real.rpow_one, hηw]; field_simp
  have hu8 : Z ^ (-(1 / 8 : ℝ)) ≤ u :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by nlinarith)) hu
  have hcore := zc_count_core (f := cutoffDiv g) (T := T) hA hKm hB hC₀ hs₀0.le
    (by nlinarith) hBs hP16 (by nlinarith [mul_le_mul hP16 hP16 (by norm_num) hP0.le, sq_nonneg P]) hℓ1 hlam hu0 hu1 hη0 hηw hsum hdens
    (fun t ht4 htA hdv => hZd P η t hPP₀ hη0 hη16 ht4 htA (hPu ▸ hdv)) hT
    (fun t ht => by
      obtain ⟨-, ht8, hut⟩ := hTt t ht
      refine ⟨?_, fun hk => ?_⟩
      · have : paramX δ Z ≤ Z := by
          unfold paramX; nlinarith
        rw [← hZP]; linarith
      · have := hdevZ u hu8 t hk hut
        exact this)
  rw [← hK, ← hE] at hcore
  have hlZ1 : 1 ≤ Real.log Z := by rw [hℓZ]; linarith
  have hu' : √(1 / u) = u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow zero_le_one hu0.le, Real.one_rpow,
      Real.rpow_neg hu0.le, one_div]
  rw [hu'] at hcore
  have hv0 : 0 ≤ u ^ (-(1 / 2 : ℝ)) := by positivity
  have hlog : Real.log P ^ E ≤ Real.log Z ^ (K + E) :=
    calc Real.log P ^ E ≤ Real.log Z ^ E :=
          Real.rpow_le_rpow hℓ0.le (by rw [hℓZ]; linarith) hE0
      _ ≤ Real.log Z ^ (K + E) := Real.rpow_le_rpow_of_exponent_le hlZ1 (by linarith)
  calc (T.card : ℝ) ≤ K * Real.log P ^ E * u ^ (-(1 / 2 : ℝ)) := hcore
    _ ≤ (K + E) * Real.log Z ^ (K + E) * u ^ (-(1 / 2 : ℝ)) := by
        gcongr; linarith

end LeanFormalizations.Erdos385

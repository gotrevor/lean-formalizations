/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.NearSet
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.Cover
import LeanFormalizations.NumberTheory.Erdos385.PowerSaving.SupSplit

/-!
# Erdős #385 power saving: `NearSetLeaf` from a large-value bound (phase E9b)

`nearSetLeaf_of_largeValueBound`: `NearSetLeaf δ` follows from `LargeValueBound δ`, a statement
about `1`-separated sets `S` of large values of the short prime sum (`|P(1+is)| > Z^{−η}`,
`Z^{c₀}/2 ≤ |s| ≤ 7X`): they number `≤ Z^{c₀}/8`, and `A` has `L¹` mass `≤ 1/log³ Z` on their
unit neighbourhoods.

Combinatorics: `exists_separated_cover` gives a maximal separated set of large values; by
pigeonhole one of the `≈ Z^{c₀}/4` length-`2` windows `[Z^{c₀}/2 + 2k, Z^{c₀}/2 + 2k + 2)` holds no
`|s|`, and `T₀` is its midpoint; then the large values at `|t| ≥ T₀` are covered by the `s` with
`|s| ≥ T₀ + 1`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex LeanFormalizations.Literature Erdos385.Parseval

/-- **Large values of the short prime sum** (the analytic leaf).  Believed (65%): the count is
`NearOneLargeValues` at `P = √Z`, `T = 16Z`, threshold `(√Z)^{1−2η}` (the main term
`mellin·P^{1−it}` is negligible for `|t| ≥ Z^{c₀}/2`), so `≪ Z^{B(2η)^{3/2}} log^C Z ≤ Z^{c₀}/8`
once `η ≪ c₀^{2/3}`; the `L¹` bound by levels `|P| ≈ Z^{−η'}`, `η' ≥ (log Z)^{−2/3−ε}` (VK), each
level contributing `≪ Z^{B(2η')^{3/2} − η'} log^C Z`, summable. -/
def LargeValueBound (δ : ℝ) : Prop :=
  ∃ cmax : ℝ, 0 < cmax ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cmax → ∀ g : ℝ → ℝ, Admissible δ g →
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ Z : ℝ in atTop, ∀ S : Finset ℝ, Separated S →
      (∀ s ∈ S, Z ^ c₀ / 2 ≤ |s| ∧ |s| ≤ 7 * paramX δ Z ∧
        Z ^ (-η) < ‖primeP g Z (1 + s * I)‖) →
      (S.card : ℝ) ≤ Z ^ c₀ / 8 ∧
      (∫ t in nearSet S 1, ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖) ≤
        1 / Real.log Z ^ 3

lemma mem_nearSet_iff {S : Finset ℝ} {t : ℝ} : t ∈ nearSet S 1 ↔ ∃ s ∈ S, |t - s| ≤ 1 := by
  simp only [nearSet, Set.mem_iUnion, Set.mem_Icc, exists_prop, abs_le]
  constructor <;> rintro ⟨s, hs, h1, h2⟩ <;> exact ⟨s, hs, by linarith, by linarith⟩

/-- Pigeonhole: `K` windows of length `2` above `a`, fewer than `K` points ⇒ an empty window. -/
lemma exists_empty_window (S : Finset ℝ) (a : ℝ) (K : ℕ) (hK : S.card < K) :
    ∃ k : ℕ, k < K ∧ ∀ s ∈ S, a ≤ |s| → ¬ (a + 2 * k ≤ |s| ∧ |s| < a + 2 * k + 2) := by
  classical
  set idx : ℝ → ℕ := fun s => ⌊(|s| - a) / 2⌋₊
  have hlt : (S.image idx).card < (Finset.range K).card := by
    rw [Finset.card_range]; exact (Finset.card_image_le).trans_lt hK
  obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨k, Finset.mem_range.1 hk, fun s hs ha ⟨h1, h2⟩ => hkn ?_⟩
  refine Finset.mem_image.2 ⟨s, hs, ?_⟩
  simp only [idx]
  rw [Nat.floor_eq_iff (by linarith)]
  constructor <;> linarith

theorem nearSetLeaf_of_largeValueBound {δ : ℝ} (hL : LargeValueBound δ) : NearSetLeaf δ := by
  obtain ⟨m, hm, hL⟩ := hL
  refine ⟨m, hm, fun c₀ hc₀ hc₀m g hg => ?_⟩
  obtain ⟨η, hη, hev⟩ := hL c₀ hc₀ hc₀m g hg
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, (tendsto_rpow_atTop hc₀).eventually_ge_atTop 64] with Z hZ hZc
  classical
  set a := Z ^ c₀ / 2 with ha
  let E : Set ℝ := {t | a ≤ |t| ∧ |t| ≤ 7 * paramX δ Z ∧ Z ^ (-η) < ‖primeP g Z (1 + t * I)‖}
  obtain ⟨S, hSE, hSs, hcov⟩ := exists_separated_cover (E := E) (R := 7 * paramX δ Z)
    fun t ht => ht.2.1
  have hcard := (hZ S hSs fun s hs => hSE hs).1
  -- windows
  set K := ⌊Z ^ c₀ / 4⌋₊ - 1 with hKdef
  have hK4 : Z ^ c₀ / 4 - 2 < (K : ℝ) := by
    have h1 := Nat.lt_floor_add_one (Z ^ c₀ / 4)
    have h2 : 1 ≤ ⌊Z ^ c₀ / 4⌋₊ := Nat.le_floor (by norm_num; linarith)
    rw [hKdef, Nat.cast_sub h2]; push_cast; linarith
  have hKle : (K : ℝ) ≤ Z ^ c₀ / 4 - 1 := by
    have h1 := Nat.floor_le (show 0 ≤ Z ^ c₀ / 4 by linarith)
    have h2 : 1 ≤ ⌊Z ^ c₀ / 4⌋₊ := Nat.le_floor (by norm_num; linarith)
    rw [hKdef, Nat.cast_sub h2]; push_cast; linarith
  have hSK : S.card < K := by
    have : (S.card : ℝ) < K := by linarith
    exact_mod_cast this
  obtain ⟨k, hk, hempty⟩ := exists_empty_window S a K hSK
  have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
  set T₀ := a + 2 * k + 1 with hT₀
  set S' := S.filter fun s => T₀ + 1 ≤ |s| with hS'
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨T₀, by linarith, by linarith, S', fun s hs => (Finset.mem_filter.1 hs).2,
    (hZ S' (fun s hs s' hs' h => hSs s (hS'S hs) s' (hS'S hs') h)
      fun s hs => hSE (hS'S hs)).2, fun t ht1 ht2 htn => ?_⟩
  by_contra hP
  push_neg at hP
  have htE : t ∈ E := ⟨by linarith, ht2, hP⟩
  obtain ⟨s, hs, hts⟩ := mem_nearSet_iff.1 (hcov htE)
  apply htn
  refine mem_nearSet_iff.2 ⟨s, Finset.mem_filter.2 ⟨hs, ?_⟩, hts⟩
  by_contra hlt
  push_neg at hlt
  have hsE := hSE hs
  have h1 : |t| ≤ |s| + 1 := by
    have := abs_sub_abs_le_abs_sub t s; linarith
  exact hempty s hs hsE.1 ⟨by linarith, by linarith⟩

end LeanFormalizations.Erdos385

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex LeanFormalizations.Literature Erdos385.Parseval

/-- `|Q(1+it)| ≤ 1`: at most `2δ√Z + 1` primes `q ≥ √Z`, each contributing `1/q ≤ 1/√Z`. -/
theorem norm_primeQ_le {δ Z : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 4 ≤ Z) (t : ℝ) :
    ‖primeQ δ Z (1 + t * I)‖ ≤ 1 := by
  classical
  have hs2 : 2 ≤ √Z := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hZ
  have hs0 : 0 < √Z := by linarith
  set N := ⌊(1 + 2 * δ) * √Z⌋₊
  set F := (Finset.range (N + 1)).filter (fun q : ℕ => q.Prime ∧ √Z ≤ (q : ℝ))
  have hterm : ∀ q ∈ F, ‖((q : ℂ) ^ (-(1 + t * I)))‖ ≤ 1 / √Z := by
    intro q hq
    have hq' := (Finset.mem_filter.1 hq).2
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq'.1.pos
    rw [Complex.norm_natCast_cpow_of_pos hq'.1.pos]
    simp only [neg_add_rev, add_re, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, neg_zero, one_re, zero_add]
    rw [Real.rpow_neg_one, ← one_div]
    exact one_div_le_one_div_of_le hs0 hq'.2
  have hF : F ⊆ Finset.Icc ⌈√Z⌉₊ N := by
    intro q hq
    have h := Finset.mem_filter.1 hq
    exact Finset.mem_Icc.2 ⟨Nat.ceil_le.2 h.2.2, Nat.lt_succ_iff.1 (Finset.mem_range.1 h.1)⟩
  have hcard : (F.card : ℝ) ≤ √Z / 2 + 1 := by
    have h1 := Finset.card_le_card hF
    rw [Nat.card_Icc] at h1
    by_cases hc : ⌈√Z⌉₊ ≤ N + 1
    · have : (F.card : ℝ) ≤ (N : ℝ) + 1 - ⌈√Z⌉₊ := by
        have := (Nat.cast_le (α := ℝ)).2 h1
        rw [Nat.cast_sub hc] at this; push_cast at this; linarith
      have hN : (N : ℝ) ≤ (1 + 2 * δ) * √Z := Nat.floor_le (by positivity)
      have hc' : √Z ≤ (⌈√Z⌉₊ : ℝ) := Nat.le_ceil _
      nlinarith
    · have : F.card = 0 := by omega
      rw [this]; push_cast; linarith
  calc ‖primeQ δ Z (1 + t * I)‖ ≤ ∑ q ∈ F, ‖((q : ℂ) ^ (-(1 + t * I)))‖ := norm_sum_le _ _
    _ ≤ F.card * (1 / √Z) := by
        have := Finset.sum_le_card_nsmul F _ _ hterm
        rwa [nsmul_eq_mul] at this
    _ ≤ (√Z / 2 + 1) * (1 / √Z) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 1 := by
        have e : (√Z / 2 + 1) * (1 / √Z) = 1 / 2 + 1 / √Z := by field_simp
        rw [e]
        have : 1 / √Z ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hs2
        linarith

end LeanFormalizations.Erdos385

namespace LeanFormalizations.Erdos385

open Real Filter MeasureTheory Complex LeanFormalizations.Literature Erdos385.Parseval

/-- **`LargeValueBound` for `P` alone** (the remaining analytic leaf): the near-set `L¹` mass of
the short prime sum `P` itself is `≤ 1/log² Z`.  Same confidence and route as `LargeValueBound`. -/
def LargeValueBoundP (δ : ℝ) : Prop :=
  ∃ cmax : ℝ, 0 < cmax ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cmax → ∀ g : ℝ → ℝ, Admissible δ g →
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ Z : ℝ in atTop, ∀ S : Finset ℝ, Separated S →
      (∀ s ∈ S, Z ^ c₀ / 2 ≤ |s| ∧ |s| ≤ 7 * paramX δ Z ∧
        Z ^ (-η) < ‖primeP g Z (1 + s * I)‖) →
      (S.card : ℝ) ≤ Z ^ c₀ / 8 ∧
      (∫ t in nearSet S 1, ‖primeP g Z (1 + t * I)‖) ≤ 1 / Real.log Z ^ 2

lemma isCompact_nearSet (S : Finset ℝ) (r : ℝ) : IsCompact (nearSet S r) :=
  S.isCompact_biUnion fun _ _ => isCompact_Icc

/-- `|A| ≤ |P|/log Z` (from `A = PQ/log Z`, `|Q| ≤ 1`) reduces `LargeValueBound` to `P`. -/
theorem largeValueBound_of_P {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (h : LargeValueBoundP δ) :
    LargeValueBound δ := by
  obtain ⟨m, hm, h⟩ := h
  refine ⟨m, hm, fun c₀ hc₀ hc₀m g hg => ?_⟩
  obtain ⟨η, hη, hev⟩ := h c₀ hc₀ hc₀m g hg
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (16 : ℝ)] with Z hZ hZ16 S hS hSv
  obtain ⟨hcard, hint⟩ := hZ S hS hSv
  refine ⟨hcard, ?_⟩
  have hZ1 : 1 < Z := by linarith
  have hlog : 1 ≤ Real.log Z := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hl0 : 0 < Real.log Z := by linarith
  have hK := isCompact_nearSet S 1
  have hA : ∀ t : ℝ, ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ ≤
      ‖primeP g Z (1 + t * I)‖ / Real.log Z := fun t => by
    rw [show (fun m ↦ (coeffA δ g Z m : ℂ)) = coeffC δ g Z from rfl,
      LSeries_coeffC_eq hδ hδ' hZ1 hg, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hl0.le]
    gcongr
    calc _ ≤ ‖primeP g Z (1 + t * I)‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_primeQ_le hδ hδ' (by linarith) t) (norm_nonneg _)
      _ = _ := mul_one _
  have hAc : Continuous fun t : ℝ => ‖LSeries (fun m ↦ (coeffA δ g Z m : ℂ)) (1 + t * I)‖ := by
    have := (continuous_normA_sq hδ hδ' hZ1 hg).sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hPc : Continuous fun t : ℝ => ‖primeP g Z (1 + t * I)‖ / Real.log Z :=
    (continuous_primeP g Z).norm.div_const _
  calc _ ≤ ∫ t in nearSet S 1, ‖primeP g Z (1 + t * I)‖ / Real.log Z :=
        setIntegral_mono_on (hAc.continuousOn.integrableOn_compact hK)
          (hPc.continuousOn.integrableOn_compact hK) (measurableSet_nearSet S 1)
          fun t _ => hA t
    _ = (∫ t in nearSet S 1, ‖primeP g Z (1 + t * I)‖) / Real.log Z := integral_div _ _
    _ ≤ 1 / Real.log Z ^ 2 / Real.log Z := by gcongr
    _ = 1 / Real.log Z ^ 3 := by field_simp

end LeanFormalizations.Erdos385

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.Rate
import LeanFormalizations.NumberTheory.Erdos385.RateVK.General

/-!
# Erdős #385: the rate at a general exponent (phase E3d helper)

Copies of `Rate.lean`'s `badWindow_rate`, `sqrt_le_rate`, `almost_all_F385_rate` at scale
`(log ·)^a`, `0 < a < 1/3`, over the `Gen` pipeline.
-/

open Real Filter LeanFormalizations.Literature

namespace LeanFormalizations.Erdos385.Gen

open LeanFormalizations.Erdos385

variable {a : ℝ} [hA0 : Fact (0 < a)] [hA1 : Fact (a < 1 / 3)]
include hA0 hA1

/-- `(log Z)^4 exp(−c (log Z)^a) → 0`. -/
theorem tendsto_log_pow_four_mul_exp {c : ℝ} (hc : 0 < c) :
    Tendsto (fun Z : ℝ => Real.log Z ^ 4 * Real.exp (-c * Real.log Z ^ a)) atTop (nhds 0) := by
  have ha := hA0.out
  have hu : Tendsto (fun Z : ℝ => Real.log Z ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / a) c hc).comp hu).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Z hZ
  simp only [Function.comp]
  congr 1
  rw [← Real.rpow_mul (Real.log_nonneg hZ), show a * (4 / a) = ((4 : ℕ) : ℝ) by field_simp; norm_num,
    Real.rpow_natCast]

/-- **Per-window rate.** -/
theorem badWindow_rate (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT)
    (h3 : VKZeroFreeLogDeriv) (h4 : PNTExp a) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ A : ℝ, 0 < A ∧ ∃ Z₁ : ℝ, 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
      ((badWindow δ Z).ncard : ℝ) ≤ A * Z * Real.exp (-c' * Real.log Z ^ a) := by
  obtain ⟨g, hg⟩ := exists_admissible hδ hδ'
  obtain ⟨κ₀, hκ₀, hW2'⟩ := longAverage_lower h4 hδ hδ'
  have hκ : 0 < min κ₀ 1 := lt_min hκ₀ one_pos
  obtain ⟨c₁, hc₁, hlong⟩ := hW2' (min κ₀ 1) hκ (min_le_left _ _) g hg
  obtain ⟨C, hvar⟩ := variance_small (a := a) h1 h2 (smoothPrimeSumVK_of_VKZ h3) h4 hδ hδ' hκ
    (min_le_right _ _) hg
  have hbad := card_badWindow_le (a := a) hδ hδ' hκ (min_le_right _ _) hg
  set κ := min κ₀ 1
  have hε := tendsto_log_pow_four_mul_exp (a := a) (show 0 < κ / 4 by positivity)
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.1 (hbad.and (hlong.and (hvar.and
    ((hε.eventually (eventually_lt_nhds one_pos)).and (eventually_gt_atTop 1)))))
  refine ⟨κ / 4, by positivity, |2 * C / (c₁ * δ) ^ 2| + 1, by positivity, max Z₁ 1,
    le_max_right _ _, fun Z hZ => ?_⟩
  obtain ⟨hb, hl, hv, hε', hZ⟩ := hZ₁ Z ((le_max_left _ _).trans hZ)
  have hlZ : 0 < Real.log Z := Real.log_pos hZ
  set μ := c₁ * δ / Real.log Z ^ 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hb' := hb μ hμ0 hl
  have hD0 : 0 ≤ variance a δ κ g Z := by
    unfold variance
    have : 0 < paramX δ Z := by unfold paramX; nlinarith
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hX : paramX δ Z ≤ Z := by unfold paramX; nlinarith
  have hX0 : 0 ≤ paramX δ Z := by unfold paramX; nlinarith
  set e := Real.exp (-(κ / 2) * Real.log Z ^ a)
  set e4 := Real.exp (-(κ / 4) * Real.log Z ^ a)
  have hee : e = e4 * e4 := by
    simp only [e, e4, ← Real.exp_add]; congr 1; ring
  have hCe : 0 ≤ C * e := hD0.trans hv
  have hL4 : Real.log Z ^ 4 * e ≤ e4 := by
    rw [hee, ← mul_assoc]
    have : 0 < e4 := Real.exp_pos _
    nlinarith
  have hL40 : 0 ≤ Real.log Z ^ 4 * e := by positivity
  calc ((badWindow δ Z).ncard : ℝ) ≤ 2 * paramX δ Z * variance a δ κ g Z / μ ^ 2 := hb'
    _ ≤ 2 * Z * (C * e) / μ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := mul_le_mul hX hv hD0 (by linarith)
        linarith
    _ = Z * (2 * C / (c₁ * δ) ^ 2 * (Real.log Z ^ 4 * e)) := by
        rw [hμ]; field_simp
    _ ≤ Z * ((|2 * C / (c₁ * δ) ^ 2| + 1) * e4) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc 2 * C / (c₁ * δ) ^ 2 * (Real.log Z ^ 4 * e)
            ≤ |2 * C / (c₁ * δ) ^ 2| * (Real.log Z ^ 4 * e) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hL40
          _ ≤ (|2 * C / (c₁ * δ) ^ 2| + 1) * e4 :=
              mul_le_mul (by linarith) hL4 hL40 (by positivity)
    _ = (|2 * C / (c₁ * δ) ^ 2| + 1) * Z * e4 := by ring

/-- `√X ≤ e · X exp(−c (log X)^{1/10})` for `c ≤ 1/2`, `X ≥ 1`: the `√X`-size head is absorbed. -/
theorem sqrt_le_rate {c X : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 2) (hX : 1 ≤ X) :
    √X ≤ Real.exp 1 * (X * Real.exp (-c * Real.log X ^ a)) := by
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpow : Real.log X ^ a ≤ 1 + Real.log X := by
    rcases le_total (Real.log X) 1 with h | h
    · have := Real.rpow_le_one hL h (by linarith [hA0.out] : (0 : ℝ) ≤ a); linarith
    · have := Real.rpow_le_rpow_of_exponent_le h (by linarith [hA1.out] : a ≤ 1)
      rw [Real.rpow_one] at this; linarith
  have hp0 : 0 ≤ Real.log X ^ a := Real.rpow_nonneg hL _
  have hX0 : 0 < X := by linarith
  have hsq : Real.exp (Real.log X / 2) = √X := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]; ring_nf
  set u := Real.exp (c * Real.log X ^ a)
  have hu : u ≤ Real.exp (1 / 2) * √X := by
    rw [← hsq, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have hΦ : Real.exp (-c * Real.log X ^ a) * u = 1 := by
    rw [← Real.exp_add]; simp
  have hs0 : 0 < √X := Real.sqrt_pos.2 hX0
  have hss : √X * √X = X := Real.mul_self_sqrt hX0.le
  set Φ := Real.exp (-c * Real.log X ^ a)
  have hΦ0 : 0 < Φ := Real.exp_pos _
  have h1 : √X * √X ≤ (X * Φ * Real.exp (1 / 2)) * √X := by
    have : X = X * Φ * u := by rw [mul_assoc, hΦ, mul_one]
    calc √X * √X = X * Φ * u := by rw [hss]; exact this
      _ ≤ X * Φ * (Real.exp (1 / 2) * √X) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = _ := by ring
  have h2 := le_of_mul_le_mul_right h1 hs0
  have h3 : Real.exp (1 / 2) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ X * Φ by positivity)]

/-- **Theorem A with a rate** (exponent `1/10`, from `MediumPNT`). -/
theorem almost_all_F385_rate (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT)
    (h3 : VKZeroFreeLogDeriv) (h4 : PNTExp a) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * X * Real.exp (-c * Real.log X ^ a) := by
  classical
  obtain ⟨c', hc', A, hA, Z₁, hZ₁1, hwin⟩ := badWindow_rate h1 h2 h3 h4 hδ hδ'
  obtain ⟨N₀, hcov⟩ := card_le_of_windows hδ hδ' Z₁
  set c := min (c' / 2) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  refine ⟨c, hc0, (3 + N₀) * Real.exp 1 + A * (1 + 4 / δ), fun X hX => ?_⟩
  set E : Set ℕ := {n | (F n : ℝ) < n + (1 - δ) * √n} with hE
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hX0 : (0 : ℝ) < X := by linarith
  set Φ := Real.exp (-c * Real.log X ^ a) with hΦ
  have hkey := sqrt_le_rate (a := a) hc0.le (min_le_right _ _) hXr
  rw [← hΦ] at hkey
  have hs1 : 1 ≤ √X := by rw [Real.one_le_sqrt]; exact hXr
  have hXΦ : 0 ≤ X * Φ := by positivity
  have hrest : 0 ≤ A * (1 + 4 / δ) * X * Φ := by positivity
  show (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤ _
  by_cases hXN : X < N₀
  · have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆ ↑(Finset.range (X + 1)) := fun n hn => by
      simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_succ_of_le hn.1
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_range] at this
    have hc : (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤ N₀ := by exact_mod_cast (by omega)
    have : (N₀ : ℝ) ≤ N₀ * √X := le_mul_of_one_le_right (by positivity) hs1
    have : (N₀ : ℝ) * √X ≤ N₀ * (Real.exp 1 * (X * Φ)) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    nlinarith [Real.exp_pos 1]
  push Not at hXN
  set E' : Set ℕ := {n | n ∈ E ∧ 2 * √X ≤ n} with hE'
  set η := A * Real.exp (-c' * Real.log √X ^ a) with hη
  have hη0 : 0 < η := by positivity
  have hlsX : 0 ≤ Real.log √X := Real.log_nonneg hs1
  have hW : ∀ Z : ℝ, Z₁ ≤ Z →
      ({n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℝ) ≤ η * Z := by
    intro Z hZ
    have hZ0 : 0 < Z := by linarith
    by_cases hZs : Z < √X
    · have : {n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z} = ∅ := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hE']
        rintro ⟨⟨_, h2⟩, _, h3⟩
        nlinarith
      rw [this, Set.ncard_empty, Nat.cast_zero]; positivity
    · push Not at hZs
      have hsub : {n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z} ⊆
          badWindow δ Z := fun n ⟨⟨hn, _⟩, h1, h2⟩ => ⟨h1, h2, hn⟩
      have hfin : (badWindow δ Z).Finite :=
        (Set.finite_Iic ⌊(1 + δ / 2) * Z⌋₊).subset fun n hn => by
          simp only [Set.mem_Iic]; exact Nat.le_floor hn.2.1
      have h1 : ((({n : ℕ | n ∈ E' ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℕ)
          : ℝ)) ≤ (badWindow δ Z).ncard := by exact_mod_cast Set.ncard_le_ncard hsub hfin
      have hlog : Real.log √X ≤ Real.log Z := Real.log_le_log (by linarith) hZs
      have hrp : Real.log √X ^ a ≤ Real.log Z ^ a :=
        Real.rpow_le_rpow hlsX hlog (by linarith [hA0.out])
      have hexp : Real.exp (-c' * Real.log Z ^ a) ≤
          Real.exp (-c' * Real.log √X ^ a) :=
        Real.exp_le_exp.2 (by nlinarith)
      calc _ ≤ ((badWindow δ Z).ncard : ℝ) := h1
        _ ≤ A * Z * Real.exp (-c' * Real.log Z ^ a) := hwin Z hZ
        _ ≤ A * Z * Real.exp (-c' * Real.log √X ^ a) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = η * Z := by rw [hη]; ring
  have hcnt := hcov E' η hη0 hW X hXN
  -- η ≤ A Φ
  have hηΦ : η ≤ A * Φ := by
    rw [hη, hΦ]
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.exp_le_exp.2
    have hL : 0 ≤ Real.log X := Real.log_nonneg hXr
    rw [Real.log_sqrt hX0.le, Real.div_rpow hL (by norm_num)]
    have h2 : (2 : ℝ) ^ a ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith [hA1.out] : a ≤ 1)
      rwa [Real.rpow_one] at this
    have h2p : 0 < (2 : ℝ) ^ a := by positivity
    set p := Real.log X ^ a
    have hp : 0 ≤ p := Real.rpow_nonneg hL _
    have hq : p / 2 ≤ p / (2 : ℝ) ^ a := div_le_div_of_nonneg_left hp h2p h2
    have hcc : c ≤ c' / 2 := min_le_left _ _
    have : c * p ≤ c' * (p / 2) := by nlinarith
    nlinarith
  -- split off the head `n < 2√X`
  have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆
      ↑(Finset.range ⌈2 * √X⌉₊) ∪ {n : ℕ | n ≤ X ∧ n ∈ E'} := by
    intro n ⟨hnX, hnE⟩
    by_cases hn : (n : ℝ) < 2 * √X
    · left; simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.lt_ceil.2 hn
    · right; push Not at hn; exact ⟨hnX, hnE, hn⟩
  have hfin2 : {n : ℕ | n ≤ X ∧ n ∈ E'}.Finite :=
    (Set.finite_Iic X).subset fun n hn => hn.1
  have hA1 := Set.ncard_le_ncard hsub ((Finset.finite_toSet _).union hfin2)
  have hA2 := Set.ncard_union_le (↑(Finset.range ⌈2 * √X⌉₊) : Set ℕ) {n : ℕ | n ≤ X ∧ n ∈ E'}
  rw [Set.ncard_coe_finset, Finset.card_range] at hA2
  have hceil : (⌈2 * √X⌉₊ : ℝ) ≤ 2 * √X + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have htot : (({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℕ) : ℝ) ≤
      ⌈2 * √X⌉₊ + ({n : ℕ | n ≤ X ∧ n ∈ E'}.ncard : ℝ) := by
    exact_mod_cast hA1.trans hA2
  have hηX : η * (1 + 4 / δ) * X ≤ A * (1 + 4 / δ) * X * Φ := by
    have : η * ((1 + 4 / δ) * X) ≤ A * Φ * ((1 + 4 / δ) * X) :=
      mul_le_mul_of_nonneg_right hηΦ (by positivity)
    linarith
  have hN : (3 + (N₀ : ℝ)) * √X ≤ (3 + N₀) * (Real.exp 1 * (X * Φ)) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hN' : 2 * √X + 1 + (N₀ : ℝ) ≤ (3 + N₀) * √X := by
    have : (0 : ℝ) ≤ N₀ := by positivity
    nlinarith
  nlinarith

end LeanFormalizations.Erdos385.Gen

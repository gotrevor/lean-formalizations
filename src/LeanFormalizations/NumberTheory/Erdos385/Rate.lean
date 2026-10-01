/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.AlmostAll

/-!
# Erdős #385: a rate for the almost-all theorem (phase E3c)

One frozen statement, `almost_all_F385_rate`: under the same four literature inputs as
`almost_all_F385`, for each `δ ∈ (0, 1/4)`,
`#{n ≤ X : F(n) < n + (1 − δ)√n} ≤ C X exp(−c (log X)^{1/10})`.

The exponent `1/10` is what the E3 pieces give as they stand: `variance_small` saves
`exp(−(κ/2)(log Z)^{1/10})`, inherited from `MediumPNTStatement`.  The source argument
(`DOOR-ALMOSTALL-ERDOS-385.md`, check (3)) gives `1/3 − ε` once the long-range average uses
Vinogradov–Korobov strength; that is a later phase, not this one.

## Route (DONE 2026-10-01: `card_le_of_windows` + `badWindow_rate` + `sqrt_le_rate`; the head
`n < 2√X` is split off so one uniform window rate `A exp(−c'(log √X)^{1/10})` covers the rest)

1. Fix `g` from `exists_admissible`, then `κ := min κ₀ 1` and `c₁` from `longAverage_lower`,
   and `C` from `variance_small h1 h2 (smoothPrimeSumVK_of_VKZ h3) h4` (copy the opening of
   `almost_all_F385`).
2. Per window: `card_badWindow_le` with `μ = c₁ δ / log² Z` gives, eventually in `Z`,
   `#badWindow δ Z ≤ 2 paramX δ Z · C exp(−(κ/2) L^{1/10}) · L⁴ / (c₁δ)²` with `L = log Z`,
   hence `≤ C' Z exp(−(κ/4) L^{1/10})` for `Z ≥ Z₀` (absorb `L⁴`, and `paramX δ Z ≤ 2Z`).
3. Cover: the windows `[Z + paramH δ Z, (1 + δ/2) Z]` at `Z_k = Z₀ (1 + δ/4)^k` overlap
   (because `paramH δ Z = o(Z)`) and cover every `n ≥ N₀`.  Reuse the covering lemma inside
   `tendsto_density_zero_of_windows` if it is exposed; otherwise prove the covering directly.
4. Sum: windows with `Z_k ≤ √X` contribute at most `√X + O(1)` in total (crude count).  Windows
   with `√X < Z_k ≤ X` have `log Z_k ≥ (log X)/2`, so each is
   `≤ C' Z_k exp(−(κ/4) 2^{−1/10} (log X)^{1/10})`, and `Σ_{Z_k ≤ X} Z_k ≤ (4/δ + 1) X`
   (geometric).  Take `c = (κ/4) 2^{−1/10}/2` so that `√X ≤ X exp(−c (log X)^{1/10})` for
   large `X`.
5. Small `X` (below the eventual thresholds): the count is `≤ X + 1`, and
   `exp(−c (log X)^{1/10})` is bounded below on a bounded range; enlarge `C`.

If step 3 stalls, state the covering as a NAMED sub-lemma with a disclosed hole plus an English
paragraph and a confidence; that is an acceptable finish.

Frozen: this statement, every statement in `AlmostAll.lean`, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Real Filter LeanFormalizations.Literature

/-- **Uniform covering count.**  For fixed `Z₁` there is one `N₀`, independent of the set `E` and
of `η`, such that window bounds `≤ η Z` for all `Z ≥ Z₁` give
`#{n ≤ X : n ∈ E} ≤ N₀ + η (1 + 4/δ) X`.
(The counting half of `tendsto_density_zero_of_windows`, with the uniformity made explicit.) -/
theorem card_le_of_windows {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (Z₁ : ℝ) :
    ∃ N₀ : ℕ, ∀ (E : Set ℕ) (η : ℝ), 0 < η →
      (∀ Z : ℝ, Z₁ ≤ Z →
        ({n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℝ) ≤ η * Z) →
      ∀ X : ℕ, N₀ ≤ X → ({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℝ) ≤ N₀ + η * (1 + 4 / δ) * X := by
  classical
  set r : ℝ := 1 + δ / 4 with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  set Z₀ : ℝ := max Z₁ (max 16 (4 / δ)) with hZ₀
  have hZ₀16 : 16 ≤ Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hZ₀δ : 1 ≤ Z₀ * (δ / 4) := by
    have : 4 / δ ≤ Z₀ := (le_max_right _ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hδ] at this; linarith
  set Zs : ℕ → ℝ := fun j => Z₀ * r ^ j with hZs
  have hZs_ge : ∀ j, Z₀ ≤ Zs j := fun j => le_mul_of_one_le_right (by linarith)
    (one_le_pow₀ hr1.le)
  have hZs_succ : ∀ j, Zs (j + 1) = r * Zs j := fun j => by simp only [hZs, pow_succ]; ring
  have hZs_big : ∀ j : ℕ, (j : ℝ) ≤ Zs j := fun j => by
    have h1 : 1 + (j : ℝ) * (δ / 4) ≤ r ^ j := by
      rw [hr]; exact one_add_mul_le_pow (by linarith) j
    have : (j : ℝ) ≤ Z₀ * (1 + j * (δ / 4)) := by nlinarith
    exact this.trans (mul_le_mul_of_nonneg_left h1 (by linarith))
  have hH0 : ∀ Z : ℝ, 0 ≤ paramH δ Z := fun Z => by unfold paramH; positivity
  set N₀ : ℕ := ⌈Z₀ + paramH δ Z₀⌉₊ with hN₀
  refine ⟨N₀, fun E η hη hZ₁ => ?_⟩
  set W : ℝ → Set ℕ := fun Z => {n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}
  have hWfin : ∀ Z, (W Z).Finite := fun Z =>
    (Set.finite_Iic ⌊(1 + δ / 2) * Z⌋₊).subset fun n hn => by
      simp only [Set.mem_Iic]; exact Nat.le_floor hn.2.2
  set P : ℕ → ℕ → Prop := fun X j => Zs j + paramH δ (Zs j) ≤ X with hP
  have hcover : ∀ X n : ℕ, n ∈ E → N₀ ≤ n → n ≤ X →
      ∃ j ≤ Nat.findGreatest (P X) X, n ∈ W (Zs j) := by
    intro X n hnE hn hnX
    set j := Nat.findGreatest (P n) n with hj
    have hP0 : P n 0 := by
      simp only [hP, hZs, pow_zero, mul_one]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hPj : P n j := Nat.findGreatest_spec (Nat.zero_le n) hP0
    have hjn : j ≤ n := Nat.findGreatest_le n
    refine ⟨j, Nat.le_findGreatest (hjn.trans hnX) ((show (P n j) from hPj).trans
      (by exact_mod_cast hnX)), hnE, hPj, ?_⟩
    by_contra hcon
    push Not at hcon
    have hstep := window_step hδ hδ' ((show (2 : ℝ) ≤ 16 by norm_num).trans
      (hZ₀16.trans (hZs_ge j)))
    rw [← hZs_succ] at hstep
    have hPj1 : P n (j + 1) := by simp only [hP]; linarith
    by_cases hj1 : j + 1 ≤ n
    · exact Nat.findGreatest_is_greatest (by omega) hj1 hPj1
    · have := hZs_big (j + 1)
      have : Zs (j + 1) ≤ n := le_trans (le_add_of_nonneg_right (hH0 _)) hPj1
      have : (n : ℝ) < (j + 1 : ℕ) := by exact_mod_cast (by omega : n < j + 1)
      linarith
  intro X hX
  set J := Nat.findGreatest (P X) X
  have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆ Set.Iio N₀ ∪ ⋃ j ∈ Finset.range (J + 1), W (Zs j) := by
    intro n ⟨hnX, hnE⟩
    by_cases hn : n < N₀
    · exact Or.inl hn
    · obtain ⟨j, hj, hW'⟩ := hcover X n hnE (by omega) hnX
      exact Or.inr (Set.mem_biUnion (Finset.mem_range.2 (by omega)) hW')
  have hfin : (Set.Iio N₀ ∪ ⋃ j ∈ Finset.range (J + 1), W (Zs j)).Finite :=
    (Set.finite_Iio N₀).union (Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => hWfin _)
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_union_le (Set.Iio N₀) (⋃ j ∈ Finset.range (J + 1), W (Zs j))
  have h3 := Finset.set_ncard_biUnion_le (Finset.range (J + 1)) (fun j => W (Zs j))
  have hN : (Set.Iio N₀).ncard = N₀ := by
    rw [show Set.Iio N₀ = ↑(Finset.range N₀) by ext; simp, Set.ncard_coe_finset,
      Finset.card_range]
  have hsumW : (∑ j ∈ Finset.range (J + 1), ((W (Zs j)).ncard : ℝ)) ≤
      ∑ j ∈ Finset.range (J + 1), η * Zs j :=
    Finset.sum_le_sum fun j _ => hZ₁ (Zs j) ((le_max_left _ _).trans (hZs_ge j))
  have hgeom : ∑ j ∈ Finset.range (J + 1), Zs j ≤ r * Zs J / (r - 1) := by
    simp only [hZs]
    rw [← Finset.mul_sum, geom_sum_eq hr1.ne', ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : 0 ≤ Z₀ := by linarith
    rw [pow_succ]
    nlinarith [pow_pos (show 0 < r by linarith) J]
  have hJX : Zs J ≤ X := by
    have hP0 : P X 0 := by
      simp only [hP, hZs, pow_zero, mul_one]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hX)
    have := Nat.findGreatest_spec (Nat.zero_le X) hP0
    exact le_trans (le_add_of_nonneg_right (hH0 _)) this
  have hcast : ((⋃ j ∈ Finset.range (J + 1), W (Zs j)).ncard : ℝ) ≤
      ∑ j ∈ Finset.range (J + 1), ((W (Zs j)).ncard : ℝ) := by exact_mod_cast h3
  have hrr : r / (r - 1) = 1 + 4 / δ := by
    rw [hr, show 1 + δ / 4 - 1 = δ / 4 by ring]; field_simp; ring
  have : η * (r * Zs J / (r - 1)) ≤ η * (1 + 4 / δ) * X := by
    rw [mul_div_right_comm, hrr, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJX (by positivity)) hη.le
  calc ({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℝ)
      ≤ ((Set.Iio N₀ ∪ ⋃ j ∈ Finset.range (J + 1), W (Zs j)).ncard : ℝ) := by exact_mod_cast h1
    _ ≤ (Set.Iio N₀).ncard + ((⋃ j ∈ Finset.range (J + 1), W (Zs j)).ncard : ℝ) := by
        exact_mod_cast h2
    _ ≤ N₀ + η * (r * Zs J / (r - 1)) := by
        rw [hN]
        have := hsumW.trans_eq (Finset.mul_sum _ _ _).symm
        have := mul_le_mul_of_nonneg_left hgeom hη.le
        linarith
    _ ≤ N₀ + η * (1 + 4 / δ) * X := by linarith

/-- **Per-window rate.** -/
theorem badWindow_rate (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT)
    (h3 : VKZeroFreeLogDeriv) (h4 : MediumPNTStatement) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ A : ℝ, 0 < A ∧ ∃ Z₁ : ℝ, 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
      ((badWindow δ Z).ncard : ℝ) ≤ A * Z * Real.exp (-c' * Real.log Z ^ ((1 : ℝ) / 10)) := by
  obtain ⟨g, hg⟩ := exists_admissible hδ hδ'
  obtain ⟨κ₀, hκ₀, hW2'⟩ := longAverage_lower h4 hδ hδ'
  have hκ : 0 < min κ₀ 1 := lt_min hκ₀ one_pos
  obtain ⟨c₁, hc₁, hlong⟩ := hW2' (min κ₀ 1) hκ (min_le_left _ _) g hg
  obtain ⟨C, hvar⟩ := variance_small h1 h2 (smoothPrimeSumVK_of_VKZ h3) h4 hδ hδ' hκ
    (min_le_right _ _) hg
  have hbad := card_badWindow_le hδ hδ' hκ (min_le_right _ _) hg
  set κ := min κ₀ 1
  have hε := tendsto_log_pow_four_mul_exp (show 0 < κ / 4 by positivity)
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.1 (hbad.and (hlong.and (hvar.and
    ((hε.eventually (eventually_lt_nhds one_pos)).and (eventually_gt_atTop 1)))))
  refine ⟨κ / 4, by positivity, |2 * C / (c₁ * δ) ^ 2| + 1, by positivity, max Z₁ 1,
    le_max_right _ _, fun Z hZ => ?_⟩
  obtain ⟨hb, hl, hv, hε', hZ⟩ := hZ₁ Z ((le_max_left _ _).trans hZ)
  have hlZ : 0 < Real.log Z := Real.log_pos hZ
  set μ := c₁ * δ / Real.log Z ^ 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hb' := hb μ hμ0 hl
  have hD0 : 0 ≤ variance δ κ g Z := by
    unfold variance
    have : 0 < paramX δ Z := by unfold paramX; nlinarith
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hX : paramX δ Z ≤ Z := by unfold paramX; nlinarith
  have hX0 : 0 ≤ paramX δ Z := by unfold paramX; nlinarith
  set e := Real.exp (-(κ / 2) * Real.log Z ^ ((1 : ℝ) / 10))
  set e4 := Real.exp (-(κ / 4) * Real.log Z ^ ((1 : ℝ) / 10))
  have hee : e = e4 * e4 := by
    simp only [e, e4, ← Real.exp_add]; congr 1; ring
  have hCe : 0 ≤ C * e := hD0.trans hv
  have hL4 : Real.log Z ^ 4 * e ≤ e4 := by
    rw [hee, ← mul_assoc]
    have : 0 < e4 := Real.exp_pos _
    nlinarith
  have hL40 : 0 ≤ Real.log Z ^ 4 * e := by positivity
  calc ((badWindow δ Z).ncard : ℝ) ≤ 2 * paramX δ Z * variance δ κ g Z / μ ^ 2 := hb'
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
    √X ≤ Real.exp 1 * (X * Real.exp (-c * Real.log X ^ ((1 : ℝ) / 10))) := by
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpow : Real.log X ^ ((1 : ℝ) / 10) ≤ 1 + Real.log X := by
    rcases le_total (Real.log X) 1 with h | h
    · have := Real.rpow_le_one hL h (by norm_num : (0 : ℝ) ≤ 1 / 10); linarith
    · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) / 10 ≤ 1)
      rw [Real.rpow_one] at this; linarith
  have hp0 : 0 ≤ Real.log X ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hL _
  have hX0 : 0 < X := by linarith
  have hsq : Real.exp (Real.log X / 2) = √X := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]; ring_nf
  set u := Real.exp (c * Real.log X ^ ((1 : ℝ) / 10))
  have hu : u ≤ Real.exp (1 / 2) * √X := by
    rw [← hsq, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have hΦ : Real.exp (-c * Real.log X ^ ((1 : ℝ) / 10)) * u = 1 := by
    rw [← Real.exp_add]; simp
  have hs0 : 0 < √X := Real.sqrt_pos.2 hX0
  have hss : √X * √X = X := Real.mul_self_sqrt hX0.le
  set Φ := Real.exp (-c * Real.log X ^ ((1 : ℝ) / 10))
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
    (h3 : VKZeroFreeLogDeriv) (h4 : MediumPNTStatement) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ({n : ℕ | n ≤ X ∧ (F n : ℝ) < n + (1 - δ) * Real.sqrt n}.ncard : ℝ) ≤
        C * X * Real.exp (-c * Real.log X ^ ((1 : ℝ) / 10)) := by
  classical
  obtain ⟨c', hc', A, hA, Z₁, hZ₁1, hwin⟩ := badWindow_rate h1 h2 h3 h4 hδ hδ'
  obtain ⟨N₀, hcov⟩ := card_le_of_windows hδ hδ' Z₁
  set c := min (c' / 2) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  refine ⟨c, hc0, (3 + N₀) * Real.exp 1 + A * (1 + 4 / δ), fun X hX => ?_⟩
  set E : Set ℕ := {n | (F n : ℝ) < n + (1 - δ) * √n} with hE
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hX0 : (0 : ℝ) < X := by linarith
  set Φ := Real.exp (-c * Real.log X ^ ((1 : ℝ) / 10)) with hΦ
  have hkey := sqrt_le_rate hc0.le (min_le_right _ _) hXr
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
  set η := A * Real.exp (-c' * Real.log √X ^ ((1 : ℝ) / 10)) with hη
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
      have hrp : Real.log √X ^ ((1 : ℝ) / 10) ≤ Real.log Z ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow hlsX hlog (by norm_num)
      have hexp : Real.exp (-c' * Real.log Z ^ ((1 : ℝ) / 10)) ≤
          Real.exp (-c' * Real.log √X ^ ((1 : ℝ) / 10)) :=
        Real.exp_le_exp.2 (by nlinarith)
      calc _ ≤ ((badWindow δ Z).ncard : ℝ) := h1
        _ ≤ A * Z * Real.exp (-c' * Real.log Z ^ ((1 : ℝ) / 10)) := hwin Z hZ
        _ ≤ A * Z * Real.exp (-c' * Real.log √X ^ ((1 : ℝ) / 10)) :=
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
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 : ℝ) / 10 ≤ 1)
      rwa [Real.rpow_one] at this
    have h2p : 0 < (2 : ℝ) ^ ((1 : ℝ) / 10) := by positivity
    set p := Real.log X ^ ((1 : ℝ) / 10)
    have hp : 0 ≤ p := Real.rpow_nonneg hL _
    have hq : p / 2 ≤ p / (2 : ℝ) ^ ((1 : ℝ) / 10) := div_le_div_of_nonneg_left hp h2p h2
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

end LeanFormalizations.Erdos385

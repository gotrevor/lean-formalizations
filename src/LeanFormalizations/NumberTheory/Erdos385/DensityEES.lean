/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385VK
import LeanFormalizations.NumberTheory.Erdos385.Landau

/-!
# Erdős–Eggleton–Selfridge for almost all `n` (phase E7, new mathematics)

formal-conjectures `ErdosProblems/385.lean` records, as `erdos_385.variants.lb`, the guess of
Erdős, Eggleton and Selfridge that `F(n) ≥ n + (1 − o(1))√n` for **all** `n`, and proves
`trivial_ub : F n ≤ n + √n`.  The all-`n` guess meets the parity barrier.  This file proves it
off a set of density zero, assuming only Richert's bound (the base of `Landau.lean`), and draws the
two corollaries:

* `density_one_EES`: `∃ e = o(1)` and a density-zero `E` with `n + (1 − e n)√n ≤ F n` for `n ∉ E`;
* `F_sub_div_sqrt_tendsto_one`: `(F n − n)/√n → 1` along the complement of a density-zero set
  (with the trivial upper bound `F_le_add_sqrt`), so `F(n) − n ∼ √n` for almost all `n`;
* `F_sub_tendsto_atTop`: the density-one form of `erdos_385.parts.ii`.

## Route (85%): diagonalize `almost_all_F385_of_richert` over `δ → 0`

1. **Trivial upper bound** `F_le_add_sqrt`: every composite `m < n` has `minFac m ^ 2 ≤ m`
   (`Nat.minFac_sq_le_self`), so `m + minFac m ≤ m + √m ≤ n + √n` (monotone in `m`); `sSup` of
   the empty set is `0`.  Prove it here (do not copy formal-conjectures' text).
2. **Diagonal.**  Put `δ_k = 1/(k+5)` and `B_k = {n : F n < n + (1 − δ_k)√n}`; `B_k ⊆ B_{k+1}`.
   By `almost_all_F385_of_richert h δ_k`, choose `X_0 < X_1 < …` with
   `#{n ≤ X : n ∈ B_k}/X ≤ 2^{-k}` for all `X ≥ X_k` (also `X_{k+1} ≥ 2^k X_k`, harmless).  Let
   `k(n) = max{k : X_k ≤ n}` (`0` below `X_0`), `e n = δ_{k(n)}` and `E = {n : n ∈ B_{k(n)}}`.
   Then `e → 0` (`k(n) → ∞`), and for `X_k ≤ X < X_{k+1}`:
   `#{n ≤ X : n ∈ E} ≤ X_{k'} + #{n ≤ X : n ∈ B_{k}}` for the fixed `k' = k − K`, which is
   `≤ X_{k−K} + 2^{-k} X`; choose `K` first, then `k` large, to get density `→ 0`.  (Any standard
   diagonal works; a cleaner one: `E ∩ [X_j, X_{j+1}) ⊆ B_j`, so `#{n ≤ X : n ∈ E} ≤
   Σ_{j ≤ k} #{n ≤ min(X, X_{j+1}) : n ∈ B_j}`, bounded by `X_J + Σ_{J ≤ j ≤ k} 2^{-j} X`.)
   `e =o[atTop] 1` from `Tendsto e atTop (𝓝 0)` (`Asymptotics.isLittleO_one_iff`).
3. **Corollaries.**  For `n ∉ E`: `(1 − e n) ≤ (F n − n)/√n ≤ 1`; squeeze along `atTop ⊓ 𝓟 Eᶜ`.
   Then `F n − n ≥ (1 − e n)√n → ∞`.

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: these statements, every earlier statement, and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open Filter Asymptotics LeanFormalizations.Literature

/-- `E ⊆ ℕ` has natural density zero. -/
def DensityZero (E : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => ({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℝ) / X) atTop (nhds 0)

/-- The trivial upper bound `F n ≤ n + √n` (formal-conjectures `Erdos385.trivial_ub`). -/
theorem F_le_add_sqrt (n : ℕ) : (F n : ℝ) ≤ n + Real.sqrt n := by
  have hN : F n ≤ n + Nat.sqrt n := by
    unfold F
    apply csSup_le'
    rintro x ⟨m, hm, hc, rfl⟩
    have h1 : m.minFac ≤ Nat.sqrt m :=
      Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) hc.2)
    have h2 : Nat.sqrt m ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hm.le
    omega
  have h3 : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have : (F n : ℝ) ≤ ((n + Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hN
  push_cast at this
  linarith

/-- The diagonal core: a gauge `e → 0` and a density-zero exceptional set. -/
private theorem density_core (h : RichertZetaGrowth) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (nhds 0) ∧ (∀ n, 0 ≤ e n) ∧ ∃ E : Set ℕ, DensityZero E ∧
      ∀ n, n ∉ E → (n : ℝ) + (1 - e n) * Real.sqrt n ≤ F n := by
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 5) with hδ
  set B : ℕ → Set ℕ := fun k => {n | (F n : ℝ) < n + (1 - δ k) * Real.sqrt n} with hB
  have hBmono : ∀ {k K : ℕ}, k ≤ K → B k ⊆ B K := by
    intro k K hkK n hn
    simp only [hB, Set.mem_setOf_eq] at hn ⊢
    have : δ K ≤ δ k := by
      simp only [hδ]
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (by omega : k + 5 ≤ K + 5)
    have := Real.sqrt_nonneg n
    nlinarith
  have hA := almost_all_F385_of_richert h
  have hT : ∀ k : ℕ, ∃ T : ℕ, ∀ X ≥ T,
      ({n : ℕ | n ≤ X ∧ n ∈ B k}.ncard : ℝ) / X < 1 / ((k : ℝ) + 1) := by
    intro k
    have hk := hA (δ k) (by simp only [hδ]; positivity)
      (by simp only [hδ]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
            [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    have := (hk.eventually (gt_mem_nhds (show (0:ℝ) < 1 / ((k : ℝ) + 1) by positivity)))
    exact eventually_atTop.mp this
  choose T hT using hT
  set Y : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup T with hY
  have hYT : ∀ k, T k ≤ Y k := fun k => Finset.le_sup (f := T) (Finset.self_mem_range_succ k)
  have hYmono : Monotone Y := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  set κ : ℕ → ℕ := fun n => Nat.findGreatest (fun k => Y k ≤ n) n with hκ
  have hκmono : Monotone κ := by
    intro a b hab
    exact Nat.findGreatest_mono (fun k (hk : Y k ≤ a) => le_trans hk hab) hab
  have hκspec : ∀ X, Y 0 ≤ X → Y (κ X) ≤ X := fun X hX =>
    Nat.findGreatest_spec (P := fun k => Y k ≤ X) (Nat.zero_le X) hX
  have hκtop : Tendsto κ atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun K => ⟨max K (Y K), fun X hX => ?_⟩
    exact Nat.le_findGreatest (le_of_max_le_left hX) (le_of_max_le_right hX)
  have hκR : Tendsto (fun n => ((κ n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hκtop
  refine ⟨fun n => δ (κ n), ?_, fun n => by simp only [hδ]; positivity,
    {n | n ∈ B (κ n)}, ?_, ?_⟩
  · simp only [hδ]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ hκR)
  · unfold DensityZero
    have hup : Tendsto (fun X : ℕ => 1 / (((κ X : ℕ) : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ hκR)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun X => by positivity) ?_
    filter_upwards [eventually_ge_atTop (Y 0)] with X hX
    have hsub : {n : ℕ | n ≤ X ∧ n ∈ {n | n ∈ B (κ n)}} ⊆ {n : ℕ | n ≤ X ∧ n ∈ B (κ X)} := by
      rintro n ⟨hnX, hn⟩
      exact ⟨hnX, hBmono (hκmono hnX) hn⟩
    have hfin : {n : ℕ | n ≤ X ∧ n ∈ B (κ X)}.Finite :=
      (Set.finite_Iic X).subset fun n hn => hn.1
    have hc := Set.ncard_le_ncard hsub hfin
    have hc' : ({n : ℕ | n ≤ X ∧ n ∈ {n | n ∈ B (κ n)}}.ncard : ℝ) ≤
        ({n : ℕ | n ≤ X ∧ n ∈ B (κ X)}.ncard : ℝ) := by exact_mod_cast hc
    have hlt := hT (κ X) X (le_trans (hYT _) (hκspec X hX))
    have hXnn : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    calc _ ≤ ({n : ℕ | n ≤ X ∧ n ∈ B (κ X)}.ncard : ℝ) / X :=
          div_le_div_of_nonneg_right hc' hXnn
      _ ≤ _ := hlt.le
  · intro n hn
    simp only [Set.mem_setOf_eq, hB, not_lt] at hn
    exact hn

/-- **Erdős–Eggleton–Selfridge off a density-zero set** (`erdos_385.variants.lb` with `∀ n`
weakened to `∀ n ∉ E`, `E` of density zero), from Richert's bound. -/
theorem density_one_EES (h : RichertZetaGrowth) :
    ∃ e : ℕ → ℝ, e =o[atTop] (1 : ℕ → ℝ) ∧ ∃ E : Set ℕ, DensityZero E ∧
      ∀ n, n ∉ E → (n : ℝ) + (1 - e n) * Real.sqrt n ≤ F n := by
  obtain ⟨e, he, -, E, hE, hEe⟩ := density_core h
  exact ⟨e, (Asymptotics.isLittleO_one_iff ℝ).mpr he, E, hE, hEe⟩

/-- `F(n) − n ∼ √n` for almost all `n`. -/
theorem F_sub_div_sqrt_tendsto_one (h : RichertZetaGrowth) :
    ∃ E : Set ℕ, DensityZero E ∧
      Tendsto (fun n : ℕ => ((F n : ℝ) - n) / Real.sqrt n) (atTop ⊓ 𝓟 Eᶜ) (nhds 1) := by
  obtain ⟨e, he, -, E, hE, hEe⟩ := density_core h
  refine ⟨E, hE, ?_⟩
  have hlow : Tendsto (fun n => 1 - e n) (atTop ⊓ 𝓟 Eᶜ) (nhds 1) := by
    simpa using (tendsto_const_nhds.sub he).mono_left (inf_le_left (b := 𝓟 Eᶜ))
  have hev : ∀ᶠ n in atTop ⊓ 𝓟 Eᶜ, n ∉ E ∧ 1 ≤ n :=
    Filter.Eventually.and (mem_inf_of_right (mem_principal_self Eᶜ))
      (mem_inf_of_left (eventually_ge_atTop 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with n ⟨hnE, hn1⟩
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
    rw [le_div_iff₀ hs]; linarith [hEe n hnE]
  · filter_upwards [hev] with n ⟨_, hn1⟩
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
    rw [div_le_iff₀ hs]; linarith [F_le_add_sqrt n]

/-- The density-one form of `erdos_385.parts.ii`: `F(n) − n → ∞` off a density-zero set. -/
theorem F_sub_tendsto_atTop (h : RichertZetaGrowth) :
    ∃ E : Set ℕ, DensityZero E ∧
      Tendsto (fun n : ℕ => (F n : ℝ) - n) (atTop ⊓ 𝓟 Eᶜ) atTop := by
  obtain ⟨e, he, -, E, hE, hEe⟩ := density_core h
  refine ⟨E, hE, ?_⟩
  have hlow : Tendsto (fun n => 1 - e n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub he
  have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hprod := (hlow.pos_mul_atTop one_pos hsq).mono_left (inf_le_left (b := 𝓟 Eᶜ))
  refine tendsto_atTop_mono' _ ?_ hprod
  filter_upwards [(mem_inf_of_right (mem_principal_self Eᶜ) :
    ∀ᶠ n in atTop ⊓ 𝓟 Eᶜ, n ∉ E)] with n hnE
  have := hEe n hnE
  show (1 - e n) * Real.sqrt n ≤ (F n : ℝ) - n
  linarith

end LeanFormalizations.Erdos385

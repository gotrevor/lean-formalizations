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
  sorry

/-- **Erdős–Eggleton–Selfridge off a density-zero set** (`erdos_385.variants.lb` with `∀ n`
weakened to `∀ n ∉ E`, `E` of density zero), from Richert's bound. -/
theorem density_one_EES (h : RichertZetaGrowth) :
    ∃ e : ℕ → ℝ, e =o[atTop] (1 : ℕ → ℝ) ∧ ∃ E : Set ℕ, DensityZero E ∧
      ∀ n, n ∉ E → (n : ℝ) + (1 - e n) * Real.sqrt n ≤ F n := by
  sorry

/-- `F(n) − n ∼ √n` for almost all `n`. -/
theorem F_sub_div_sqrt_tendsto_one (h : RichertZetaGrowth) :
    ∃ E : Set ℕ, DensityZero E ∧
      Tendsto (fun n : ℕ => ((F n : ℝ) - n) / Real.sqrt n) (atTop ⊓ 𝓟 Eᶜ) (nhds 1) := by
  sorry

/-- The density-one form of `erdos_385.parts.ii`: `F(n) − n → ∞` off a density-zero set. -/
theorem F_sub_tendsto_atTop (h : RichertZetaGrowth) :
    ∃ E : Set ℕ, DensityZero E ∧
      Tendsto (fun n : ℕ => (F n : ℝ) - n) (atTop ⊓ 𝓟 Eᶜ) atTop := by
  sorry

end LeanFormalizations.Erdos385

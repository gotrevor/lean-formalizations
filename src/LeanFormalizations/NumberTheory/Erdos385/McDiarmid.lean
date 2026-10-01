/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385Exceptional
import LeanFormalizations.NumberTheory.Erdos385.McDiarmid.Core

/-!
# McDiarmid's inequality on a finite product (phase E4b)

One frozen statement, `mcDiarmidFinite_holds : McDiarmidFinite`.  It removes one of the three
literature inputs of the E4 exceptional-set bound (`Exceptional.lean`).

**DONE 2026-10-01**, axiom-clean.  As built: `McDiarmid/Hoeffding.lean` (mathlib's Hoeffding
lemma on `PMF.uniformOfFintype`), `McDiarmid/Core.lean` (`f_s x := avg_z f (s.piecewise z x)`,
averaging over the whole product; the one combinatorial fact is that swapping coordinate `i`
between two points is an involution of `Ω × Ω`), then Chernoff with `λ = −4t/Σc²` here.

## Route (85%): exponential moment by induction over coordinates, then Chernoff

Everything is a finite average, so avoid filtrations; work with `Finset` sums over `∀ i, α i`.

1. **Hoeffding's lemma, finite form.**  For a function `Z` on a finite nonempty set with uniform
   weights, values in an interval of length `c`, and `λ : ℝ`:
   `avg exp(λ (Z − avg Z)) ≤ exp(λ² c² / 8)`.  Mathlib has it for measures as
   `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (`Mathlib/Probability/Moments/SubGaussian.lean`);
   instantiate with `PMF.uniformOfFintype`/`uniformOn`, or prove directly (convexity of `exp` plus
   the standard `log cosh`-type bound `p e^{λ(1−p)c} + (1−p) e^{−λpc} ≤ e^{λ²c²/8}`).
2. **Averaging out one coordinate at a time.**  For a finset `s ⊆ ι`, let `f_s(x)` be the average of
   `f` over the coordinates in `s` (others fixed).  `f_∅ = f`, `f_univ = avg f`.  For `i ∉ s`,
   `f_s − f_{s ∪ {i}}`, as a function of `x_i` with the rest fixed, has average `0` and range in an
   interval of length `≤ c i` (bounded differences survive averaging).  So
   `avg exp(λ(f_s − f_univ)) ≤ exp(λ² c_i² / 8) · avg exp(λ(f_{s∪{i}} − f_univ))` (Fubini over the
   product split `x_i` vs the rest; `Fintype.piFinset`/`Equiv.piSplitAt` help).
   Induction: `avg exp(λ(f − avg f)) ≤ exp(λ² Σ c_i² / 8)`.
3. **Chernoff** for the lower tail with `−λ`: `#{f ≤ avg f − t} ≤ card · exp(−λt + λ² Σc²/8)`;
   take `λ = 4t / Σc²` (if `Σc² = 0`, the inequality is trivial: `f` is constant, the set is empty
   since `t > 0`).

If a step stalls, state it as a NAMED sub-lemma with a disclosed hole plus an English paragraph and
a confidence; that is an acceptable finish.

Frozen: this statement and everything in `Literature/`.
-/

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-- **McDiarmid's inequality**, proved. -/
theorem mcDiarmidFinite_holds : McDiarmidFinite := by
  intro ι _ _ α _ _ _ f c hf t ht
  set N : ℝ := (Fintype.card (∀ i, α i) : ℝ)
  set m := (∑ z, f z) / N
  set C := ∑ i, c i ^ 2
  set S := Finset.univ.filter fun x => f x ≤ m - t
  have hN : (0 : ℝ) < N := McDiarmid.card_pos'
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hC.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, Real.exp_zero, mul_one]
    have : S.card ≤ Fintype.card (∀ i, α i) := (Finset.card_filter_le _ _).trans (by simp)
    simp only [N]; exact_mod_cast this
  set l := -(4 * t / C)
  have hmom := McDiarmid.sum_exp_le f c hf l
  have hlow : (S.card : ℝ) * Real.exp (4 * t ^ 2 / C) ≤
      ∑ x : ∀ i, α i, Real.exp (l * (f x - m)) := by
    calc (S.card : ℝ) * Real.exp (4 * t ^ 2 / C) = ∑ _x ∈ S, Real.exp (4 * t ^ 2 / C) := by
          simp
      _ ≤ ∑ x ∈ S, Real.exp (l * (f x - m)) := by
          refine Finset.sum_le_sum fun x hx => Real.exp_le_exp.2 ?_
          have hx' : f x ≤ m - t := (Finset.mem_filter.1 hx).2
          have : l * (f x - m) = 4 * t / C * (m - f x) := by simp only [l]; ring
          rw [this, show 4 * t ^ 2 / C = 4 * t / C * t by ring]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => (Real.exp_pos _).le
  have key := hlow.trans hmom
  have hl2 : l ^ 2 * C / 8 = 2 * t ^ 2 / C := by
    simp only [l]; field_simp; ring
  rw [hl2] at key
  have hsplit : Real.exp (-2 * t ^ 2 / C) * Real.exp (4 * t ^ 2 / C) =
      Real.exp (2 * t ^ 2 / C) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE := Real.exp_pos (4 * t ^ 2 / C)
  refine le_of_mul_le_mul_right ?_ hE
  calc (S.card : ℝ) * Real.exp (4 * t ^ 2 / C) ≤ N * Real.exp (2 * t ^ 2 / C) := key
    _ = _ := by rw [← hsplit]; ring

end LeanFormalizations.Erdos385

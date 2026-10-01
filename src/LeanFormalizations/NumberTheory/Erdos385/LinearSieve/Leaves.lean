/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.UpperBoundary
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.Assembly
import LeanFormalizations.NumberTheory.Erdos385.LinearSieve.UpperAt

/-!
# The named leaves of `aLow_pos` (phase E5, steps 2–5)

`aLow_pos` follows (`aLow_pos_of_leaves`) from:
* `aLow_nonneg`, `aLow_mono`, `bUp_mono`: bookkeeping on the liminf/limsup;
* `buchstab_limit_a`, `buchstab_limit_b`: Buchstab's identity in the limit (Mertens' 2nd theorem);
* `fundamental_lemma`: `|a(s) − Cs|, |b(s) − Cs| ≤ M e^{−s}` for `s ≥ 2`, `C = e^{−γ}`;
* `comparison_functions`: Jurkat–Richert's `f, F` (scaled by `s/ (e^γ)`… i.e. `α = Cs·f`,
  `β = Cs·F`), which solve the delay system with equality, have `α ≤ 0 ≤ … , β ≥ 2` on `(1, 2]`,
  the same exponential approach to `Cs`, and `α > 0` on `(2, ∞)`;
* `bUp_le_two` (proved, `UpperBoundary.lean`).

The assembly is the comparison principle (`Comparison.lean`) applied to
`K = max(α − a, b − β, 0)`.
-/

namespace LeanFormalizations.Erdos385.LinearSieve

open MeasureTheory Set Filter

/-- `C = e^{−γ}`, the Mertens constant `∏_{p<z}(1−1/p) ~ C / log z`. -/
noncomputable def mertC : ℝ := Real.exp (-Real.eulerMascheroniConstant)

/-- Leaf: `a ≥ 0`.  (Bookkeeping; needs coboundedness from `siftMin ≤ siftMax`.) -/
theorem aLow_nonneg : ∀ s : ℝ, 0 < s → 0 ≤ aLow s := by
  sorry

/-- Leaf: `a` is monotone on `(0, ∞)` (larger `s` = smaller `z` = more survivors). -/
theorem aLow_mono : MonotoneOn aLow (Ioi 0) := by
  sorry

/-- Leaf: `b` is monotone on `(0, ∞)`. -/
theorem bUp_mono : MonotoneOn bUp (Ioi 0) := by
  sorry

/-- Leaf (step 2): the lower Buchstab inequality in the limit. -/
theorem buchstab_limit_a : ∀ s s' : ℝ, 2 ≤ s → s ≤ s' →
    aLow s' - ∫ t in s..s', bUp (t - 1) / (t - 1) ≤ aLow s := by
  sorry

/-- Leaf (step 2): the upper Buchstab inequality in the limit. -/
theorem buchstab_limit_b : ∀ s s' : ℝ, 2 ≤ s → s ≤ s' →
    bUp s ≤ bUp s' - ∫ t in s..s', aLow (t - 1) / (t - 1) := by
  sorry

/-- Leaf (step 3): the fundamental lemma, with an exponentially small error. -/
theorem fundamental_lemma : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 2 ≤ s →
    |aLow s - mertC * s| ≤ M * Real.exp (-s) ∧ |bUp s - mertC * s| ≤ M * Real.exp (-s) := by
  sorry

/-- Leaf (step 4): the Jurkat–Richert comparison functions `α = Cs f(s)`, `β = Cs F(s)`. -/
theorem comparison_functions : ∃ α β : ℝ → ℝ, Continuous α ∧ Continuous β ∧
    (∀ s, 1 < s → s ≤ 2 → α s ≤ 0 ∧ 2 ≤ β s) ∧
    (∀ s s' : ℝ, 2 ≤ s → s ≤ s' →
      α s = α s' - ∫ t in s..s', β (t - 1) / (t - 1) ∧
      β s = β s' - ∫ t in s..s', α (t - 1) / (t - 1)) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 2 ≤ s →
      |α s - mertC * s| ≤ M * Real.exp (-s) ∧ |β s - mertC * s| ≤ M * Real.exp (-s)) ∧
    (∀ s, 2 < s → 0 < α s) := by
  sorry

/-- **Assembly**: the comparison principle turns the leaves into `a(s) ≥ α(s) > 0`. -/
theorem aLow_pos_of_leaves : ∀ s : ℝ, 2 < s → 0 < aLow s := by
  obtain ⟨α, β, hα, hβ, h12, hαβ, ⟨M2, hM2, hdec2⟩, hpos⟩ := comparison_functions
  obtain ⟨M1, hM1, hdec1⟩ := fundamental_lemma
  set a' : ℝ → ℝ := fun s => aLow (max s 1)
  set b' : ℝ → ℝ := fun s => bUp (max s 1)
  have hmax : ∀ s : ℝ, 1 ≤ s → max s 1 = s := fun s hs => max_eq_left hs
  have ha' : Monotone a' := fun x y h =>
    aLow_mono (show (0:ℝ) < max x 1 by positivity) (show (0:ℝ) < max y 1 by positivity)
      (max_le_max h le_rfl)
  have hb' : Monotone b' := fun x y h =>
    bUp_mono (show (0:ℝ) < max x 1 by positivity) (show (0:ℝ) < max y 1 by positivity)
      (max_le_max h le_rfl)
  have hcongr : ∀ (f : ℝ → ℝ) (s s' : ℝ), 2 ≤ s → s ≤ s' →
      ∫ t in s..s', f (max (t - 1) 1) / (t - 1) = ∫ t in s..s', f (t - 1) / (t - 1) := by
    intro f s s' hs hss
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hss] at ht
    simp only [hmax (t - 1) (by linarith [ht.1])]
  have key := pos_of_delay_system a' b' α β (M1 + M2) ha' hb' hα hβ
    (fun u hu1 hu2 => by
      simp only [a', b', hmax u hu1.le]
      obtain ⟨h1, h2⟩ := h12 u hu1 hu2
      exact ⟨h1.trans (aLow_nonneg u (by linarith)), (bUp_le_two (by linarith) hu2).trans h2⟩)
    (fun s s' hs hss => by
      simp only [a', b', hmax s (by linarith), hmax s' (by linarith), hcongr bUp s s' hs hss]
      exact buchstab_limit_a s s' hs hss)
    (fun s s' hs hss => by
      simp only [a', b', hmax s (by linarith), hmax s' (by linarith), hcongr aLow s s' hs hss]
      exact buchstab_limit_b s s' hs hss)
    hαβ
    (fun s hs => by
      unfold discK
      simp only [a', b', hmax s (by linarith)]
      obtain ⟨h1, h2⟩ := hdec1 s hs
      obtain ⟨h3, h4⟩ := hdec2 s hs
      rw [abs_le] at h1 h2 h3 h4
      have he := (Real.exp_pos (-s)).le
      refine max_le (max_le (by nlinarith) (by nlinarith)) (by positivity))
  intro s hs
  have := key s hs.le
  simp only [a', hmax s (by linarith)] at this
  linarith [hpos s hs]

end LeanFormalizations.Erdos385.LinearSieve

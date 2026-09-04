/-
# Catalan's constant: tails and Sun's weighted tails (§1 of arXiv:2609.04176v1)

Faithful rendering of the §1 objects of Zhi-Wei Sun, *Catalan's constant is irrational*,
arXiv:2609.04176v1 (3 Sep 2026).  ⚠️ The paper's headline claim (`G ∉ ℚ`) is **false as
proved** — see `TwoAdic.lean` and `papers/sun-2026-catalan-irrationality.md` — but §1–§2 are
sound, and this thread formalises exactly what survives.  Nothing in this directory claims,
or should ever claim, that Catalan's constant is irrational.

* `tail m`      = `T_m = Σ_{r ≥ 0} (-1)^r / (2(m+r)+1)^2`          (paper (1.1));
* `catalanConst` = `G = T_0 = Σ (-1)^k/(2k+1)^2 = 0.91596…`;
* `partialSum m` = `S_{m-1} = Σ_{k < m} (-1)^k/(2k+1)^2`;
* `wtail m`     = `u_m = T_m / (2m+1)`                             (paper (1.2), Sun's weighting).

The algebraic core (`Residual.lean`) consumes ONE analytic fact: the recurrence
`tail_add_tail_succ : T_m + T_{m+1} = 1/(2m+1)^2` (paper (1.4)).  Everything else here is a
sanity anchor ((1.1) as a theorem, the bounds (1.3)).
-/
import Mathlib

namespace LeanFormalizations.Catalan

open Finset

/-- The `m`-th tail `T_m = Σ_{r ≥ 0} (-1)^r / (2(m+r)+1)^2` of the Catalan series (paper (1.1)). -/
noncomputable def tail (m : ℕ) : ℝ := ∑' r : ℕ, (-1 : ℝ) ^ r / (2 * ((m : ℝ) + r) + 1) ^ 2

/-- Catalan's constant `G = β(2) = Σ_{k ≥ 0} (-1)^k / (2k+1)^2`, as the zeroth tail. -/
noncomputable def catalanConst : ℝ := tail 0

/-- The partial sum `S_{m-1} = Σ_{k < m} (-1)^k / (2k+1)^2` (paper §1; note the index shift). -/
noncomputable def partialSum (m : ℕ) : ℝ := ∑ k ∈ range m, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2

/-- Sun's **weighted tail** `u_m = T_m / (2m+1)` (paper (1.2)) — the author's own contribution,
and the reason the residual matrix of §2 has full column rank. -/
noncomputable def wtail (m : ℕ) : ℝ := tail m / (2 * (m : ℝ) + 1)

/-- The `r`-th absolute term `1/(2(m+r)+1)^2`, as a function of `r`. -/
noncomputable def tailAbs (m : ℕ) (r : ℕ) : ℝ := 1 / (2 * ((m : ℝ) + r) + 1) ^ 2

lemma tailAbs_pos (m r : ℕ) : 0 < tailAbs m r := by unfold tailAbs; positivity

lemma tailAbs_antitone (m : ℕ) : Antitone (tailAbs m) := by
  intro a b hab
  unfold tailAbs
  have : (0:ℝ) < 2 * ((m : ℝ) + a) + 1 := by positivity
  gcongr

lemma tailAbs_strictAnti (m : ℕ) : StrictAnti (tailAbs m) := by
  intro a b hab
  unfold tailAbs
  have : (0:ℝ) < 2 * ((m : ℝ) + a) + 1 := by positivity
  gcongr

lemma tailTerm_eq (m r : ℕ) :
    (-1 : ℝ) ^ r / (2 * ((m : ℝ) + r) + 1) ^ 2 = (-1 : ℝ) ^ r * tailAbs m r := by
  unfold tailAbs; ring

lemma summable_tailAbs (m : ℕ) : Summable (tailAbs m) := by
  have h : Summable (fun r : ℕ => 1 / ((r : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_nonneg_of_le (fun r => (tailAbs_pos m r).le) (fun r => ?_) h
  unfold tailAbs
  have h1 : (0:ℝ) < (r : ℝ) + 1 := by positivity
  gcongr
  have : (0:ℝ) ≤ m := by positivity
  linarith

/-- The tail series converges absolutely (compare with `1/r^2`). -/
theorem summable_tailTerm (m : ℕ) :
    Summable (fun r : ℕ => (-1 : ℝ) ^ r / (2 * ((m : ℝ) + r) + 1) ^ 2) := by
  simp_rw [tailTerm_eq]
  exact (summable_tailAbs m).alternating

/-- **Recurrence (1.4)**: `T_m + T_{m+1} = 1/(2m+1)^2`.  Peel the first term of `T_m`
(`Summable.tsum_eq_zero_add`); the remainder is `-T_{m+1}`.  This is the only analytic input to
`Residual.lean`. -/
theorem tail_add_tail_succ (m : ℕ) : tail m + tail (m + 1) = 1 / (2 * (m : ℝ) + 1) ^ 2 := by
  unfold tail
  rw [(summable_tailTerm m).tsum_eq_zero_add]
  have : ∀ r : ℕ, (-1 : ℝ) ^ (r + 1) / (2 * ((m : ℝ) + ((r + 1 : ℕ) : ℝ)) + 1) ^ 2
      = -((-1 : ℝ) ^ r / (2 * (((m + 1 : ℕ) : ℝ) + r) + 1) ^ 2) := by
    intro r; push_cast; rw [pow_succ]; ring
  simp_rw [this, tsum_neg]
  simp

/-- **(1.1)**: `T_m = (-1)^m (G - S_{m-1})`.  Induction on `m` from `tail_add_tail_succ`. -/
theorem tail_eq_catalan_sub_partialSum (m : ℕ) :
    tail m = (-1 : ℝ) ^ m * (catalanConst - partialSum m) := by
  induction m with
  | zero => simp [catalanConst, partialSum]
  | succ m ih =>
    have h := tail_add_tail_succ m
    have hsq : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [partialSum, sum_range_succ, ← partialSum, pow_succ]
    have hsq' : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by rw [← sq]; exact hsq
    linear_combination h - ih - (1 / (2 * (m : ℝ) + 1) ^ 2) * hsq'

/-- `T_m` as an alternating series over `tailAbs m`. -/
lemma tail_eq_tsum_alt (m : ℕ) : tail m = ∑' r : ℕ, (-1 : ℝ) ^ r * tailAbs m r := by
  unfold tail; simp_rw [tailTerm_eq]

/-- **(1.3), lower half**: `0 < T_m` (alternating series with decreasing terms). -/
theorem tail_pos (m : ℕ) : 0 < tail m := by
  rw [tail_eq_tsum_alt]
  have hl := (tailAbs_antitone m).alternating_series_le_tendsto
    (summable_tailAbs m).tendsto_alternating_series_tsum 1
  have h01 : tailAbs m 1 < tailAbs m 0 := tailAbs_strictAnti m (by norm_num)
  simp [sum_range_succ] at hl
  linarith

/-- **(1.3), upper half**: `T_m < 1/(2m+1)^2`. -/
theorem tail_lt (m : ℕ) : tail m < 1 / (2 * (m : ℝ) + 1) ^ 2 := by
  rw [tail_eq_tsum_alt]
  have hu := (tailAbs_antitone m).tendsto_le_alternating_series
    (summable_tailAbs m).tendsto_alternating_series_tsum 1
  have h12 : tailAbs m 2 < tailAbs m 1 := tailAbs_strictAnti m (by norm_num)
  have h0 : tailAbs m 0 = 1 / (2 * (m : ℝ) + 1) ^ 2 := by simp [tailAbs]
  simp [sum_range_succ] at hu
  linarith

end LeanFormalizations.Catalan

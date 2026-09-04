/-
# Dirichlet beta values: `β(s) = Σ (-1)^k / (2k+1)^s`

Phase 4 of the Catalan thread (`DIRECTION.md`).  The target is the nearest **true** theorem in
Catalan's family — Rivoal–Zudilin 2003 / Zudilin 2019 (arXiv:1804.09922, §2), made elementary in
the pattern of Zudilin's SIGMA 2018 paper on odd zeta values (arXiv:1801.09895):

> **at least one of `β(2), β(4), …, β(20)` is irrational.**

`β(2) = G` is Catalan's constant, so this is a *proved* statement whose Catalan case is the open
problem.  ⚠️ Nothing in this directory claims `G ∉ ℚ`.  That remains open.

This file: the definition, its summability, and the bridge `β(2) = catalanConst`.
-/
import Mathlib
import LeanFormalizations.NumberTheory.Catalan.Tails

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- The Dirichlet beta value `β(s) = Σ_{k ≥ 0} (-1)^k / (2k+1)^s`.  Meaningful (absolutely
convergent) for `s ≥ 2`, which is the only range this development uses. -/
noncomputable def dirichletBeta (s : ℕ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ s

/-- **B1.**  The defining series converges absolutely for `s ≥ 2`. -/
theorem summable_betaTerm {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun k : ℕ => (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ s) := by
  refine Summable.of_norm_bounded (LeanFormalizations.Catalan.summable_tailAbs 0) fun k => ?_
  have hk : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (by positivity),
    LeanFormalizations.Catalan.tailAbs]
  simp only [Nat.cast_zero, zero_add]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hk hs)

/-- **B2.**  `β(2)` is Catalan's constant, as defined in the Phase 1–3 thread
(`Catalan/Tails.lean`).  This is the edge that makes the headline a statement *about* `G`. -/
theorem beta_two_eq_catalanConst : dirichletBeta 2 = LeanFormalizations.Catalan.catalanConst := by
  unfold dirichletBeta LeanFormalizations.Catalan.catalanConst LeanFormalizations.Catalan.tail
  simp

end LeanFormalizations.DirichletBeta

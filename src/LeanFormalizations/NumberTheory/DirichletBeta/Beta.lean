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
  sorry

/-- **B2.**  `β(2)` is Catalan's constant, as defined in the Phase 1–3 thread
(`Catalan/Tails.lean`).  This is the edge that makes the headline a statement *about* `G`. -/
theorem beta_two_eq_catalanConst : dirichletBeta 2 = LeanFormalizations.Catalan.catalanConst := by
  sorry

end LeanFormalizations.DirichletBeta

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Literature input: ζ(5) is irrational (Fauzan 2026), machine-checked twice

Statement only, cited, never an `axiom`.  This follows the Stephan pattern (`Stephan2026Ridout`): a
result already formalized elsewhere enters verbatim, and is discharged by `require`-ing a fork
once the toolchains meet.  Our pin is v4.31; both formalizations are newer.

* M. Fauzan, *ζ(5) is irrational* (Zenodo 22826419, 2026).  Our audit is
  `papers/fauzan-2026-zeta5-irrationality.md`.
* **github.com/domino14/zeta5** (César Del Solar + Claude, 2026-09-23, Lean v4.35.0-rc2).  It
  proves `Irrational (riemannZeta 5).re` with `(riemannZeta 5).im = 0`; Ren rebuilt it locally
  and checked `#print axioms` on 2026-09-23.
* **github.com/mo271/Zeta5** (Moritz Firsching, 2026-09-27, Lean v4.34.0-rc1).  It proves
  formal-conjectures' `RiemannZetaValues.irrational_five`, the form stated below, CI-checked by
  Comparator.  The two are independent; peers, not rivals.
* Epoch FrontierMath lists ζ(5) as solved (human + AI).  ζ(7) and Catalan remain open there.  The
  Anand 2026 "ζ(7) is irrational" preprint is refuted (`papers/anand-2026-zeta7-irrationality.md`).
-/
import Mathlib

namespace LeanFormalizations.Literature

/-- **ζ(5) is irrational** (Fauzan 2026; formal-conjectures' `RiemannZetaValues.irrational_five`,
proved in domino14/zeta5 and mo271/Zeta5). -/
def Fauzan2026Zeta5 : Prop := ∃ x : ℝ, Irrational x ∧ riemannZeta 5 = x

end LeanFormalizations.Literature

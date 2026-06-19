/-
# The Goodstein length function

The **Goodstein length** `goodsteinLength m` is the step at which the Goodstein
sequence seeded at `m` first reaches `0`. It is well-defined by `goodstein_terminates`
(every Goodstein sequence terminates — proved axiom-clean in `Engine.lean`).

This function is the bridge to the *independence* story. Its growth rate is
astronomically fast — it tracks the Hardy function `H_{ε₀}` (equivalently the
fast-growing `f_{ε₀}` of `Mathlib.SetTheory.Ordinal.Notation`, `ONote.fastGrowingε₀`).
Because every PA-provably-total function is dominated by some `f_α` with `α < ε₀`,
and `goodsteinLength` eventually outgrows every such `f_α`, PA cannot prove that
`goodsteinLength` is total — which is the Kirby–Paris independence result. The
*growth content* of that argument (the part that lives entirely in mathlib, no
first-order-logic machinery) is what the `Logic/FastGrowing/` files develop, and
`Logic/Goodstein/Growth.lean` (to be built) connects this function to it.

The PA-syntactic wrapper (`PA ⊬ γ`) is a separate expedition; see the repo
`~/src/goodstein-independence`. This file builds only the object-level function and
its basic API.
-/
import LeanFormalizations.Logic.Goodstein.Statement

namespace LeanFormalizations.Logic.Goodstein

/-- The **Goodstein length** of `m`: the least step `N` at which the Goodstein
sequence seeded at `m` reaches `0`. Total by `goodstein_terminates`. -/
def goodsteinLength (m : ℕ) : ℕ := Nat.find (goodstein_terminates m)

/-- Defining property: the sequence is `0` at its length. -/
theorem goodsteinSeq_goodsteinLength (m : ℕ) :
    goodsteinSeq m (goodsteinLength m) = 0 :=
  Nat.find_spec (goodstein_terminates m)

/-- The length is the *least* zero: any zero step is `≥ goodsteinLength m`. -/
theorem goodsteinLength_le {m N : ℕ} (h : goodsteinSeq m N = 0) :
    goodsteinLength m ≤ N :=
  Nat.find_le h

/-- Before the length, the sequence is nonzero. -/
theorem goodsteinSeq_ne_zero_of_lt {m N : ℕ} (h : N < goodsteinLength m) :
    goodsteinSeq m N ≠ 0 :=
  Nat.find_min (goodstein_terminates m) h

/-! ## Anchors (anti-vacuity)

Small computed values, off any headline axiom path. A wrong definition of
`goodsteinSeq` could not satisfy these. -/

example : goodsteinLength 0 = 0 := by native_decide
example : goodsteinLength 2 = 3 := by native_decide
example : goodsteinLength 3 = 5 := by native_decide

end LeanFormalizations.Logic.Goodstein

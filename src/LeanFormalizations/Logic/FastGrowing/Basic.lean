/-
# Growth theory of the fast-growing hierarchy

`Mathlib.SetTheory.Ordinal.Notation` already provides the **fast-growing hierarchy**
on ordinal notations below `ε₀`:

* `ONote.fastGrowing : ONote → ℕ → ℕ`  with `f₀ = succ`, `f_{α+1} = fun n => f_α^[n] n`,
  `f_λ = fun n => f_{λ[n]} n` (limit `λ`, via `ONote.fundamentalSequence`);
* `ONote.fastGrowingε₀ : ℕ → ℕ`, the one-step extension to `ε₀` itself.

mathlib proves the *small values* (`fastGrowing_one = (2 * ·)`, `fastGrowing_two = fun n => 2^n * n`,
`fastGrowingε₀_zero = 1`, `fastGrowingε₀_one = 2`) but **none of the growth theory**:
no expansiveness, no monotonicity, no domination. Those are exactly the facts the
Kirby–Paris growth argument needs, and they are the targets here.

These lemmas are mathlib-PR-shaped (they belong next to `ONote.fastGrowing`); developing
them here both serves the Goodstein-independence growth content and is independently useful.

## Normal-form hypotheses
`fastGrowing` is total on all of `ONote`, but the intended (and provable) statements
hold for **normal-form** notations (`ONote.NF`). Carry `[o.NF]`/`(h : o.NF)` where the
proof needs it; the `fundamentalSequence` correctness lemmas
(`ONote.fundamentalSequence_has_prop`, `ONote.FundamentalSequenceProp`) and the
`fastGrowing_zero'/_succ/_limit` characterizations are the entry points.
-/
import Mathlib.SetTheory.Ordinal.Notation

namespace LeanFormalizations.Logic.FastGrowing

open ONote

/-- **Expansiveness.** Every level of the fast-growing hierarchy dominates the
identity. (Foundational; by transfinite induction on the notation via
`fastGrowing_zero'/_succ/_limit`. The successor step needs that iterating a
`≥ id` function stays `≥ id`.) -/
lemma le_fastGrowing (o : ONote) (h : o.NF) (n : ℕ) : n ≤ fastGrowing o n := by
  sorry

/-- **Monotonicity in the argument.** Each level is a monotone function of `n`. -/
lemma fastGrowing_monotone (o : ONote) (h : o.NF) : Monotone (fastGrowing o) := by
  sorry

/-- **Strict expansiveness for positive input.** For `n ≥ 1` every level strictly
exceeds the identity. (Follows from `le_fastGrowing` + the structure of the
successor/limit steps.) -/
lemma lt_fastGrowing (o : ONote) (h : o.NF) {n : ℕ} (hn : 1 ≤ n) :
    n < fastGrowing o n := by
  sorry

end LeanFormalizations.Logic.FastGrowing

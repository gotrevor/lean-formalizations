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
import Mathlib.Order.Iterate

namespace LeanFormalizations.Logic.FastGrowing

open ONote

/-- **Expansiveness.** Every level of the fast-growing hierarchy dominates the
identity: `n ≤ f_o(n)` for every notation `o` (no normal-form hypothesis needed —
`fundamentalSequence_has_prop` holds for all `o`).

Proof by well-founded recursion on `o` (the same `<`-recursion that *defines*
`fastGrowing`), via the three characterizations `fastGrowing_zero'/_succ/_limit`:
* `o = 0`: `f_o = Nat.succ`, so `n ≤ n+1`.
* successor `o = a+1`: `f_o n = (f_a)^[n] n`; by IH `id ≤ f_a`, and iterating a
  function that dominates the identity stays `≥ id` (`id_le_iterate_of_id_le`).
* limit: `f_o n = f_{o[n]} n` with `o[n] < o`, so the IH applies directly. -/
theorem le_fastGrowing (o : ONote) (n : ℕ) : n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · -- `o = 0`: `fastGrowing o = Nat.succ`
    rw [fastGrowing_zero' o e]
    exact Nat.le_succ n
  · -- successor: `fastGrowing o n = (fastGrowing a)^[n] n`, `a < o`
    have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    have ih : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    exact Function.id_le_iterate_of_id_le ih n n
  · -- limit: `fastGrowing o n = fastGrowing (f n) n`, `f n < o`
    have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    exact le_fastGrowing (f n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Strict expansiveness for positive input.** For `n ≥ 1` every level strictly
exceeds the identity, `n < f_o(n)`.

Same well-founded recursion as `le_fastGrowing`:
* `o = 0`: `f_o n = n+1 > n`.
* successor: `n < f_a n` (strict IH) and `f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
  (iterate count is monotone for `id ≤ f_a`, and `1 ≤ n`).
* limit: `n < f_{o[n]} n` directly by the strict IH at `o[n] < o`. -/
theorem lt_fastGrowing (o : ONote) {n : ℕ} (hn : 1 ≤ n) : n < fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [fastGrowing_zero' o e]
    exact Nat.lt_succ_self n
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    -- `n < f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
    have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    have hstep : fastGrowing a n ≤ (fastGrowing a)^[n] n := by
      have hmono := Function.monotone_iterate_of_id_le hexp hn
      simpa using hmono n
    exact lt_of_lt_of_le (lt_fastGrowing a hn) hstep
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    exact lt_fastGrowing (f n) hn
termination_by o
decreasing_by all_goals exact hlt

/-- **Monotonicity in the argument** (successor/zero levels). Placeholder for the
full `Monotone (fastGrowing o)`: the limit case requires index-monotonicity of the
hierarchy (the A3 crux), so the general statement is developed alongside that. -/
lemma fastGrowing_monotone (o : ONote) (h : o.NF) : Monotone (fastGrowing o) := by
  sorry

end LeanFormalizations.Logic.FastGrowing

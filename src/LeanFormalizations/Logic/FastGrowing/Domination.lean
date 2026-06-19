/-
# A4 — `fastGrowingε₀` dominates every fixed level (the headline domination crux)

The unboundedness that *is* the Goodstein/Kirby–Paris independence content:

> For every notation `o < ε₀`, eventually `fastGrowing o n < fastGrowingε₀ n`.

`fastGrowingε₀` is `mathlib`'s one-step extension of the fast-growing hierarchy to `ε₀`,
built on the *diagonal tower* fundamental sequence `0, 1, ω, ω^ω, ω^ω^ω, …` converging to
`ε₀`:

* `fastGrowingε₀ i = fastGrowing (tower i) i`, where `tower i = (fun a => ω^a)^[i] 0`.

This file pins the tower structure and **states A4**, reducing it to its hard core. With
A1 (`le_fastGrowing`), A2 (`fastGrowing_monotone`) and A3 (`fastGrowing_bachmann_reach`)
all proved axiom-clean in `Basic.lean`, the remaining content of A4 is an **index
domination** fact: each fixed `o` is eventually outgrown because the tower indices climb
past it (the towers are cofinal in `ε₀`).

## Attack plan (the disclosed `sorry` is the index-domination core)
1. **Tower structure** (done here): `tower (i+1) = ω^{tower i}`, `fastGrowingε₀` unfolds to
   `fastGrowing (tower i) i`.
2. **Cofinality** *(open)*: for NF `o`, `∃ k, o < tower k` — the towers exhaust `ε₀`.
   Needs `repr o < ε₀` (from `NF`) and `x < ω^x` for `x < ε₀` (strictness via `NF`).
3. **Index domination** *(open, the core)*: `o < tower n ⟹ fastGrowing o n ≤
   fastGrowing (tower n) n` for `n` past some threshold. The `Reaches`/Bachmann engine
   gives index monotonicity *along fundamental sequences*; lifting it to a general
   `α < β ⟹ eventually f_α ≤ f_β` is the genuine remaining work.
4. **Strictness**: bump `≤` to `<` via one successor step (`lt_fastGrowing`).
-/
import Mathlib.SetTheory.Ordinal.Notation
import LeanFormalizations.Logic.FastGrowing.Basic

namespace LeanFormalizations.Logic.FastGrowing

open ONote

/-- The **diagonal tower** `0, 1, ω, ω^ω, …` underlying `ONote.fastGrowingε₀`:
`tower i = (fun a => ω^a)^[i] 0`. -/
def tower (i : ℕ) : ONote := (fun a => oadd a 1 0)^[i] 0

@[simp] theorem tower_zero : tower 0 = 0 := rfl

/-- `tower (i+1) = ω^{tower i}`. -/
theorem tower_succ (i : ℕ) : tower (i + 1) = oadd (tower i) 1 0 := by
  rw [tower, tower, Function.iterate_succ_apply']

/-- `fastGrowingε₀ i = f_{tower i}(i)` — the definitional unfolding, as a named lemma. -/
theorem fastGrowingε₀_eq (i : ℕ) : fastGrowingε₀ i = fastGrowing (tower i) i := rfl

/-- **A4 — domination (the headline crux).** Every fixed level of the fast-growing
hierarchy is eventually strictly dominated by `fastGrowingε₀`. *(disclosed `sorry`: the
index-domination core, see the file header's attack plan; A1–A3 it builds on are all
proved axiom-clean.)* -/
theorem fastGrowing_lt_fastGrowingε₀ (o : ONote) (_ho : o.NF) :
    ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n := by
  sorry

/-! ### Anti-vacuity anchors for `fastGrowingε₀` (`native_decide`) -/

example : fastGrowingε₀ 0 = 1 := by native_decide
example : fastGrowingε₀ 1 = 2 := by native_decide
example : fastGrowingε₀ 2 = 2048 := by native_decide
-- the tower really is `ω^ω` at level 3 (a genuine limit-of-limits index)
example : tower 3 = oadd (oadd 1 1 0) 1 0 := by native_decide

end LeanFormalizations.Logic.FastGrowing

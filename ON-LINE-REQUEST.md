# ON-LINE-REQUEST — open-web help needed (the box has no general internet)

## 2026-06-19 — General Bachmann reachability / fast-growing index domination

**Context.** Formalizing the growth theory of `ONote.fastGrowing` (the fast-growing
hierarchy on ordinal notations `< ε₀`, mathlib `Mathlib.SetTheory.Ordinal.Notation`).
Monotonicity (A2) and the consecutive index step (A3, the "Bachmann property" that the
budget-`n+1` descent of `o[n+1]` passes through `o[n]`) are now fully proved in this repo
(`Logic/FastGrowing/Basic.lean`, theorem `fastGrowing_bachmann_reach`). The last open piece
of A4 (`fastGrowingε₀` dominates every fixed `f_o`) is the **general** reachability:

> For normal-form notations `α < β` and the standard CNF fundamental sequences `(·)[·]`,
> define the descent relation `Reaches x β α` (predecessor steps at successors, index-`x`
> steps at limits). Show `Reaches x β α` holds once `x` is at least the "norm" of `α`
> (intuitively the largest finite coefficient/finite tail in `α`'s Cantor normal form).

**What I need (any of these unblocks me):**
1. The precise classical statement + proof that, for the standard fundamental sequences,
   `α < β ⟹ f_α(n) ≤ f_β(n)` for `n ≥ G(α)` (some norm/length of `α`) — i.e. the
   eventual index-domination lemma — with the cleanest definition of the norm. Primary
   sources: Buchholz–Wainer; Cichoń–Wainer "The slow-growing and the Grzegorczyk
   hierarchies" (JSL 1983); Schwichtenberg–Wainer "Proofs and Computations" (subrecursive
   hierarchies chapter). The exact hypothesis on `n` is what I need pinned down.
2. The "Bachmann property" of the standard CNF fundamental-sequence assignment stated as a
   reachability/`→_n` relation (e.g. as in Buchholz's notes), with the budget condition.
3. Any existing **formalization** (Lean/mathlib, Isabelle/AFP, Coq) of fast-growing or
   Hardy hierarchy index monotonicity / domination, or of the Bachmann property, to port.
   (Checked Reservoir 2026-06-18: none in the Lean ecosystem. Isabelle AFP "Ackermann"/
   "Goodstein"/"Ordinal" entries? Coq developments by Castéran on the Hydra/Goodstein?)

**Why it unblocks:** with the norm condition pinned, the open lemma
`fastGrowing_lt_of_lt_tower` (`Domination.lean`) closes by a well-founded recursion on `β`
reusing the existing `Reaches` engine, completing A4 — the unboundedness that *is* the
Kirby–Paris independence growth gap.

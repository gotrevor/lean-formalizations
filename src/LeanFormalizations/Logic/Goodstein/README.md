# Goodstein's theorem (termination)

**Result.** Goodstein, R. L., *"On the restricted ordinal theorem,"* J. Symbolic
Logic 9 (1944), 33–41. Every Goodstein sequence reaches 0.

**Why it's here.** Solved (1944), and — as of this writing — *unformalized in Lean*
(confirmed against the 705-repo Reservoir ecosystem mirror and mathlib's
`docs/1000.yaml`, where it sits with a title but no `decl:`). Even the Isabelle/AFP
artifact (`Goodstein_Lambda`, Felgenhauer 2020) is narrower: it implements the
Goodstein *function* in λ-calculus over Church-encoded ordinals and *explicitly
skips the hereditary-base-2 conversion* — the very bridge to the literal integer
sequence. A faithful Lean proof that includes that bridge would be a first.

## Status: IN PROGRESS (treadmill)
- `goodsteinSeq` (`Defs.lean`) — **STUB**, to be replaced by the faithful definition.
- `goodstein_terminates` (`Statement.lean`) — headline, `sorry`.
- `Anchors.lean` — ground-truth trajectories, `sorry` (discharge by `native_decide`
  once the definition is real). These gate completion.

## What to audit (the entire trust surface)
1. **`Defs.lean`** — `base` and `goodsteinSeq`. Check the definition matches the
   standard hereditary-base / bump-then-subtract-one construction.
2. **`Anchors.lean`** — the m = 0,1,2,3 trajectories below, discharged by
   computation. These certify the definition is non-vacuous and correct on small
   seeds.
3. **`Statement.lean`** — `goodstein_terminates`. Check `#print axioms` is clean
   (`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no custom axiom; no
   `native_decide` on this path).

Everything in the engine siblings is "ignore for faithfulness."

## Ground-truth trajectories (hand-computed; bases 2,3,4,…)

Convention: `G 0 = m`; `G (k+1)` = (write `G k` in hereditary base `k+2`, bump
`k+2 ↦ k+3`, subtract 1); `0` absorbing.

| m | sequence `G 0, G 1, …` | reaches 0 at step |
|---|------------------------|-------------------|
| 0 | 0 | 0 |
| 1 | 1, 0 | 1 |
| 2 | 2, 2, 1, 0 | 3 |
| 3 | 3, 3, 3, 2, 1, 0 | 5 |

Worked example, m = 3: `3 = 2+1` (base 2) → bump → `3+1 = 4`, −1 → **3**;
`3 = 3¹` (base 3) → bump → `4`, −1 → **3**; `3` (base 4, a bare digit) → −1 → **2**;
**2** → **1** → **0**. (m = 4 is finite too but astronomically long — not anchorable.)

## Proof of termination
Map `G k` (hereditary base `k+2`) to an ordinal by replacing the base with `ω`.
Bump = invisible to the map; −1 = strict ordinal decrease; `Ordinal` well-founded
(`Ordinal.wellFoundedLT`) ⇒ the strictly-decreasing ordinal sequence terminates ⇒
`G k = 0`. mathlib provides `Ordinal.CNF`, `Ordinal.coeff`/`eval`, and
well-foundedness; we build the hereditary-base ↔ ordinal interpretation and the
bump-invariance + strict-decrease lemmas.

## Out of scope: Kirby–Paris independence
"PA does not prove Goodstein's theorem" (Kirby & Paris, *"Accessible independence
results for Peano arithmetic,"* Bull. LMS 14 (1982), 285–293) is a true,
**separate**, metamathematical theorem. It would require formalizing PA, provability,
Gödel's second incompleteness theorem (these exist in Lean 4 via
`FormalizedFormalLogic/Foundation`, *not* mathlib), plus the `Goodstein ⟹ Con(PA)`
ε₀-induction reduction (not formalized anywhere in Lean, to our knowledge). Not
attempted here — this project proves the positive theorem only.

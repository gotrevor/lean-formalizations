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

## Status: ✅ PROVED, axiom-clean
- `goodsteinSeq` (`Defs.lean`) — **faithful** hereditary-base bump definition.
- `goodstein_terminates` (`Statement.lean`) — **PROVED**;
  `#print axioms = [propext, Classical.choice, Quot.sound]`.
- `Anchors.lean` — m = 0,1,2,3 trajectories, all discharged by `native_decide`.

The proof engine is `Engine.lean` (ordinal interpretation + descent).

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

## Proof of termination (`Engine.lean`)
Map `G k` (hereditary base `k+2`) to an ordinal `toOrdinal (k+2) (G k)` by replacing
the base with `ω` — the *same* top-power peeling as `bump`. The proof rests on:

1. **`toOrdinal_mono_and_bound`** — `n ↦ toOrdinal b n` is strictly monotone, and
   `toOrdinal b n < ω^(toOrdinal b (log b n) + 1)` (the CNF leading bound). These
   two are mutually recursive, so proved together in one strong induction.
   `bump_mono_and_bound` is the verbatim ℕ-twin (`ω ↦ b+1`).
2. **`toOrdinal_bump`** — `toOrdinal (b+1) (bump b n) = toOrdinal b n`: bumping the
   base is invisible to the map. Proof reads off the base-`(b+1)` digit structure
   of `bump b n` (leading exponent `bump b (log b n)`, digit `n / b^(log b n)`,
   remainder `bump b (n % …)`) via `Nat.log_eq_of_pow_le_of_lt_pow` and recurses.
3. **`seqOrd_step`** — for `seqOrd m k := toOrdinal (k+2) (G k)`, a nonzero term
   forces `seqOrd m (k+1) < seqOrd m k` (invariance fixes the base-bump; `−1` is a
   strict ordinal drop by monotonicity).
4. **`goodstein_terminates_engine`** — an infinite strictly-decreasing `seqOrd`
   contradicts well-foundedness of `<` on `Ordinal` (`Ordinal.lt_wf.has_min`), so
   some `G N = 0`.

Built directly on `toOrdinal`/`bump`; uses `Mathlib.SetTheory.Ordinal.Exponential`
(`opow`, `omega0`) rather than `Ordinal.CNF`.

## Out of scope: Kirby–Paris independence
"PA does not prove Goodstein's theorem" (Kirby & Paris, *"Accessible independence
results for Peano arithmetic,"* Bull. LMS 14 (1982), 285–293) is a true,
**separate**, metamathematical theorem. It would require formalizing PA, provability,
Gödel's second incompleteness theorem (these exist in Lean 4 via
`FormalizedFormalLogic/Foundation`, *not* mathlib), plus the `Goodstein ⟹ Con(PA)`
ε₀-induction reduction (not formalized anywhere in Lean, to our knowledge). Not
attempted here — this project proves the positive theorem only.

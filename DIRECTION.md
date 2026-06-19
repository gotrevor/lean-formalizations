# DIRECTION — read FIRST (operator directive, 2026-06-18, Trevor via Ren)

## ⛔ BOUNDED RUN. Prove **Goodstein's theorem** (termination), then STOP.

New directed target. The prior power-tower thread is COMPLETE — do not touch it.
You are formalizing exactly ONE new result and then ending the run.

### ⚠️ This is a hard, multi-lap proof. STAYING is the whole point.
Goodstein needs an ordinal-descent argument and a faithful hereditary-base
definition. **Expect many grind laps. That is fine — chip at it lap by lap.** Do
NOT declare it "out of scope," do NOT decide a narrow axiom is the "realistic
destination," and ABOVE ALL do NOT wander to a different result. The repo is
otherwise finished; the ONLY work this run is Goodstein.

### DO NOT TOUCH — four complete, axiom-clean threads
`NumberTheory/Transcendence/`, `Geometry/Constructible/`,
`NumericalSemigroups/Curtis/`, `RealAnalysis/PowerTower/` are all DONE and
axiom-clean. Do not modify them, do not reopen them, do not re-add any axiom. Work
ONLY in `src/LeanFormalizations/Logic/Goodstein/`.

### ⚠️ DO NOT start any other new target
`HANDOFF`/`PENDING_WORK` may mention other ideas (general Hermite–Lindemann,
Constructible Layer-2 geometry, gathering the Erdős repos). They are ALL out of
scope for this run. When Goodstein is proved, the run is OVER — see Completion.

---

## The target

Goodstein, *"On the restricted ordinal theorem,"* JSL 1944: every Goodstein
sequence reaches 0. The scaffold is in place (`Logic/Goodstein/`):

- `Defs.lean` — `goodsteinSeq m k = G k` is currently a **STUB** returning the
  seed. **Replace it with the faithful definition** (hereditary base `k+2`, bump
  `k+2 ↦ k+3`, subtract one; `0` absorbing). One general definition — NO
  special-casing small inputs.
- `Anchors.lean` — ground-truth trajectories for m = 0,1,2,3 (`sorry` now).
  **Discharge each by `decide`/`native_decide`** once the definition is real.
  These are the anti-vacuity lock; a fake definition cannot satisfy e.g.
  `goodsteinSeq 3 3 = 2`.
- `Statement.lean` — the headline (`sorry` now):
  ```lean
  theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0
  ```
  This is the faithful audit surface; keep the statement exactly this shape.

### Proof plan (ordinal descent)
1. Faithful `goodsteinSeq` via `Nat.digits` (well-founded recursion on the value;
   exponents are strictly smaller). Discharge the anchors to confirm it.
2. Build the hereditary-base → ordinal interpretation: read `G k` in base `k+2`,
   replace the base by `ω`. Use `Ordinal.CNF` / `Ordinal.coeff` / `Ordinal.eval`
   (`Mathlib.SetTheory.Ordinal.CantorNormalForm`).
3. **Bump-invariance:** the map of `G k` at base `k+2` equals the map of
   `bump(G k)` at base `k+3` (the base reads as `ω` either way).
4. **Strict decrease:** subtracting one strictly lowers the ordinal, so the
   ordinal of `G (k+1)` `<` ordinal of `G k` whenever `G k ≠ 0`.
5. `Ordinal.wellFoundedLT` ⇒ no infinite strictly-decreasing sequence ⇒ the map
   must hit `0` ⇒ `G k = 0`. Conclude `goodstein_terminates`.

Put the definition's recursion + the ordinal machinery in engine siblings
(e.g. `Engine.lean`); keep `Statement.lean` thin and faithful.

### Scope: POSITIVE theorem only
Prove termination (object-level math; Lean's logic is far stronger than PA, so this
is just the ordinal argument). The **Kirby–Paris independence** ("PA cannot prove
this") is metamathematics about PA and is OUT OF SCOPE — README documents it, do
not attempt it.

---

## Rules (same as every run here)
- **No `sorry`/`admit` at the end.** A stuck step is a lemma-name/bookkeeping issue
  — grind it, don't bail, don't switch targets. Partial green progress committed
  each lap is exactly right.
- **Stay in your lane:** ONLY `Logic/Goodstein/`. Keep the repo at 0 math axioms.
- Verify every lemma name against this repo's mathlib (`v4.29.1`). `push_neg` is
  deprecated → `push Not at h`.
- `native_decide` is fine for the `Anchors.lean` `example`s (standalone, off the
  headline path) but must NOT appear on `goodstein_terminates`'s axiom path.
- Commit every green build (from a real `lake build`). **DO NOT push.**
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
- Blocked needing the open web (exact mathlib name for an ordinal/CNF/well-founded
  lemma, or a reference proof of the bump-invariance)? Append a dated item to
  `ON-LINE-REQUEST.md` and continue on a different sub-lemma.

---

## Completion = stop condition (`--allow-stop` is armed)

`src/` was sorry-free before this run; the Goodstein scaffold added `sorry`s
(the headline + the anchors), so the sorry-gate is genuinely CLOSED and stays
closed until the work is truly done. Self-stop ONLY when ALL of these hold:

- `goodsteinSeq` (`Defs.lean`) is the **faithful definition** (not the stub);
- ALL `Anchors.lean` `example`s are **discharged** (`decide`/`native_decide`), no `sorry`;
- `goodstein_terminates` (`Statement.lean`) is **PROVED** (no `sorry`);
- `src/` is sorry-free, `lake build` green;
- `#print axioms goodstein_terminates` = `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no custom axiom, no `native_decide` on the headline path).

Then refresh `STATUS.md`, `HANDOFF.md`, the Goodstein `README.md`, and the top
`README.md` table (add the Goodstein row), commit, and:
```
printf 'source=lap\nreason=Goodstein theorem complete (every Goodstein sequence terminates, axiom-clean)\n' > "$LEAN_STOP_SENTINEL"
```
then end the turn. If ANY `sorry` lingers or the definition is still the stub, do
NOT stop — finish it. And do NOT start a different result to "keep busy."

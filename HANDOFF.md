# HANDOFF — lean-formalizations (2026-06-19, expedition START)

## 👉 READ `DIRECTION.md` FIRST. This is an UNBOUNDED expedition, not a bounded run.

**Mission:** build the **growth theory behind Goodstein independence (Kirby–Paris)** —
the mathlib-only "Goodstein grows like `f_{ε₀}`" content. NOT the PA-syntactic `PA ⊬ γ`
(that's a separate repo, `~/src/goodstein-independence`, and needs logic machinery you
don't have here). Full mission + milestone ladder + anti-vacuity rules: **`DIRECTION.md`**.

No self-stop. `--allow-stop` is OFF. Keep building lap after lap until Trevor stops the run.

## State at expedition start (this commit)
- **Five prior threads COMPLETE + axiom-clean, untouched:** `NumberTheory/Transcendence`
  (e+π Lindemann), `Geometry/Constructible` (Wantzel L1), `NumericalSemigroups/Curtis`,
  `RealAnalysis/PowerTower` (sharp Euler iff), `Logic/Goodstein` (termination). **Do not
  modify these** (except read/reuse `Logic/Goodstein/{Defs,Engine,Statement}`).
- **New scaffold, build GREEN (8285 jobs):**
  - `Logic/Goodstein/Length.lean` — `goodsteinLength m := Nat.find (goodstein_terminates m)`,
    the `Nat.find` API (`goodsteinSeq_goodsteinLength`, `goodsteinLength_le`,
    `goodsteinSeq_ne_zero_of_lt`), and **`native_decide` anchors** (`0↦0, 2↦3, 3↦5`,
    all compile — anti-vacuity lock confirmed).
  - `Logic/FastGrowing/Basic.lean` — three `sorry`'d growth-theory targets over mathlib's
    `ONote.fastGrowing`: `le_fastGrowing` (A1), `fastGrowing_monotone` (A2),
    `lt_fastGrowing` (strict). These are lap-1 handles.
  - Both wired into `src/LeanFormalizations.lean`.

## Next bricks (see DIRECTION.md §"milestone ladder" for the full map)
1. **A1 `le_fastGrowing`** (expansiveness `n ≤ fastGrowing o n`) — foundational, unblocks the rest.
   Transfinite induction on `ONote` via `fastGrowing_zero'/_succ/_limit`; successor step =
   "iterating a `≥ id` map stays `≥ id`".
2. **A2 `fastGrowing_monotone`**, then the strict `lt_fastGrowing`.
3. Define **`hardy`** (B1) + its char lemmas + anchors — cheap, computable, unlocks anchors.
4. **Attack the cruxes** (hardest-first, every lap): A3 (index monotonicity stepping stones),
   A4 (`fastGrowingε₀` dominates each fixed level), then C2/C3 (bridge our `Engine.toOrdinal`
   descent to `ONote`, then the headline `goodsteinLength` growth theorem).

## Key reuse / facts
- mathlib ALREADY has `ONote.fastGrowing` + `ONote.fastGrowingε₀` + `ONote.fundamentalSequence`
  (`Mathlib.SetTheory.Ordinal.Notation`). Do NOT reinvent them — build the *growth theory* on top.
- Our `Logic/Goodstein/Engine.lean` already maps Goodstein terms to `Ordinal < ε₀`
  (`toOrdinal`, `seqOrd`, `seqOrd_step`) and proves termination by well-foundedness. That
  descent is the model-side content C2/C3 reuse.
- Reference corpus (cross-lap memory): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

Older dated HANDOFFs (the completed bounded Goodstein-termination run, etc.) are in
`archive/handoff/`.

# DIRECTION — read FIRST (operator directive, 2026-06-19, Trevor via Ren)

## ♾️ UNBOUNDED EXPEDITION. Build the *growth theory* behind Goodstein independence.

This is an **open-ended research run**, not a bounded "do X then stop" task. There is
NO self-stop sentinel and `--allow-stop` is OFF. You keep going, lap after lap, until
Trevor stops the treadmill. Do not look for a finish line. Slow, steady, real progress
is the whole point.

### What this run is (and why it's real progress on Kirby–Paris)
Goodstein's theorem (termination) is **already proved and axiom-clean** in this repo
(`Logic/Goodstein/`). The famous companion result is **Kirby–Paris (1982): Peano
Arithmetic cannot prove Goodstein's theorem.** The full PA-syntactic statement
(`PA ⊬ γ`) lives in a *separate* expedition (`~/src/goodstein-independence`) and needs
first-order-logic machinery you do NOT have here. **Do not attempt the syntactic
`PA ⊬ γ` statement in this repo.**

What you ARE building here is the **mathematical heart of why PA fails** — the part that
lives entirely in mathlib, with no logic/provability machinery:

> The Goodstein length function `goodsteinLength` grows like the fast-growing function
> `f_{ε₀}`. Every PA-provably-total function is dominated by some `f_α` with `α < ε₀`;
> `f_{ε₀}` (hence `goodsteinLength`) outgrows all of them. That growth gap is *the reason*
> PA can't prove termination.

You are formalizing the **growth side** of that argument: the growth theory of the
fast-growing hierarchy, the Hardy hierarchy, the Goodstein length function, and the
bridge between them. This is genuine, novel, mathlib-PR-shaped mathematics — none of it
is in mathlib or anywhere in the 705-repo Reservoir ecosystem (checked 2026-06-18).

---

## What mathlib ALREADY gives you (do NOT reinvent these)

`import Mathlib.SetTheory.Ordinal.Notation` — namespace `ONote`:
- **`ONote`** — computable ordinal notations below `ε₀` (CNF trees), with `repr : ONote → Ordinal`.
- **`ONote.fundamentalSequence : ONote → (Option ONote) ⊕ (ℕ → ONote)`** — computable
  fundamental sequences, with correctness `fundamentalSequence_has_prop` / `FundamentalSequenceProp`.
- **`ONote.fastGrowing : ONote → ℕ → ℕ`** — the fast-growing hierarchy `f_α`
  (`f₀ = succ`, `f_{α+1} n = f_α^[n] n`, `f_λ n = f_{λ[n]} n`). Characterization lemmas:
  `fastGrowing_zero'`, `fastGrowing_succ`, `fastGrowing_limit`, `fastGrowing_def`.
  Known values: `fastGrowing_zero`, `fastGrowing_one (= 2·n)`, `fastGrowing_two (= 2^n·n)`.
- **`ONote.fastGrowingε₀ : ℕ → ℕ`** — the one-step extension to `ε₀` itself, via the
  fundamental sequence `ω, ω^ω, ω^ω^ω, …`. Known: `fastGrowingε₀_zero (= 1)`,
  `fastGrowingε₀_one (= 2)`.
- **`ONote.NF`** (`class NF (o : ONote)`), `NFBelow`, normal-form API.
- Abstract layer (separate, on `Ordinal`): `Mathlib.SetTheory.Ordinal.FundamentalSequence`
  (`IsFundamentalSequence`, `exists_fundamental_sequence`, normality interaction) and
  `…/Veblen`, `…/CantorNormalForm`, `…/Arithmetic` (well-foundedness, `Ordinal.wellFoundedLT`).

mathlib proves the hierarchy's *small values* but **NONE of its growth theory** — no
expansiveness, no monotonicity, no domination, no Hardy hierarchy, no Ackermann, no
Goodstein. Those gaps are your targets.

---

## The milestone ladder (your runway — pick the next brick, hardest-relevant-first)

Work in NEW modules; never touch the five completed threads except to *read/reuse* them
(see Lane). Suggested layout (adapt as needed):
`Logic/FastGrowing/{Basic,Domination,Hardy,Anchors}.lean`, `Logic/Goodstein/{Length,Growth}.lean`.
**Wire every new file into `src/LeanFormalizations.lean`** (the lib only builds files
reachable from that root — an unimported file is invisible to the build gate).

### A. Growth theory of `ONote.fastGrowing`  (scaffold started in `FastGrowing/Basic.lean`)
- **A1. Expansiveness** `le_fastGrowing : n ≤ fastGrowing o n` (NF `o`). Transfinite
  induction on the notation via `fastGrowing_zero'/_succ/_limit`; the successor step needs
  "iterating a `≥ id` function stays `≥ id`". *(sorry'd target, lap-1 handle.)*
- **A2. Monotonicity in `n`** `fastGrowing_monotone : Monotone (fastGrowing o)` (NF `o`). *(sorry'd.)*
- **A3. Monotonicity in the index (THE FIRST CRUX).** The clean form is local, not
  "`α<β ⟹ ∀n f_α n ≤ f_β n`" (false for small `n`). Aim for the stepping stones the
  classical proof uses: `fastGrowing (o[n]) n ≤ fastGrowing o n` for limit `o`, and the
  successor comparison, building toward eventual domination. This is hard; **bang on it
  across laps** — a disclosed `sorry` on it is a checkpoint, not a reason to retreat.
- **A4. `fastGrowingε₀` dominates every fixed level (THE HEADLINE CRUX).**
  `∀ (o : ONote) [o.NF], ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n`. The
  unboundedness that *is* independence. Builds on A1–A3.

### B. The Hardy hierarchy `H_α`  (entirely absent from mathlib)
- **B1.** Define `hardy : ONote → ℕ → ℕ` mirroring `fastGrowing`'s structure
  (`H₀ n = n`, `H_{α+1} n = H_α (n+1)`, `H_λ n = H_{λ[n]} n`) on `fundamentalSequence`,
  with the same `termination_by`. Keep it **computable** (for anchors).
- **B2.** Characterization lemmas `hardy_zero'/_succ/_limit` (mirror `fastGrowing_*`).
- **B3.** Small-value + `native_decide` anchors (`hardy 0 n = n`, `hardy 1 n = n+1`, …).
- **B4. (stretch)** the classical identity `H_{ω^α} = f_α` — deep; a long-horizon target.

### C. Goodstein length ↔ hierarchy  (the crown jewel; reuses our `Engine`)
- **C1. ✅ started** `goodsteinLength` is defined in `Logic/Goodstein/Length.lean` with
  `native_decide` anchors (`0↦0, 2↦3, 3↦5`) and the `Nat.find` API
  (`goodsteinSeq_goodsteinLength`, `goodsteinLength_le`, `goodsteinSeq_ne_zero_of_lt`).
- **C2. The semantic bridge.** Relate our `Engine.toOrdinal`/`Engine.seqOrd` (which already
  maps each Goodstein term to an `Ordinal < ε₀` and is the descent that proves termination)
  to `ONote.repr`, so the Goodstein descent is expressed on `ONote`. *This is the reuse the
  expedition plan flagged: `Engine.lean`'s ε₀-descent IS the model-side content.*
- **C3. The growth theorem (headline of this run).** `goodsteinLength` eventually dominates
  every `fastGrowing o` (`o < ε₀`) — equivalently tracks `fastGrowingε₀`. Combines C2 + A4.
  State it as a thin **audit-surface** theorem delegating to the engine work, the way
  `Goodstein/Statement.lean` does. This is the formal "Goodstein grows too fast for PA."

**Ordering guidance:** A1/A2 and B1–B3 and C1 are achievable foundations that also unlock
anchors — get them solid. A3/A4/C2/C3 are the real cruxes; per the charter's hardest-first
rule, keep attacking them every lap (decompose, read the source, formalize the next
prerequisite, feed Aristotle) rather than only mopping up easy leaves. A lap that advances
a crux by one honest prerequisite — even leaving a disclosed `sorry` on the crux itself —
is a **successful lap**.

---

## Anti-vacuity locks (non-negotiable — this is metamath-adjacent; vacuous "wins" are the danger)
- **Every new computable function gets `native_decide` anchors** for small inputs, as
  standalone `example`s (off any headline axiom path). A wrong definition must fail them.
- **The headline growth theorem (C3) is the audit surface.** Keep its statement thin and
  faithful (delegate the proof to engine siblings), so a human can read it against the math.
- **No axiom-smuggling.** These targets are *constructible in mathlib* — never introduce an
  `axiom` for something that is supposed to be built (e.g. do NOT axiomatize a domination
  bound and call it done). A disclosed `sorry` on an open crux is fine and expected; a bare
  `axiom` standing in for the actual growth content is NOT.
- **Keep `#print axioms` clean on every *completed* theorem** = `[propext, Classical.choice,
  Quot.sound]`. `native_decide` may appear on standalone anchors but MUST NOT leak onto a
  headline theorem's axiom path. Run `#print axioms <thm>` when you close a real theorem.
- The five completed threads stay at **0 math axioms** — do not regress them.

---

## Lane discipline
- Work ONLY in `Logic/FastGrowing/` and `Logic/Goodstein/{Length,Growth}.lean` (new).
  You MAY read/reuse `Logic/Goodstein/{Defs,Engine,Statement}.lean` (especially
  `toOrdinal`, `seqOrd`, `seqOrd_step`, `goodstein_terminates`).
- **DO NOT TOUCH** the four other completed, axiom-clean threads:
  `NumberTheory/Transcendence/`, `Geometry/Constructible/`, `NumericalSemigroups/Curtis/`,
  `RealAnalysis/PowerTower/`. Do not modify, reopen, or re-axiomatize them.
- Do NOT start an unrelated new result to "keep busy." The growth theory above is a deep,
  many-lap runway; if one brick blocks, take another brick on the ladder — never leave the
  ladder.
- `Combinatorics/NoThreeInLine/` is unrelated pre-existing scratch — ignore it.

---

## Rules (same as every autonomous run here)
- **Commit every green build** from a real `lake build` you actually saw succeed. **NEVER push** (the host pushes).
- A `sorry` is a disclosed checkpoint, never a faked proof. Never claim green you didn't see.
- Verify lemma names against THIS repo's mathlib (`v4.29.1`). `push_neg` is deprecated → `push Not at h`.
- **Reference corpus** (your cross-lap memory, NOT auto-loaded): `ls`
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/` at lap start, and
  `grep -rl <keyword>` it before re-deriving any ordinal/`ONote`/`native_decide`/well-founded-recursion friction.
- **Aristotle:** keep one job in flight only while a genuinely-open lemma exists to feed it
  (a domination/iteration lemma is a good candidate). Verify any returned proof in-kernel +
  `#print axioms` before trusting; never re-submit something already proved locally.
- **Blocked needing the open web** (a textbook proof of fast-growing domination, the Hardy↔
  fast-growing identity, an existing formalization to port)? First check for answered
  `ON-LINE-FINDINGS-*.md`; else append a dated, specific item to `ON-LINE-REQUEST.md` and
  continue on another brick. Do not block.
- Keep `HANDOFF.md` current as you go; on the governor's budget signal, `/handoff` and end
  the lap (you'll be relaunched fresh, resumed from the HANDOFF).

## NOT a stop condition
There is no completion sentinel for this run. Do **not** write `$LEAN_STOP_SENTINEL`. Do
**not** stop because a milestone landed, "to take stock," or because the next crux is hard.
Reaching A1–A4 + B + C is *months* of real work; keep building. Trevor ends the run.

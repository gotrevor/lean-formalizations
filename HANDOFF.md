# HANDOFF — lean-formalizations (thin pointer)

## 👉 READ `DIRECTION.md` FIRST. UNBOUNDED expedition (growth theory behind Goodstein/Kirby–Paris). No self-stop.

This file is a **thin pointer**. The durable overview is **`STATUS.md`**; the per-lap baton
is the newest **`HANDOFF-<date>.md`**; open items/attack paths live in **`PENDING_WORK.md`**.

## Where things stand (2026-06-19 lap 3 — newest baton: `HANDOFF-2026-06-19-0641.md`)
- **C3 BUILT modulo one sorry.** The Cichoń identity `goodsteinLength m = H_{seqONote m 0}(2) − 2`
  is proved end-to-end except the `r=0 ∧ L≥1` "borrowing" case of `hstep_toONote`. New intrinsic
  Hardy machinery (`hstep`, `hardy_hstep`, `hstep_oadd_tail`) is axiom-clean. Crux submitted to
  Aristotle (job `77c99f0e`). Build 🟢 green (8288 jobs). See the dated baton for the full model.

## Where things stood (2026-06-19 lap 2)
- Branch `no-three-in-line`. Build 🟢 green (8287 jobs). `src/` is **sorry-free** and
  **0 math axioms**.
- **Section A COMPLETE + axiom-clean**: A1/A2/A3 **and now A4** — the headline crux
  `fastGrowing_lt_fastGrowingε₀` (`f_{ε₀}` dominates every fixed `f_o`), the unboundedness
  that *is* the Kirby–Paris growth gap. New engine in `Logic/FastGrowing/Domination.lean`:
  `norm`, `lt_fundamentalSequence_of_norm_le` (the genuinely new theorem), `reaches_of_lt`,
  `osucc`. Plus general index monotonicity `fastGrowing_le_of_lt` / `hardy_le_of_lt`.
- The `ON-LINE-REQUEST` fast-growing-norm ask was **self-resolved** (the `norm` derivation);
  request file removed.

- **C2 DONE** (`Logic/Goodstein/Growth.lean`): `toONote`, `repr_toONote`, `toONote_NF`, and
  the descent on `ONote` `seqONote_lt`. All axiom-clean.

## Next (see PENDING_WORK "ACTIVE FRONTIER")
1. **C3 — the growth theorem** (crown jewel): `goodsteinLength` tracks `fastGrowingε₀`.
   `goodsteinLength m` = length of the `seqONote m ·` descent; classically a **Hardy**
   function of `seqONote m 0`. Needs a "Hardy-counts-steps" identity, then combine with A4 +
   `hardy_le_of_lt`. Deep, multi-lap; `seqONote_lt` is the running start.
2. B4 (`H_{ω^α}=f_α`) — long-horizon trap under mathlib's `ω[n]=n+1`.

## Discipline
- Commit every green `lake build`. NEVER push. Verify `#print axioms` clean on closed theorems.
- Work only in `Logic/FastGrowing/*` + `Logic/Goodstein/{Length,Growth}`; don't touch the five frozen threads.
- Reference corpus (not auto-loaded): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

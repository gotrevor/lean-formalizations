# HANDOFF — lean-formalizations (thin pointer)

## 👉 READ `DIRECTION.md` FIRST. UNBOUNDED expedition (growth theory behind Goodstein/Kirby–Paris). No self-stop.

This file is a **thin pointer**. The durable overview is **`STATUS.md`**; the per-lap baton
is the newest **`HANDOFF-<date>.md`**; open items/attack paths live in **`PENDING_WORK.md`**.

## Where things stand (2026-06-19 lap 2)
- Branch `no-three-in-line`. Build 🟢 green (8287 jobs). `src/` is **sorry-free** and
  **0 math axioms**.
- **Section A COMPLETE + axiom-clean**: A1/A2/A3 **and now A4** — the headline crux
  `fastGrowing_lt_fastGrowingε₀` (`f_{ε₀}` dominates every fixed `f_o`), the unboundedness
  that *is* the Kirby–Paris growth gap. New engine in `Logic/FastGrowing/Domination.lean`:
  `norm`, `lt_fundamentalSequence_of_norm_le` (the genuinely new theorem), `reaches_of_lt`,
  `osucc`. Plus general index monotonicity `fastGrowing_le_of_lt` / `hardy_le_of_lt`.
- The `ON-LINE-REQUEST` fast-growing-norm ask was **self-resolved** (the `norm` derivation);
  request file removed.

## Next (see PENDING_WORK "ACTIVE FRONTIER")
1. **C2 — the bridge `toOrdinal` ↔ `ONote.repr`** (path 1: define `toONote`, prove
   `repr ∘ toONote = toOrdinal` + NF). The crown-jewel prerequisite.
2. **C3** — `goodsteinLength` tracks `fastGrowingε₀` (= C2 + A4). Deep, multi-lap.
3. B4 (`H_{ω^α}=f_α`) — long-horizon trap under mathlib's `ω[n]=n+1`.

## Discipline
- Commit every green `lake build`. NEVER push. Verify `#print axioms` clean on closed theorems.
- Work only in `Logic/FastGrowing/*` + `Logic/Goodstein/{Length,Growth}`; don't touch the five frozen threads.
- Reference corpus (not auto-loaded): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

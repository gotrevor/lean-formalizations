# HANDOFF — lean-formalizations (thin pointer)

## 👉 READ `DIRECTION.md` FIRST. UNBOUNDED expedition (growth theory behind Goodstein/Kirby–Paris). No self-stop.

This file is a **thin pointer**. The durable overview is **`STATUS.md`**; the per-lap baton
is the newest **`HANDOFF-<date>.md`**; open items/attack paths live in **`PENDING_WORK.md`**.

## Where things stand (2026-06-19 lap 8 — DEEP-REFLECTION lap; newest baton: `HANDOFF-2026-06-19-1117.md`)
- **DONE + axiom-clean:** A1–A4 (fast-growing growth theory, incl. `f_{ε₀}` domination =
  Kirby–Paris growth gap); B1–B3 (Hardy); C1, C2, **C3 — the Cichoń identity
  `goodsteinLength m = H_{seqONote m 0}(2) − 2`** (borrowing crux discharged lap 5); `f_1` dominated;
  `goodsteinLength` NON-ELEMENTARY. `src/` **sorry-free, 0 math axioms**; build 🟢 green (8289 jobs).
- **Lap-8 reflection call: direction SOUND, keep going.** All 12 headlines re-verified axiom-clean +
  faithful. Full synthesis in **`PENDING_WORK.md` → `## Reflection — 2026-06-19`** (read it).
- **The ONE remaining headline = the diagonal `f_o(m) ≤ goodsteinLength m + 2`** (every fixed `o`),
  machine-reduced (lap 6) to **sub-fact (ii)**: the descent stays `≥ ω^o` for `≥ m` steps (Cichoń's
  lower bound). NOT axiomatizable — keep as a disclosed open crux.

## Next (the lap-8 sharpened target — START HERE)
1. **The `o=2` diagonal `f_2(m) ≤ goodsteinLength m + 2`** — smallest open instance of the headline.
   Crack it by proving the **steps-between-drops base case**: leading CNF exponent stays `≥ 2` for
   `≥ m` steps. **Lap 8 completed the per-step leading-exponent characterization** (the prerequisite):
   `log_bump_pred_of_not_pow` (NO drop off pure powers) + `log_bump_pred_of_pow` (drop by EXACTLY 1
   at a pure power `n = b^log_b n`). Plus `leadExp_ge_of_not_pow` (unconditional non-decrease off
   pure powers) and **`ppCount` + `leadExp_ge_sub_ppCount`** (the sharpened telescope `log₂ m ≤
   leadExp_k + ppCount m k`). **⟹ the diagonal crux is REDUCED to ONE sparsity bound:**
   `ppCount m m ≤ log₂ m − 2` (correct implication, since ppCount is monotone) ⟹ `leadExp_k ≥ 2` for
   `k ≤ m` ⟹ `f_2(m) ≤ goodsteinLength m + 2`. **NEXT BRICK = prove the sparsity bound**
   `ppCount m m ≤ log₂ m − 2` (pure-power hits are extremely sparse among the huge early terms — the
   genuine steps-between-drops content). Two routes in `PENDING_WORK.md`. Cleanest Aristotle carve too
   (a slot is free). Also wired: `omega_opow_le_seqONote_repr` + `fastGrowing_step_le_goodsteinLength`.
2. **DO NOT** chase further *non-diagonal* lower-bound refinements — NON-ELEMENTARY is a complete,
   bankable result; iterating it would simulate progress without advancing sub-fact (ii).
3. B4 (`H_{ω^α}=f_α`) — long-horizon trap under mathlib's `ω[n]=n+1`. Lower priority.

## Discipline
- Commit every green `lake build`. NEVER push. Verify `#print axioms` clean on closed theorems.
- Work only in `Logic/FastGrowing/*` + `Logic/Goodstein/{Length,Growth}`; don't touch the five frozen threads.
- Reference corpus (not auto-loaded): `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.

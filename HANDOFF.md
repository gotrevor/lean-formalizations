# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (axiom ledger re-verified, what's happened). REFRESHED this lap.
2. **`PENDING_WORK.md`** — top is the dated **`## Reflection — 2026-06-19`** (the direction call). START HERE.
3. **newest dated `HANDOFF-2026-06-19-*.md`** — the per-lap baton (outcome + next actions).
   ✅ `STATUS.md` line 3's `🛑 FINISH-AND-STOP` directive (Trevor) is now **EXECUTED**: src/ sorry-free,
   headlines axiom-clean, off-headline work relocated to `wip/`, self-stopped.

## One-line state — PROJECT COMPLETE, self-stopped
**The no-three-in-line frontier is CLOSED to HJSW's optimal `3/2 − o(N)`, UNCONDITIONAL & axiom-clean**
(`weakPNT` discharged via in-repo Wiener–Ikehara), and **the classical Mertens trilogy is COMPLETE** —
1st, 2nd, and the sharp `e^{−γ}` 3rd (Limit B PROVEN), all axiom-clean. **All 17 headlines are
`[propext, Classical.choice, Quot.sound]`** (re-verified from real `#print axioms` this lap); `src/` has
**zero math axioms AND zero open `sorry`**. Per Trevor's FINISH-AND-STOP, this reflection lap completed
the wind-down: the three off-headline `sorry`s (`nagura_prime` + its `5/4` rung; the dead `prelim_decay_2/3`
island) were **quarantined into `wip/`**, and the complete Dirichlet divisor proof was restored into
`wip/DivisorProblem.lean` (from `d356584`) per the `wip/` convention. **`src/` is sorry-free** (governor
gate verified), build green (8297 jobs). → **self-stop armed.** No active frontier remains. If
FINISH-AND-STOP is lifted, see `PENDING_WORK.md` `## Reflection` for the (low-value, optional) next options.

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

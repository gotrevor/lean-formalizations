# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (axiom ledger re-verified, what's happened). REFRESHED this lap.
2. **`PENDING_WORK.md`** — top section is **`## ⭐ weakPNT DISCHARGED`**: open items + attack paths. START HERE for the next target.
3. **newest dated `HANDOFF-2026-06-19-*.md`** — the per-lap baton (latest lap's outcome + next actions).

## One-line state
**The general-`N` no-three-in-line frontier is CLOSED to HJSW's optimal `3/2 − o(N)`, and it is now
UNCONDITIONAL & axiom-clean** — `weakPNT` (the PNT) was discharged by porting PNTAnd's Wiener–Ikehara tower
in-repo. **Every headline in the repo is axiom-free** (`[propext, Classical.choice, Quot.sound]`); `src/`
carries **zero math axioms**. On the unlocked PNT layer, **Mertens' first theorem** is now in `Mertens.lean`
— vonMangoldt form, sharp **prime form** `∑_{p≤x}log p/p = log x + O(1)`, and `~ log` capstones, all
mathlib-absent and axiom-clean. Remaining open `sorry`s (all non-blocking, off every headline):
`nagura_prime` (superseded by the unconditional `3/2`) and `prelim_decay_2/3` (dead-code island in
`Wiener.lean`). **The classical Mertens TRILOGY is in `Mertens.lean`, all axiom-clean & mathlib-absent:**
1st (`∑log p/p = log x + O(1)`, prime + vonMangoldt, both `~ log`); 2nd (`∑1/p = log log x + O(1)`,
`mertens_second`, via Abel summation); 3rd up to the constant (`∏(1−1/p) ≍ 1/log N`,
`mertens_third_up_to_const`). **Next:** the sharp Mertens constants (`e^{−γ}` / Meissel–Mertens `M` / `γ`) —
see PENDING_WORK "NEXT TARGET" + newest dated `HANDOFF-2026-06-19-*.md`. Aristotle `0fa80268` working the
correction-series convergence.

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

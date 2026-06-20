# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (axiom ledger re-verified, what's happened). REFRESHED 2026-06-20.
2. **`PENDING_WORK.md`** — top is the dated **`## Completion-verification review lap — 2026-06-20`** (the
   self-stop direction call). START HERE.
3. **newest dated `HANDOFF-2026-06-20-1631.md`** — the per-lap baton (outcome + next actions).
   ✅ `STATUS.md`'s `🛑 FINISH-AND-STOP` directive (Trevor) is **EXECUTED & RE-VERIFIED**: src/ sorry-free,
   all 14 headlines axiom-clean (from real `#print axioms`), off-headline work in `wip/`, self-stopped.
   ✅ **Statements now also certified** (deep-reflection lap, 2026-06-20): fresh statement-faithfulness
   audit of every headline signature = all FAITHFUL; external-dep seam (`weakPNT`/flagship) axiom-clean
   through the dep. `#print axioms` certifies proofs; this closed the statement gap. Proofs + statements done.

## One-line state — PROJECT COMPLETE, self-stopped (re-verified 2026-06-20)
**The no-three-in-line frontier is CLOSED to HJSW's optimal `3/2 − o(N)`, UNCONDITIONAL & axiom-clean**
(`weakPNT` discharged), and **the classical Mertens trilogy is COMPLETE** — 1st, 2nd, and the sharp `e^{−γ}`
3rd (Limit B PROVEN), all axiom-clean. mathlib **v4.31.0 + de-vendor** done (PNTAnd is now a real lake dep);
the **BV-Fourier decay route-(b) bonus** is in `src/` (axiom-clean). **All 14 `.bump-axioms` headlines are
`[propext, Classical.choice, Quot.sound]`** (re-verified from real `#print axioms` this lap); `src/` has
**zero math axioms AND zero open `sorry`**; build green (8621 jobs). The complete Dirichlet divisor proof is
in `src/` (`DivisorProblem.lean`); the unfinished `nagura_prime` / dead `prelim_decay` island remain in
`wip/`. **The frontier is saturated** — the only repo-connected open item is the off-headline 🟠 sharp-`2π|u|`
wall (needs mathlib-absent signed-BV IBP; gates nothing). → **self-stopped.** If finish-and-stop is lifted,
see `PENDING_WORK.md` item 1 (sharp `2π|u|`, route (c)) for the one real multi-lap target.

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

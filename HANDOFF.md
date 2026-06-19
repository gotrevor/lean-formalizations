# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (axiom ledger re-verified, what's happened). REFRESHED this lap.
2. **`PENDING_WORK.md`** — the C₃=−γ / Limit B section has the full B0/B1/B2 decomposition + DONE markers. START HERE.
3. **newest dated `HANDOFF-2026-06-19-*.md`** (currently `…-2030`) — the per-lap baton (outcome + next actions).
   ⚠️ `STATUS.md` line 3 carries a `🛑 FINISH-AND-STOP` directive (Trevor): wind down to headline-only,
   self-stop, start no new side-quests. The `…-2030` handoff explains how this lap honored it (Dirichlet
   divisor side-quest built+verified+reverted; complete theorem preserved in git at `d356584`).

## One-line state
**The no-three-in-line frontier is CLOSED to HJSW's optimal `3/2 − o(N)`, UNCONDITIONAL & axiom-clean**
(`weakPNT` discharged via in-repo Wiener–Ikehara). **Every UNCONDITIONAL headline is axiom-free**
(`[propext, Classical.choice, Quot.sound]`); `src/` carries **zero math axioms**. **The classical Mertens
trilogy is now COMPLETE** — 1st, 2nd, AND the sharp `e^{−γ}` 3rd, all axiom-clean. As of this lap
(`MertensConstant.lean`) **Limit B is PROVEN** (`tendsto_primeZeta_add_logSub_limitB`), discharging the
deep Abelian/Tauberian crux `tendsto_sub_one_mul_integral_abelian` (`δ∫_0^∞ f·e^{−δx}→0`, ε–X argument),
so `mertens_third_classical_eGamma` (`∏(1−1/p)·log N→e^{−γ}`) and `mertensThirdConst_eq_neg_gamma`
(`C₃=−γ`) are UNCONDITIONAL. **No active frontier remains on the Mertens/NTL threads** — pick a fresh
mathlib-absent classical target (see `…-1639` handoff, Next action #1). The two open `sorry`s
(`nagura_prime` — needs effective PNT; `prelim_decay_2/3` — needs Stieltjes-IBP infra, unused) are genuine
infrastructure walls, off every complete thread. Aristotle correctly idle (the crux was a hand proof; the
rest is measure theory, its weak spot).

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

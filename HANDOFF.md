# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (axiom ledger re-verified, what's happened). REFRESHED this lap.
2. **`PENDING_WORK.md`** — the C₃=−γ / Limit B section has the full B0/B1/B2 decomposition + DONE markers. START HERE.
3. **newest dated `HANDOFF-2026-06-19-*.md`** (currently `…-1601`) — the per-lap baton (outcome + next actions).

## One-line state
**The no-three-in-line frontier is CLOSED to HJSW's optimal `3/2 − o(N)`, UNCONDITIONAL & axiom-clean**
(`weakPNT` discharged via in-repo Wiener–Ikehara). **Every UNCONDITIONAL headline is axiom-free**
(`[propext, Classical.choice, Quot.sound]`); `src/` carries **zero math axioms**. The classical Mertens
trilogy (1st, 2nd, 3rd sharp convergence forms) is complete & axiom-clean in `Mertens.lean`. **Active
frontier = the classical `e^{−γ}` Mertens 3rd**, reduced to ONE Tauberian limit **Limit B**
(`primeZeta s + log(s−1) → M − γ`) via `mertens_third_classical_of_tauberian`. This lap built the entire
analytic spine of Limit B in **`MertensConstant.lean`** (10 axiom-clean lemmas): brick B1 integral rep +
its `eˣ` form, the γ-injection `∫_0^∞ log u·e^{−u}=−γ`, the M-part, and the **log-part fully evaluated**
`(s−1)∫_0^∞ log x·e^{−(s−1)x} = −γ−log(s−1)`. **Sole remaining piece of Limit B = the Tauberian/Abelian
final-value step** `(s−1)∫_0^∞ r(x)e^{−(s−1)x}→0` (deep; see the `…-1601` handoff + PENDING_WORK). Other
open `sorry`s (`nagura_prime`, `prelim_decay_2/3`) are non-blocking, off every headline. Aristotle idle
(remaining work is measure theory, where it is weak — correct to leave idle).

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

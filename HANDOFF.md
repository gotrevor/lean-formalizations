# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`PENDING_WORK.md`** — top section is **`## Reflection — 2026-06-19`**: the durable direction call
   (KEEP / STOP / single highest-value next target). START HERE.
2. **`STATUS.md`** — the living overview (axiom ledger re-verified, what's happened). REFRESHED this lap.
3. **newest dated `HANDOFF-2026-06-19-1040.md`** — the per-lap baton (reflection-lap outcome + next actions).

## One-line state
**The general-`N` no-three-in-line constant frontier is CLOSED to HJSW's optimal `3/2 − o(N)`.** The
original mandated target (`hjsw_lower_bound`, 3N/2 at N=2p, axiom-clean in `Statement.lean`) is COMPLETE;
the audit surface + the two **unconditional** improvements past Bertrand `3/4` (`15/16`, `6/5`) are
axiom-clean. The flagship `maxNoThreeInLine_ge_three_halves_sub` (`3/2−o(N)`) rests on **one cited deep
axiom `weakPNT`** (the PNT, **🟠**). The six other threads (Curtis, power-tower, constructibles,
e/π-transcendence, Goodstein) are complete & axiom-clean. `src/` carries exactly one math axiom (`weakPNT`)
+ one non-blocking disclosed `sorry` (`nagura_prime`). **Next (per the Reflection):** decisively resolve
`weakPNT` — cheap dep-test → else wait-and-cite mathlib (it already has ζ≠0 on `Re=1`; only the
Wiener–Ikehara bridge is missing). Do NOT grind tighter elementary Chebyshev constants. Aristotle: only
IDLE jobs, nothing live.

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

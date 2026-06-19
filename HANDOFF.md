# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (where it stands, axiom ledger, what's happened).
2. **newest `HANDOFF-2026-06-19-*.md`** — the latest per-lap baton (exact next steps, gotchas).
3. **`PENDING_WORK.md`** — open items + the three attack paths for `hjsw_lower` (the crux).
4. Background: `DIRECTION.md` (operator directive), `Combinatorics/NoThreeInLine/PLAN.md` (frozen plan),
   `ON-LINE-REQUEST.md` (the network-gated blocker), `README.md`.

## One-line state
Five umbrella threads (Curtis, power-tower, constructibles, e/π-transcendence, Goodstein) complete &
axiom-clean. The **only** open obligation is `hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2*p)` (HJSW
`3N/2`, `Hyperbola.lean`) — a disclosed `sorry`. The geometric reduction (real-collinear ⇒ residues
mod-`p`-collinear ⇒ two lifts coincide) is formalized & axiom-clean; the remaining blocker is the
paper's explicit covering construction (filed in `ON-LINE-REQUEST.md`). `3(p−1)` is
native_decide-witnessed at p=5,7,11,13 (off-headline anchors).

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

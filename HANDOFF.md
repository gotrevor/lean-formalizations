# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **newest `HANDOFF-2026-06-19-0728.md`** — the lap that COMPLETED `hjsw_lower` (techniques, state).
2. **`STATUS.md`** — the living overview (axiom ledger, what's happened).
3. **`PENDING_WORK.md`** — open items (now: none open; only the open *math* Main Conjecture).

## One-line state
**HJSW DONE.** `hjsw_lower : 3*(p−1) ≤ maxNoThreeInLine (2*p)` is **fully proven, axiom-clean**
(`[propext, Classical.choice, Quot.sound]`, no `sorry`) as of HEAD `59b1fd8` — the crux
`shearSel_cross_diag` was discharged via the partner lemmas `shear_diag_partner`/`shear_anti_partner`.
Promoted to the audit surface (`Statement.lean`: `hjsw_lower_bound`) and extended to a `3N/4`
general-`N` bound (`maxNoThreeInLine_ge_three_quarters`, via Bertrand). **Zero `sorry` in the whole
repo**; all umbrella threads (Curtis, power-tower, constructibles, e/π-transcendence, Goodstein) and
the entire NTL formalization (upper `2N`, Erdős `Θ(N)`, HJSW `3N/2`) are complete & axiom-clean.
The only thing left in the no-three-in-line problem is the **Main Conjecture (open math)** — not a
formalizable proof target. See the newest HANDOFF for the (optional) next-lap menu.

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

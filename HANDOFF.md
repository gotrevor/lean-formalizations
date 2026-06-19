# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (axiom ledger, what's happened). REFRESHED this lap.
2. **`PENDING_WORK.md`** — active frontier + attack paths (top section is current).
3. **newest dated `HANDOFF-2026-06-19-0859.md`** — the per-lap baton (mental model + next actions).

## One-line state
**All NTL headlines proven & axiom-clean** (kernel-verified): `hjsw_lower` (3N/2 at N=2p), `2N` upper,
Erdős `Θ(N)`, general-`N` `3N/4`. The other five threads (Curtis, power-tower, constructibles,
e/π-transcendence, Goodstein) are complete & axiom-clean. **Active frontier** (HEAD `10c002b`): the
general-`N` *constant* (`3/4 → >3/4`) — genuine 🟡 debt. **KEY FINDING this lap:** crude Chebyshev
bounds **cannot** beat Bertrand's `c=2` for any `c<2`; the only route is a **refined** bound
`ψ(x)≳0.91x`, which mathlib lacks. **Built the entire prerequisite stack for it, axiom-clean** (keystone
`∑Λ(d)⌊n/d⌋=log(n!)`, the `2,3,5,30` floor combo ∈{0,1}, `T`-combination ≤ ψ(n), Stirling upper bound on
`log(m!)`, constant `A>0.91`, leading-term identity `=A·x`). Lone disclosed `sorry` in `src/` is still
`nagura_prime`. **Next: the analytic-half assembly `ψ(n) ≥ A·n − C log n`** (Stirling-floor error bounds)
— see HANDOFF-2026-06-19-0859 + PENDING_WORK top. Aristotle `1644a603` grinding `nagura_prime` cold.

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

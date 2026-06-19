# HANDOFF — no-three-in-line / HJSW frontier (isolated clone)

**You are in an ISOLATED CLONE** `~/src/lean-formalizations-ntl`, branch `ntl-hjsw`. Work ONLY here;
never touch the sibling `~/src/lean-formalizations`. This file is a **thin pointer** — the durable
content lives in the three docs below.

## Read these, in order
1. **`STATUS.md`** — the living overview (axiom ledger, what's happened). REFRESHED this lap.
2. **`PENDING_WORK.md`** — active frontier + attack paths (top section is current).
3. **newest dated `HANDOFF-2026-06-19-0845.md`** — the per-lap baton (mental model + next actions).

## One-line state
**All NTL headlines proven & axiom-clean** (kernel-verified): `hjsw_lower` (3N/2 at N=2p), `2N` upper,
Erdős `Θ(N)`, general-`N` `3N/4`. The other five threads (Curtis, power-tower, constructibles,
e/π-transcendence, Goodstein) are complete & axiom-clean. **NEW active frontier** (HEAD `bece6a8`):
the general-`N` *constant* (`3/4 → 5/4 → 3/2`) — genuine 🟡 debt vs. HJSW's actual `3N/2 − o(N)` for
all `N`. `PrimeGap.lean`: prime-gap interface + wired `5/4` payoff `maxNoThreeInLine_ge_five_fourths`;
crux `nagura_prime` (Nagura 1952, prime in `(n,6n/5]`) = the **one disclosed `sorry`** in `src/`,
gated on a Chebyshev θ lower bound mathlib lacks (ℕ foundation `four_pow_lt_mul_lcm` landed,
axiom-clean). Aristotle `1644a603` grinding `nagura_prime`. The Main Conjecture (`c·N`, `c≈1.87`)
stays open *math*. Next: the bridge `log(lcm(1..N)) = ψ N` (see PENDING_WORK top).

## Build
`lake build` (whole repo, ~seconds — mathlib prebuilt) or
`lake build LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola`. Commit green; never push.

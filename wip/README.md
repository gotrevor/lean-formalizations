# `wip/` — work-in-progress / quarantined Lean (NOT part of the build)

Files here are **outside `src/`**, so:
- `lake build` does **not** compile them (the `LeanFormalizations` lib globs only `src/`);
- the treadmill self-stop gate (`has_open_sorry`, which scans `src/**.lean`) does **not** see their
  `sorry`s — so a `sorry` here never blocks a self-stop or contradicts a "`src/` is sorry-free" claim.

They are git-tracked snapshots for preservation/resumption. They will generally **not** compile
standalone (their imports/context live in the `src/` files they came from). This mirrors the
`scratch/`/`notes/`/`wip/` convention used across the sibling formalization repos; ntl adopted it on
2026-06-19 during the FINISH-AND-STOP wind-down (a peer session flagged its absence).

## Contents

| file | status | provenance |
|---|---|---|
| `DivisorProblem.lean` | ✅ **COMPLETE, axiom-clean** (no `sorry`) — a finished *bonus* (Dirichlet's divisor problem `∑_{n≤N} d(n) = N log N + (2γ−1)N + O(√N)`), reverted from `src/` only because it is an adjacent non-headline side-quest under FINISH-AND-STOP. | restored verbatim from commit `d356584` |
| `NaguraFiveFourths.lean` | 🟡 **PARKED CRUX** — `nagura_prime` (the lap-crossing `sorry`) + its `5/4` rung. Superseded by the unconditional `6/5` and PNT `3/2−o(N)`; finishable via Nagura's tuned finite inequality. | excised from `Combinatorics/NoThreeInLine/PrimeGap.lean` |
| `WienerDecayIsland.lean` | ⬛ **DEAD CODE** — `prelim_decay_2/3` + `decay_alt`; two `sorry`s still open upstream (PNTAnd v4.30.0), need mathlib-absent BV-Stieltjes IBP; referenced nowhere. | excised from `NumberTheory/PrimeNumberTheorem/Wiener.lean` |

## To restore a file into the build

Move it back under `src/` (and, for `DivisorProblem.lean`, re-add its import to
`src/LeanFormalizations.lean`); for the two excised islands, paste the declarations back into the
`src/` file named in their headers. Everything is also recoverable from git history (the islands at the
parent of their excising commit; the divisor proof at `d356584`).

**Do not import anything here from `src/`** — that would pull a `sorry` (and the divisor side-quest)
back into the build and the headlines' axiom base.

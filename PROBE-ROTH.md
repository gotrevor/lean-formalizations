# Roth: freshness probe and plan (2026-09-28)

## Finding: Roth is already formalized in Lean 4

**Ralf Stephan (`rwst`), [Subspace-Theorems](https://github.com/rwst/Subspace-Theorems)**,
announced on Zulip 2026-09-25 (#Autoformalization › "Subspace Theorems formalized").  Created
2026-09-15, still active (HEAD `ce289c64`, 2026-09-28), Apache 2.0, Lean `v4.35.0-rc3` on mathlib
master, ~87 kLOC.  Aimed at Tau Ceti.  Covers Siegel's lemma, Roth (classical, number-field with
several places, `p`-adic), Ridout, Schmidt's Subspace Theorem, Evertse's counting.
`COMPARATOR.md` lists the certified statements; library dirs grep sorry-free (not built here).

Relevant names: `Rat.finite_setOf_ridout` (`DiophantineApproximation/Ridout.lean:188`),
`Real.irrationalityExponent_eq_two`, `NumberField.finite_setOf_prod_min_one_le`,
`Rat.finite_setOf_apply_intCast_sub_le`; Roth's lemma in `DiophantineApproximation/RothLemma.lean`.

## Elsewhere (searched 2026-09-28)

* **mathlib**: no Diophantine-Roth, Thue, Thue–Siegel or Dyson PR, open or closed.  Present:
  Siegel's lemma (`Mathlib/NumberTheory/SiegelsLemma.lean`, `NumberField/House.lean`), 2×2
  polynomial Wronskian, Liouville / `LiouvilleWith`, Dirichlet/Legendre, heights + Northcott.
  `docs/1000.yaml`: Thue–Siegel–Roth (Q751120) and Thue (Q2378270) unclaimed.  Nearby open PRs:
  Gelfond–Schneider via Siegel (Karatarakis, #35735 #39874 #39875), #42046 (Wronskian), #43595
  (`LiouvilleWith`).
* **Isabelle AFP**: no Roth; the Hančl–Rucki entry (Wenda Li) takes Roth as a locale assumption.
  Its 2021 "never formalized in any proof assistant" line is now stale.
* HOL Light, Metamath, math-comp: nothing found (weak negatives, partial code search).

## Plan

Peer, not race: reuse his proof, don't redo it.  Toolchains differ (his `v4.35.0-rc3`, ours
`v4.33.1`, bump gated on PNT+), so:

1. **Phase 12 (now)**: his `Rat.finite_setOf_ridout` enters verbatim as
   `Literature.Stephan2026Ridout`, a machine-checked input rather than a paper one; derive
   `Roth1955`, `Ridout1957SUnitDen`, `Mahler1957` (+ Dubickas's factor form) and Mills
   irrationality from it (`NumberTheory/Diophantine/StephanEdges.lean`).
2. **Once our toolchain reaches his** (fork `rwst/Subspace-Theorems` to `gotrevor/`, `require` at
   a SHA, never vendor): `Stephan2026Ridout := Rat.finite_setOf_ridout`, and Roth / Mahler / Mills
   irrationality become unconditional in this repo up to BHP + Matomäki.
3. Not implied by his statement: `Ridout1958` with general `p`-adic roots `ξ_r` (his targets are
   `0` and `∞` only), and full two-sided `Ridout1957` with exponent `μ + ν < 2`.  Neither is on a
   live path once Mahler routes through Stephan.

Our own Pottmeyer-based scaffold (index, counting lemma 2.6.4, auxiliary polynomial, Roth's lemma)
was drafted and discarded after this finding; the source notes are
`papers/pottmeyer-2022-dioapp.{pdf,txt}` (ch. 3) if a native proof is ever wanted.

## Bonus: the phase-9 wall

Phase 9 stopped at Corvaja–Zannier's main theorem, which rests on the `p`-adic (Schlickewei)
Subspace Theorem (`PROBE-DUBICKAS-NOSUBSPACE.md`).  Stephan's `COMPARATOR.md` lists the Subspace
Theorem over number fields with several places, including the affine `S`-integral form
(`NumberField.exists_finset_submodule_of_integer_of_affineProd_le`, 6.4) and Vojta's form (6.5).
So Dubickas's Lemma 6 may reduce to his theorems too: CZ 2004's argument on top of his Subspace
Theorem, not a proof of the Subspace Theorem.  Next probe after phase 12: state 6.2 or 6.4 verbatim
as a `Prop`, then try to derive `corvajaZannier_dichotomy` from it.

## Update 2026-09-29: Stephan also formalized Corvaja–Zannier 2004 (and Adamczewski–Bugeaud 2007)

Paper lanes beside the libraries: `CorvajaZannier2004/` (whole paper, 11 certified statements,
comparator `corvaja-zannier-2004.json`) and `AdamczewskiBugeaud2007/` (32).  Phase 13 (deriving CZ
from his Subspace Theorem, `CorvajaZannier.lean`) was stopped and superseded by phase 13b
(`CorvajaZannierStephan.lean`, from `Stephan2026CZMain` / `Stephan2026CZLemma4`).

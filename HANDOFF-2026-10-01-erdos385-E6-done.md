# HANDOFF: Erdős #463 almost-all (phase E6) DONE (2026-10-01)

`almost_all_erdos463` (Erdos463.lean) proved, `#print axioms` = {propext, Classical.choice, Quot.sound},
from `RichertZetaGrowth` only (+ the discharged MR16/MVT/MediumPNT inputs).

Mechanism: decouple the construction parameter from the margin.  Coefficients `coeffA (1/8) g Z`
(witness minFac ≥ (15/16)√Z); covering windows at δ = 1/16 (n ≤ (33/32)Z); shifted points
φ(n) = n + δ√n + 1, unit-separated, inside [Z, (17/16)Z − 1] for Z ≥ 10⁴.  `card_shift_le` is
`card_badWindow_le` generalized to any unit-separated family whose windows [φ n, φ n + h/2] carry no
witness.  Full build green (8860 jobs).  Branch `erdos-385-brun`.
Next: per DIRECTION.md (E5 on branch `erdos-385`; merge then compose BadCountExpBound).

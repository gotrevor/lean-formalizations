# HANDOFF 2026-10-01 — Erdős #385 E3c DONE (run stopped)

Branch `erdos-385`, HEAD `8707688` (+ this handoff commit).  `lake build` green.

## Done
`src/LeanFormalizations/NumberTheory/Erdos385/Rate.lean` sorry-free.  `almost_all_F385_rate`
(#{n ≤ X : F n < n + (1−δ)√n} ≤ C X exp(−c (log X)^{1/10})) depends only on
[propext, Classical.choice, Quot.sound], with the 4 literature Props as hypotheses.
New lemmas: `card_le_of_windows` (covering count, N₀ uniform in E and η), `badWindow_rate`,
`sqrt_le_rate`.  Trick: count E ∩ [2√X, ∞) so all relevant windows have Z ≥ √X and share one rate.

## Next (needs a new phase planted in DIRECTION.md)
- Exponent 1/3 − ε: needs a Vinogradov–Korobov-strength long-range average.
- The five `not_…` checks in `Literature/Erdos385AlmostAll.lean`: each must refute a wrong
  transcription of a literature Prop.
- Discharge candidates for the hypotheses: `MediumPNTStatement` (PNT+), `MontgomeryVaughanMVT`.

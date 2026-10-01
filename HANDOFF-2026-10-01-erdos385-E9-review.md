# HANDOFF 2026-10-01 — Erdős #385 phase E9b review lap (branch erdos-385-c)

Read DIRECTION.md → ⚡ CURRENT DIRECTIVE first (it outranks this file).

## Finding (review lap)
The planned next step (`largeValueCount_of_lit` from `NearOneLargeValues`) rested on
`nearOneLargeValues_of_density`, which is NOT derivable from density + Richert for a general C^∞
weight: the local explicit formula only localises a large value to within L of a zero, L = where
the Mellin tail drops below P^{−η}; slow-decay weights (`SlowMellinWeight`) give L = exp(√(η log P)),
too many large values for (log P)^{−2/3} ≪ η ≪ (log P)^{−1/2}.  Recorded: Maze row (frozen tier,
anchor `SlowMellinWeight`), revised docstring (10%) on the frozen theorem, now off-path.

## Re-route (built, green)
`largeValueCount_of_lit := largeValueCount_of_zeroDetect (localZeroDetect_of_richert h1) h2`.
- `PowerSaving/ZeroDetect.lean`: `LocalZeroDetect` (window A P^{η/3} log P, Re ≥ 1 − 2η − A loglogP/logP),
  `localZeroDetect_of_richert` (sorry, THE crux, route in header), `SlowMellinWeight` (Maze anchor).
- `PowerSaving/ZeroCount.lean`: `largeValueCount_of_zeroDetect` (sorry, transport, route in header).

## Next
Crux decomposition (a)(b)(c) in PENDING_WORK.md top section.  Start with (a) local_logDeriv_bound.

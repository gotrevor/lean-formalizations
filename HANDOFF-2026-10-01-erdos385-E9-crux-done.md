# HANDOFF 2026-10-01 — Erdős #385 E9b: crux `localZeroDetect_of_richert` PROVED (branch erdos-385-c)

Axiom-clean (A = 8).  New: `zc_horiz_right`, `zc_rect1`, `zc_split`, `zc_rect2` (ZeroContour.lean),
`zc_numeric`, `vkDev_lt_of_zeroFree` (ZeroDetect.lean).
Gotcha: the numerics needed their own lemma (`zc_numeric`) — nlinarith in the big context timed out;
`set` for constants also timed out (use `obtain ⟨Q, hQ⟩ : ∃ Q, Q = … := ⟨_, rfl⟩`).

## Next
1. Transport `largeValueCount_of_zeroDetect` (PowerSaving/ZeroCount.lean:34, header has route;
   riemannZeta_conj from PrimeNumberTheoremAnd.ZetaConj, IsCompact.inter_riemannZetaZeros_finite).
2. `nearOneLargeValues_of_density` (PowerSaving.lean:105) is OFF path / judged not derivable — once
   (1) closes, report via `box stuck` rather than fake it.

# HANDOFF 2026-10-01 — Erdős #385 E9b crux, step (a) done (branch erdos-385-c, HEAD 325b5f7)

Read DIRECTION.md → ⚡ CURRENT DIRECTIVE first: objective = `localZeroDetect_of_richert`
(PowerSaving/ZeroDetect.lean).  `nearOneLargeValues_of_density` is OFF path (do not work it).

## Done this lap (all compile, green, committed)
- Review lap (cde0101): re-route; `LocalZeroDetect` def + crux sorry; transport sorry
  `largeValueCount_of_zeroDetect` (ZeroCount.lean); Maze row anchored at `SlowMellinWeight`.
- PowerSaving/LocalLog.lean: `local_logDeriv_bound` PROVED (Landau at scale η₂, zero-free disc
  radius 5η₂/2 around 1+η₂+iy₀ ⇒ |ζ'/ζ(σ+iy₀)| ≤ K(log|y₀| + (loglog|y₀| + log(1/η₂) + 1)/η₂),
  σ ∈ [1−η₂, 1+3η₂], η₂ ≤ 1/8, |y₀| ≥ 16).
- PowerSaving/ContourTools.lean: `rect_shift_gen` ([σ₁,σ₂]×[−U,U]), `mellin_cube_decay`
  (‖F s‖(1+y²)³ ≤ K₃ on 1/2 ≤ Re ≤ 2), `norm_intervalIntegral_le_pi`, `zetaH_bound_right`
  (‖H w‖ ≤ 2/(Re w − 1) + C).
- PowerSaving/ZeroContour.lean: `zc_eventually` (all size conditions on P, eventually),
  `LocalLogProp` (= local_logDeriv_bound's shape), `box_H_bound` (zero-free window
  4P^{η/3}ℓ for Re ≥ 1−2η−8λ/ℓ ⇒ on Re w ∈ [1−η₂, 1+3η₂], |Im w − t| ≤ 2P^{η/3}ℓ:
  ζ w ≠ 0, w ≠ 1, ‖H w‖ ≤ 12K₁ℓ²+1; η₂ = η + 3λ/ℓ), `zcG` (G(s)=F(s)P^s H(s+it)) + diff/
  continuity/norm lemmas, `mellin_cube_le`, `zc_tail` (Re-2 tail beyond |y|=P ≤ K₃|H₂|π, integrable).

## Next (in ZeroContour.lean, then ZeroDetect.lean)
1. `zc_rect1`: rect_shift_gen on [c,2]×[−P,P], c = 1+1/ℓ; horizontals ‖G‖ ≤ K₃·Hc (‖F‖P² ≤ K₃),
   Hc = 2ℓ+CH; careful with ↑(2:ℝ) vs (2:ℂ).
2. `zc_split`: ∫_{−P}^{P} G(c+iy) = ∫_{−P}^{−L} + ∫_{−L}^{L} + ∫_L^P (integral_add_adjacent_intervals,
   continuity from `continuous_zcG_line`); outer ≤ K₃·E·Hc/L⁴·π via mellin_cube_le (M = L⁴), E ≥ P^c = eP.
3. `zc_rect2`: rect_shift_gen on [σ₁,c]×[−L,L] (hd from box_H_bound); left ≤ K·P^{σ₁}·H₁·π
   (mellin_pointwise), horizontals ≤ K₃/L⁶·E·H₁; P^{σ₁} = P^{1−η}/ℓ³.
4. `vkDev_lt_of_zeroFree` (A = 8): V4 `smoothTwist_sub_main_eq` (vkDev = smoothTwist − main, rfl),
   ‖∫g‖ ≤ tail + 2h₂ + 2t₃ + left + 2h₄ ≤ c₁ℓ + P^{1−η}Q/ℓ ≤ 2P^{1−η}; Q, c₁ as in zc_eventually.
   Pick constants: Q := K₃eπ(2+CH)/8 + Kπ(12K₁+1) + K₃e(12K₁+1)/32 + 1, c₁ := K₃(2+CH)π + 2K₃(2+CH) + 1.
5. `localZeroDetect_of_richert`: exists_support_Icc + contrapositive of 4 (A = 8).
6. Then the transport `largeValueCount_of_zeroDetect` (ZeroCount.lean header; riemannZeta_conj from
   PrimeNumberTheoremAnd.ZetaConj, IsCompact.inter_riemannZetaZeros_finite for ncard finiteness).
Note: scope gate wants PowerSaving.lean sorry-free, but `nearOneLargeValues_of_density` is judged
not derivable (~10%); once everything else closes, take `box stuck`/report rather than fake it.

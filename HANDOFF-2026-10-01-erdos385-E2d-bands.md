# HANDOFF 2026-10-01 — Erdős #385 E2d (MR16 Lemma 14) — all bands proved, assembly left
Branch `erdos-385-brun`, HEAD 373de44 (green). Target: `Erdos385/ShortSumParseval.lean`
(`mr16Lemma14_holds`, still `sorry`). All helpers in `Erdos385/Parseval/`, sorry-free:

* `Plancherel.lean`: `plancherel_lintegral` (f integrable, bounded, a.e. continuous), axiom-clean.
* `Bands.lean`: `plancherel_integral`, `plancherel_fourierInv`, `integral_conj_fourier_mul`,
  `integral_norm_sub_proj` (∫|f − 𝓕⁻(1_S 𝓕f)|² = ∫_{Sᶜ}|𝓕f|²).
* `Mellin.lean`: `Phi a N`, `fourier_Phi` (𝓕Φ = LSeries a (sArg ξ)/sArg ξ, sArg ξ = 1+2πiξ),
  `integrable_Phi`, `norm_Phi_le`, `ae_continuousAt_Phi`, `sum_Icc_eq_Phi` (short sum = winDelta Φ
  for non-integer x>0).
* `Low.lean`: `winDelta`, `winDif g h₁ h₂ x`, `winDif_fourierInv`, `norm_winDif_low`
  (‖winDif(𝓕⁻(1_S G/s))‖ ≤ 2R·K·(2·2πR·h₂/x), S ⊆ [−R,R]), `sArg_eq`.
* `Mid.lean`: `continuousOn_winDif`, `integral_winDif_mid_le` (∫_X^{2X}|winDif 𝓕⁻(G/s)|² ≤ 12X∫|G|²).
* `High.lean`: `lintegral_winDif_le` (∫⁻_{[X,2X]}‖winDif g‖² ≤ 432X³/h₁² ∫⁻‖g‖², g measurable).
* `Freq.lean`: `supp_floor`, `continuous_LSeries_line`, `norm_LSeries_line_le` (≤ 4).
* `Dyadic.lean`: `lintegral_tail_le` (∫⁻_{|t|>T₁} f/t² ≤ 2B/T₁² from block bounds B·T/T₁).
* `LogChange.lean`, `Kernel.lean`: substitution v=e^u bound; low kernel bound.

## Next: assembly in ShortSumParseval.lean (plan, C = 420 suffices)
N = ⌊4X⌋₊, Â ξ = LSeries a (sArg ξ), bands via t = 2πξ preimages:
Slo = {|2πξ| < T₀}, Smid = {T₀ ≤ |2πξ| ≤ X/h₁}, Sall = {|2πξ| ≤ X/h₁}.
P_lo = 𝓕⁻(Slo.ind(𝓕Φ)), P_mid = 𝓕⁻(Smid.ind 𝓕Φ) (= 𝓕⁻((Smid.ind Â)/s)), Φ_hi = Φ − 𝓕⁻(Sall.ind 𝓕Φ);
𝓕⁻ additive ⇒ Φ = P_lo + P_mid + Φ_hi, winDif linear.
1. If x ↦ ‖D‖² not IntegrableOn, integral is 0 ≤ RHS; else convert to lintegral on Ioc.
2. a.e. x (x ∉ ℕ): shortSumC = winDelta Φ (sum_Icc_eq_Phi).
3. ‖lo+mid+hi‖² ≤ 3(...) ; lintegral_add with measurability (Φ measurable via indicators).
4. lo: R₀ = T₀/2π, K = 4 ⇒ |D_lo| ≤ 8/(πT₀) using h₂ ≤ X/T₀³, x ≥ X.
   mid: 12X·(2π)⁻¹∫_{Tmid}|A|² (integral_comp_mul_left).
   hi: ∫⁻‖Φ_hi‖² = ∫_{Sallᶜ}|Â/s|² ≤ (2π)⁻¹·2B h₁²/X² (|s|² ≥ t², Dyadic with T₁ = X/h₁,
   hypothesis T ≥ X/(2h₁) covers T ≥ T₁; block bound ∫ ≤ B·h₁T/X = B·T/T₁).
5. Divide by X; constants ≤ 3(7/T₀ + 2·Mid + 138B).

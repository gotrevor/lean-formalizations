# HANDOFF 2026-10-01 — Erdős #385 phase E9 (branch erdos-385-c)

Scope: sorry-free Hyperbola.lean, PowerSaving.lean (+ helper dirs).

## Done (all axiom-clean)
- Hyperbola.lean: all four statements proved.
- PowerSaving.lean: `badCount_powerSaving` ⇐ headline; headline ⇐ `badWindowPowerSaving_of_lit`
  (PowerSaving/Assembly.lean) ⇐ two leaves (PowerSaving/Split.lean, Window.lean).
- Step 1 `longAveragePower_of_lit` PROVED (LongAverage, Primes, LongAveragePower .lean).
- Step 2 machinery: `Parseval.norm_winDif_fourierInv_le` (Near.lean), `Parseval.mr16_masked`
  (Masked.lean), `Parseval.far_split` (Bridge.lean): D = D_far + D_near for real coeffs,
  |D_near| ≤ ∫_{nearSet S r}|A(1+it)|, ∫_X^{2X} D_far² ≤ 500X(1/T₀ + masked mid + B).

## Open (2 sorries, PowerSaving.lean)
1. `differenceSplit_of_lit` — apply `far_split` with a = coeffA, h₁ = paramH1, h₂ = powerH,
   T₀ = Z^{c₀} (powerH = X/T₀³). Needs coeffA inputs: choose S = maximal 1-separated large-value
   set of P (|P(1+it)| ≥ Z^{−η₀/2}-ish, T₀ ≤ |t| ≤ 8X), r = 1;
   (i) ∫_{near}|A| ≤ 1/log³Z via NearOneLargeValues levels + VK η_min (smoothPrimeSumVK);
   (ii) masked mid/blocks ≤ C Z^{−c}: |P| small off near set (needs P's t-derivative bound to pass
   from S to its 1-neighbourhood, or define S as covering), Q by primeQ_meanSquare (MVT), T > 4X by
   coeffC_meanSquare. Norm/support of coeffC: copy from RateVK/General.lean ~1047.
   Suggest: first state NearFarInput Prop + prove DifferenceSplit ⇐ NearFarInput (pure wiring).
2. `nearOneLargeValues_of_density` (80%), untouched.

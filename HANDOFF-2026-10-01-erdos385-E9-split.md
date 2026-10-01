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

## Lap 2 (2026-10-01, HEAD 016d607): step 2 decomposed down to one analytic leaf
Chain (all proved, compiles): differenceSplit_of_lit ⇐ NearFarInput (NearFar.lean, far_split
wiring; T₀ existential in [Z^c₀/2, Z^c₀]) ⇐ NearSetLeaf (NearSet.lean: masked MVT for Q, MVT for A
for T > 3X; range |t| ≤ 7X) ⇐ LargeValueBound (LargeValues.lean: exists_separated_cover (Cover.lean)
+ empty-window pigeonhole) ⇐ LargeValueBoundP (|Q| ≤ 1) ⇐ LargeValueCount + PrimePFloor
(LargeValueSum.lean: SupSplit interval maxima + mod-4 split, LayerCake Σv ≤ 2M√V; Floor.lean
proves PrimePFloor from Richert via Gen.primeP_small a=1/4).  Also mellin_decay_two
(MellinDecay.lean), dev_lower (Deviation.lean).
Gotchas: `set` locals ⇒ linarith/isDefEq timeouts (use obtain/generalize); big theorems need
maxHeartbeats.

Open sorries (PowerSaving.lean): `largeValueCount_of_lit`, `nearOneLargeValues_of_density`.
NEXT: largeValueCount_of_lit from NearOneLargeValues (= nearOneLargeValues_of_density h1 h2):
 split T at R' = max 3 (2√Km u^{-1/2}); small part separated_card_le (≤ A u^{-1/2}, u ≤ 1);
 big part: dev_lower gives ‖vkDev‖ ≥ √Z u/2 = (√Z)^{1-η}, η = 2 log(2/u)/log Z; NOLV with
 f = cutoffDiv g, P = √Z, T = 16Z (≤ Z², Z ≥ 16); η ≤ 2η₀ + 2log2/log Z ≤ η₁;
 (16Z)^{Bη^{3/2}} ≤ (2/u)^{4|B|η^{1/2}} ≤ √2 u^{-1/2} once η ≤ 1/(64B²+1);
 η₀ := min(1/8, η₁/4, 1/(256(B²+1))).

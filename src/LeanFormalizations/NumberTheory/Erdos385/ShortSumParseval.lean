/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanFormalizations.Literature.Erdos385AlmostAll
import LeanFormalizations.NumberTheory.Erdos385.Parseval.Assembly

/-!
# Erdős #385: the short-sum Parseval bound (phase E2d)

One frozen statement, `mr16Lemma14_holds : MR16Lemma14` (Matomäki–Radziwiłł 2016 Lemma 14 in
Teräväinen's general-`T₀` form, two-sided, complex coefficients; see the Prop's docstring in
`Literature/Erdos385AlmostAll.lean`).  With it, E3's headline depends on one literature input,
Vinogradov–Korobov.

## Route (Plancherel in log coordinates, 80% it closes as stated)

Notation: `A(s) = LSeries a s`, `a` supported on `[X, 4X]`, `|a_m| ≤ 1`, so `A` is a finite sum
and `|A(1+it)| ≤ Σ_{X ≤ m ≤ 4X} 1/m ≤ 2` (crude, any absolute constant works).

1. **The L² carrier.**  Let `H(v) = Σ_{m ≤ v} a_m` and `Φ(u) = e^{-u} H(e^u)`.  `Φ = 0` for
   `u < log X`, and `Φ(u) = e^{-u} H(4X)` for `u ≥ log 4X`, so `Φ ∈ L¹ ∩ L²(ℝ)`.  Its Fourier
   transform (frequency `t`, kernel `e^{-itu}`) is `Φ̂(t) = A(1+it)/(1+it)`: integrate each step
   `a_m ∫_{log m}^∞ e^{-(1+it)u} du = a_m m^{-1-it}/(1+it)`.  For a.e. `x`,
   `S(x,h) = H(x+h) − H(x⁻) = (x+h) Φ(log(x+h)) − x Φ(log x)` (the integer points are null).
   Mathlib's Plancherel: `MeasureTheory.Lp.norm_fourier_eq` / `inner_fourier_eq`
   (`Mathlib/Analysis/Fourier/LpSpace.lean`, kernel `e^{-2πi⟨x,ξ⟩}`: rescale `t = 2πξ`).

2. **Frequency split.**  `Φ = Φ_lo + Φ_mid + Φ_hi`, Fourier projections onto `|t| < T₀`,
   `T₀ ≤ |t| ≤ X/h₁`, `|t| > X/h₁`.  `Φ_lo`, `Φ_mid` are band-limited, hence smooth, with
   `Φ_•(u) = (1/2π) ∫_• Φ̂(t) e^{itu} dt` (an L¹ integral).  `S` splits linearly into
   `S_lo + S_mid + S_hi`, and `|x+y+z|² ≤ 3(|x|²+|y|²+|z|²)`.

3. **Low part** (the only use of `h₂ ≤ X/T₀³`).  With `g_lo(v) = d/dv[v Φ_lo(log v)] =
   (1/2π) ∫_{|t|<T₀} A(1+it) v^{it} dt`, `S_lo(x,h)/h` is the average of `g_lo` over `[x, x+h]`,
   and `|g_lo'(v)| ≤ (1/2π) ∫_{|t|<T₀} |A| |t| / v dt ≤ 2T₀²/X`.  So
   `|S_lo(x,h₁)/h₁ − S_lo(x,h₂)/h₂| ≤ 2 h₂ · 2T₀²/X ≤ 4/T₀`, squared `≤ 16/T₀² ≤ 16/T₀`.

4. **Middle part.**  `S_mid(x,h)/h` is the average of `g_mid` over `[x, x+h]`.  Cauchy–Schwarz and
   Fubini: `∫_X^{2X} |S_mid(x,h)/h|² dx ≤ ∫_X^{3X} |g_mid(v)|² dv ≤ 3X ∫_ℝ |g_mid(e^u)|² du
   = 3X · (1/2π) ∫_{T₀ ≤ |t| ≤ X/h₁} |A(1+it)|² dt` (Plancherel: `g_mid(e^u)` has transform
   `A(1+it)` on the band).  Same for `h₂`.  After the `1/X`, this is the middle term.

5. **High part** (pure L², no averaging).  `|S_hi(x,h)/h|² ≤ (2/h²)((x+h)²|Φ_hi(log(x+h))|² +
   x²|Φ_hi(log x)|²)`, and `∫_X^{3X} v²|Φ_hi(log v)|² dv = ∫ e^{3u}|Φ_hi(u)|² du ≤ (3X)³ ‖Φ_hi‖²`
   over `u ≤ log 3X`.  Plancherel: `‖Φ_hi‖² = (1/2π) ∫_{|t|>X/h₁} |A(1+it)|²/(1+t²) dt`.  Cover
   `|t| > X/h₁` by dyadic blocks `T_k ≤ |t| ≤ 2T_k`, `T_k = 2^k X/h₁ ≥ X/(2h₁)`; on block `k`,
   `1/(1+t²) ≤ 1/T_k²` and the hypothesis gives `∫_block |A|² ≤ B h₁ T_k / X`.  So
   `‖Φ_hi‖² ≤ (1/2π) Σ_k B h₁/(X T_k) ≤ (1/2π) · 2B (h₁/X)²` (a sum of numbers, monotone
   convergence on the blocks).  Hence `(1/X)∫_X^{2X}|S_hi(x,h)/h|² ≪ (X²/h²)(h₁/X)² B ≤ B`
   for `h ∈ {h₁, h₂}` (as `h ≥ h₁`).

Total: `≤ C (1/T₀ + ∫_mid |A|² + B)`.  Every step is real analysis on explicit functions; no
Perron formula and no contour shift.  If one step stalls (likely the a.e. identity in 1 or the
band-limited inversion in 2), state it as a NAMED sub-lemma with a disclosed hole plus an English
paragraph and a confidence; that is an acceptable finish.

Frozen: this statement and everything in `Literature/` (do not edit any Prop).
-/

namespace Erdos385

open LeanFormalizations.Literature

/-- Matomäki–Radziwiłł Lemma 14 (Teräväinen Lemma 1 form), proved. -/
theorem mr16Lemma14_holds : MR16Lemma14 :=
  ⟨500, fun _ _ _ _ _ hX hT₀ hh₁ h12 h2X ha1 hsupp _ hB ↦
    Parseval.mr16_core hX hT₀ hh₁ h12 h2X ha1 hsupp hB⟩

end Erdos385

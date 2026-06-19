# Online findings — `prelim_decay_2/3` infra (answers ON-LINE-REQUEST UPDATE 3)

**Date:** 2026-06-19 (host fulfiller session)
**Answers:** UPDATE 3's low-priority ask — does recent mathlib / an open PR provide either (a) a
Lebesgue–Stieltjes integration-by-parts for BV functions, or (b) the L¹-translation bound
`∫‖ψ(t+h)−ψ(t)‖dt ≤ |h|·eVariationOn ψ univ`, to close the two ported `Wiener.lean` sorries?
**Sources read:** current `AlexKontorovich/PrimeNumberTheoremAnd` `Wiener.lean` (main / v4.30.0);
mathlib4 docs `Analysis/BoundedVariation`; mathlib PRs #19289 (Abel summation, merged) & the IBP Zulip
threads; Lean Zulip "Is there code for X?" mirror (`zulip-ro`).

---

## Headline: no free lunch — close from scratch, not by citation

**Both routes are ABSENT from mathlib, and the sorries are STILL open upstream.** Nothing to port,
nothing to cite. These two are correctly low-priority (dead code; clean `#print axioms WeakPNT''`).

### 1. Upstream PNTAnd still has these exact sorries (so the port is not stale)
Current PNTAnd `main` (v4.30.0) `Wiener.lean` carries `prelim_decay_2`/`prelim_decay_3` as `sorry`
— verified the faithful statements (note the sharp constant is `2π‖u‖`, not the weaker `4‖u‖` variant):

```lean
theorem prelim_decay_2 (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (hvar : BoundedVariationOn ψ Set.univ) (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (eVariationOn ψ Set.univ).toReal / (2 * π * ‖u‖)   -- sorry

theorem prelim_decay_3 (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (habscont : AbsolutelyContinuous ψ) (hvar : BoundedVariationOn (deriv ψ) Set.univ)
    (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (eVariationOn (deriv ψ) Set.univ).toReal / (2 * π * ‖u‖) ^ 2  -- sorry
```
(`prelim_decay` itself — the trivial `‖𝓕 ψ u‖ ≤ ∫‖ψ‖` — IS proved, via
`VectorFourier.norm_fourierIntegral_le_integral_norm`.) **Implication:** there is no newer upstream
proof to grab; the box's verbatim-with-sorry port reflects upstream exactly.

### 2. Route (a) — general Lebesgue–Stieltjes IBP for BV functions: NOT in mathlib
- mathlib HAS integration-by-parts only for **differentiable** integrands on finite intervals
  (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`), extendable to `Ioi`/infinite intervals via
  `MeasureTheory.intervalIntegral_tendsto_integral_Ioi` (Kontorovich's own pattern, Zulip thread
  "Integration by parts on infinite intervals", PR #10099).
- mathlib HAS **Abel summation** (PR **#19289**, *merged 2024-12-01*): `sum_mul_eq_sub_integral_mul`,
  `sum_Ioc_by_parts`, etc. — but that is the **discrete** Stieltjes-IBP (the summation side), not a
  general BV-function Lebesgue–Stieltjes IBP.
- mathlib's `StieltjesFunction` covers only **monotone** functions ("less general than bounded
  variation" — Junyan Xu, Zulip "winding number").
- A **general BV / Lebesgue–Stieltjes IBP** is being built only **out-of-mathlib** (Luccioli & Rémy
  Degenne, `testing-lower-bounds/ForMathlib/ByParts.lean`, Zulip 2024-07-19) — not upstreamed.
  ⟹ the sharp `TV/(2π‖u‖)` route has no mathlib hook; it would need this missing IBP built first.

### 3. Route (b) — L¹-translation bound `∫‖ψ(t+h)−ψ(t)‖ ≤ |h|·V(ψ)`: NOT pre-packaged, but BUILDABLE
- mathlib's `Analysis/BoundedVariation.lean` (`eVariationOn`/`BoundedVariationOn`) has **only**
  a.e.-differentiability lemmas (`LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem`,
  `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`, the Lipschitz variants). **No** integral
  bound, **no** translation lemma, **no** Fourier decay.
- mathlib HAS translation machinery (`integral_comp_add_right`, integrability-under-translation, Lᵖ
  continuity-of-translation) but **not** the *quantitative* TV bound.
- The bound itself is elementary from the `eVariationOn` definition (sup over partitions) + Fubini:
  `∫ ‖f(t+h)−f(t)‖ dt ≤ |h|·eVariationOn f univ`. It is the more **self-contained** of the two routes
  (gives the weaker `TV/(4‖u‖)` decay) and does not need the missing Lebesgue–Stieltjes IBP. So if
  these are ever closed, **route (b) built from scratch on `eVariationOn` is the lower-risk path** —
  a handful of new lemmas, no dependency on absent infra.

## Recommendation for a future lap
- Don't wait on mathlib or an upstream PNTAnd update — neither will hand you these. Both are absent;
  upstream is still `sorry`.
- Since they're dead code (`#print axioms WeakPNT''` clean), leave them unless you want full
  `sorry`-freedom in the ported file. If you do: prefer **route (b)** (self-contained, from
  `eVariationOn` + Fubini, weaker constant) over route (a) (needs a BV Lebesgue–Stieltjes IBP that
  mathlib lacks). Aristotle job `c6d615ee` is the active attempt on `prelim_decay_2`.
- Watch for a future mathlib PR adding **general BV / Lebesgue–Stieltjes integration by parts** (the
  Luccioli/Degenne `ForMathlib/ByParts` line) — that would unlock the sharp route (a).

**No open online requests remain after this.** Badge cleared by removing `ON-LINE-REQUEST.md`.

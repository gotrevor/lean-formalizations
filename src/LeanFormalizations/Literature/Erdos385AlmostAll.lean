/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Literature inputs for the Erdős #385 almost-all theorem (phase E3)

Statements only, never `axiom`s.  Each is faithful-or-weaker to the cited source, as transcribed in
`DOOR-ALMOSTALL-ERDOS-385.md`, section "E3 literature Props (corrected 2026-10-01)" (on `main`).  That
section supersedes the first-draft list: two first-draft Props were **false as written** (independent
referee, `PROOF-ERDOS-385-ALMOST-ALL.md` issues 3 and 4).

Every Prop here comes with a **known-false control**: a nearby wrong transcription, stated as a `def`,
with a frozen `theorem not_… : ¬ …` (body `sorry`).  A lap that proves a control has shown the
corresponding Prop has teeth in the place a mistranscription would have broken it.

* `MR16Lemma14`: Matomäki–Radziwiłł, Annals 2016, arXiv:1501.04585, Lemma 14 (two-sided form), with
  general `T₀` as in Teräväinen arXiv:1510.06005 Lemma 1.  Controls: `MR16Lemma14OneSided`,
  `MR16Lemma14NoH2Bound`.
* `MontgomeryVaughanMVT`: Iwaniec–Kowalski Thm 9.1 (Montgomery–Vaughan 1974), upper half.  Control:
  `MVTNoLengthTerm`.
* `VKZeroFreeLogDeriv`: Vinogradov–Korobov zero-free region with a log-derivative bound (Titchmarsh,
  2nd ed., Thms 6.19 and 3.11; ⚠️ theorem numbers from memory, 80%).  Controls: `VKZeroFreeAnyWidth`,
  `VKLogDerivNoPole`.
* `MediumPNTStatement`: PNT+'s `MediumPNT`, verbatim.  **Dischargeable**: `PrimeNumberTheoremAnd`
  (a dependency of this repo, rev `40e5246`) proves it as `MediumPNT`
  (`PrimeNumberTheoremAnd/MediumPNT.lean:3710`).  Not wired here only because that module's olean is
  not built at this pin (a long first build); wiring is `mediumPNTStatement_holds := MediumPNT`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Chebyshev

namespace LeanFormalizations.Literature

/-- `S(x, h) = ∑_{x ≤ m ≤ x + h} a_m` over integers `m` (for `x ≥ 0`). -/
noncomputable def shortSumC (a : ℕ → ℂ) (x h : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, a m

/-! ## Prop 1: the Parseval bound for short sums (MR16 Lemma 14) -/

/-- **Matomäki–Radziwiłł Lemma 14, two-sided, complex coefficients.**  For `X ≥ 2`, `T₀ ≥ 1`,
`2 ≤ h₁ ≤ h₂ ≤ X / T₀³`, `|a_m| ≤ 1` supported on `[X, 4X]`, with `A(s) = ∑ a_m m^{-s}`
(`LSeries a s`):
`(1/X) ∫_X^{2X} |S₁(x)/h₁ − S₂(x)/h₂|² dx ≤ C (1/T₀ + ∫_{T₀ ≤ |t| ≤ X/h₁} |A(1+it)|² dt + B)`
for every `B` dominating `sup_{T ≥ X/(2h₁)} (X/(h₁T)) ∫_{T ≤ |t| ≤ 2T} |A(1+it)|² dt`.

Source: arXiv:1501.04585 Lemma 14 and its proof (eq. (19)); general `T₀` as in Teräväinen
arXiv:1510.06005 Lemma 1.  Faithful-or-weaker: the printed statements integrate over `t > 0` only
(valid only for real `a_m`), print the tail threshold `X/h₁` where the proof gives `X/(2h₁)`, and
Teräväinen omits `|a_m| ≤ 1`, which MR's proof uses.  The two-sided form is what the proof proves for
complex `a_m`.  The `sup` is replaced by "every dominating `B`", which is equivalent and avoids
`iSup` junk values on unbounded sets. -/
def MR16Lemma14 : Prop :=
  ∃ C : ℝ, ∀ (X T₀ h₁ h₂ : ℝ) (a : ℕ → ℂ), 2 ≤ X → 1 ≤ T₀ → 2 ≤ h₁ → h₁ ≤ h₂ →
    h₂ ≤ X / T₀ ^ 3 → (∀ m, ‖a m‖ ≤ 1) → (∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) →
    ∀ B : ℝ, (∀ T : ℝ, X / (2 * h₁) ≤ T →
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B) →
      (1 / X) * ∫ x in X..(2 * X), ‖shortSumC a x h₁ / h₁ - shortSumC a x h₂ / h₂‖ ^ 2 ≤
        C * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁}, ‖LSeries a (1 + t * I)‖ ^ 2) + B)

/-- **Control 1a (wrong transcription): integrals over `t > 0` only.**  False for complex `a`:
`a_m = m^{-iτ} 1_{[X,2X)}(m)` with `τ = X/(10h₁)` makes the left side `≍ 1` (the `h₁`-window is
phase-coherent, the `h₂`-window cancels when `h₂ ≫ h₁`) while every `t > 0` integral is small
(DOOR "Control 1a").  The parameters must also send `h₁ → ∞` with `h₁ ≪ X`, because the tail term is
`≍ max(h₁/X, 1/h₁)` (mean value at `T ≫ X`): e.g. `h₁ = X^{1/3}`, `T₀ = X^{1/12}`, `h₂ = X/T₀³`. -/
def MR16Lemma14OneSided : Prop :=
  ∃ C : ℝ, ∀ (X T₀ h₁ h₂ : ℝ) (a : ℕ → ℂ), 2 ≤ X → 1 ≤ T₀ → 2 ≤ h₁ → h₁ ≤ h₂ →
    h₂ ≤ X / T₀ ^ 3 → (∀ m, ‖a m‖ ≤ 1) → (∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) →
    ∀ B : ℝ, (∀ T : ℝ, X / (2 * h₁) ≤ T →
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ t ∧ t ≤ 2 * T}, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B) →
      (1 / X) * ∫ x in X..(2 * X), ‖shortSumC a x h₁ / h₁ - shortSumC a x h₂ / h₂‖ ^ 2 ≤
        C * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ t ∧ t ≤ X / h₁}, ‖LSeries a (1 + t * I)‖ ^ 2) + B)

/-- **Control 1b (wrong transcription): the hypothesis `h₂ ≤ X / T₀³` dropped.**  False:
`a_m = m^{-iT₀/2} 1_{[X,2X)}(m)`, `h₂ = X`, makes the left side `≥ (1 − O(1/T₀) − O(T₀h₁/X))²`, while
the right side is `≪ C (1/T₀ + max(h₁/X, 1/h₁))`.  ⚠️ DOOR "Control 1b" takes `h₁ = 2`, which does
**not** refute it: the tail term is then `≍ 1/h₁ = 1/2`.  Take `h₁ = √X`, `T₀ = X^{1/4}`. -/
def MR16Lemma14NoH2Bound : Prop :=
  ∃ C : ℝ, ∀ (X T₀ h₁ h₂ : ℝ) (a : ℕ → ℂ), 2 ≤ X → 1 ≤ T₀ → 2 ≤ h₁ → h₁ ≤ h₂ →
    (∀ m, ‖a m‖ ≤ 1) → (∀ m : ℕ, ((m : ℝ) < X ∨ 4 * X < m) → a m = 0) →
    ∀ B : ℝ, (∀ T : ℝ, X / (2 * h₁) ≤ T →
        X / (h₁ * T) * ∫ t in {t : ℝ | T ≤ |t| ∧ |t| ≤ 2 * T}, ‖LSeries a (1 + t * I)‖ ^ 2 ≤ B) →
      (1 / X) * ∫ x in X..(2 * X), ‖shortSumC a x h₁ / h₁ - shortSumC a x h₂ / h₂‖ ^ 2 ≤
        C * (1 / T₀ + (∫ t in {t : ℝ | T₀ ≤ |t| ∧ |t| ≤ X / h₁}, ‖LSeries a (1 + t * I)‖ ^ 2) + B)

theorem not_MR16Lemma14OneSided : ¬ MR16Lemma14OneSided := by
  sorry

theorem not_MR16Lemma14NoH2Bound : ¬ MR16Lemma14NoH2Bound := by
  sorry

/-! ## Prop 2: the mean value theorem for Dirichlet polynomials -/

/-- **Montgomery–Vaughan mean value theorem, upper half.**
`∫_{-T}^{T} |∑_{n ≤ N} a_n n^{-it}|² dt ≤ C (T + N) ∑_{n ≤ N} |a_n|²`.

Source: Iwaniec–Kowalski Thm 9.1 (Montgomery–Vaughan 1974), as quoted in MR16 Lemma 6.  Weaker than
the source: upper bound only, unspecified `C`. -/
def MontgomeryVaughanMVT : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (T : ℝ) (a : ℕ → ℂ), 1 ≤ N → 0 < T → (∀ n, (n = 0 ∨ N < n) → a n = 0) →
    ∫ t in (-T)..T, ‖∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 ≤
      C * (T + N) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2

/-- **Control 2 (wrong transcription): the `+ N` length term dropped.**  False: `a_n = 1` for
`1 ≤ n ≤ N` and small `T` give a left side `≈ 2T N²` against `C T N`. -/
def MVTNoLengthTerm : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (T : ℝ) (a : ℕ → ℂ), 1 ≤ N → 0 < T → (∀ n, (n = 0 ∨ N < n) → a n = 0) →
    ∫ t in (-T)..T, ‖∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 ≤
      C * T * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2

theorem not_MVTNoLengthTerm : ¬ MVTNoLengthTerm := by
  sorry

/-! ## Prop 3: the Vinogradov–Korobov zero-free region with a log-derivative bound -/

/-- The Vinogradov–Korobov region at height `T`: `σ ≥ 1 − c₀ / ((log T)^{2/3} (log log T)^{1/3})`. -/
def InVKRegion (c₀ T σ : ℝ) : Prop :=
  1 - c₀ / (Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3)) ≤ σ

/-- **Vinogradov–Korobov, with a log-derivative bound.**  There are `c₀ > 0` and `C₀` such that for
`T ≥ 3`, `σ` in the VK region at height `T`, `|y| ≤ T`, `σ + iy ≠ 1`:
`ζ(σ + iy) ≠ 0` and `|ζ'/ζ(σ + iy) + 1/(σ + iy − 1)| ≤ C₀ log T`.

Source: Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., Thm 6.19 (region) and
Thm 3.11 (log-derivative bound from a region and a growth bound), `c₀` a fraction of the zero-free
constant.  ⚠️ Theorem numbers from memory, not re-opened (80%); the statement is textbook.  Weaker than
the source in the bound (`log T` instead of `(log T)^{2/3} (log log T)^{1/3}`).  The quantifier order
(`c₀, C₀` before `T`) is load-bearing: see `VKZeroFreeAnyWidth`. -/
def VKZeroFreeLogDeriv : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C₀ : ℝ, ∀ T σ y : ℝ, 3 ≤ T → InVKRegion c₀ T σ → |y| ≤ T →
    ((σ : ℂ) + y * I) ≠ 1 →
    riemannZeta (σ + y * I) ≠ 0 ∧
      ‖deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I) + 1 / (σ + y * I - 1)‖ ≤
        C₀ * Real.log T

/-- **Control 3a (wrong transcription): "for every width `c₀`".**  False: with `c₀` large the region
at `T = 3` contains `s = −2`, a trivial zero (`riemannZeta_neg_two_mul_nat_add_one 0`). -/
def VKZeroFreeAnyWidth : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∀ T σ y : ℝ, 3 ≤ T → InVKRegion c₀ T σ → |y| ≤ T →
    ((σ : ℂ) + y * I) ≠ 1 → riemannZeta (σ + y * I) ≠ 0

/-- **Control 3b (wrong transcription): the pole term `1/(s − 1)` dropped.**  False near `s = 1`:
at `σ = 1 + 1/T`, `y = 0`, `|ζ'/ζ| ≈ T > C₀ log T` for large `T`. -/
def VKLogDerivNoPole : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C₀ : ℝ, ∀ T σ y : ℝ, 3 ≤ T → InVKRegion c₀ T σ → |y| ≤ T →
    ((σ : ℂ) + y * I) ≠ 1 →
    ‖deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I)‖ ≤ C₀ * Real.log T

theorem not_VKZeroFreeAnyWidth : ¬ VKZeroFreeAnyWidth := by
  sorry

theorem not_VKLogDerivNoPole : ¬ VKLogDerivNoPole := by
  sorry

/-! ## Prop 4: PNT with the `MediumPNT` error term -/

/-- **PNT+ `MediumPNT`, verbatim:** `ψ(x) = x + O(x exp(−c (log x)^{1/10}))`.

Source: `PrimeNumberTheoremAnd.MediumPNT` (`PrimeNumberTheoremAnd/MediumPNT.lean:3710`, rev
`40e5246`, a dependency of this repo), which proves exactly this statement with `ψ = Chebyshev.psi`.
Discharge by `mediumPNTStatement_holds : MediumPNTStatement := MediumPNT` once that module is built at
this pin.  Its control lives with the short-interval node it feeds
(`Erdos385.ShortIntervalPNTUnitWindow`). -/
def MediumPNTStatement : Prop :=
  ∃ c > 0, (ψ - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))

end LeanFormalizations.Literature

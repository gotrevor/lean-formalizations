/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.Literature.Erdos385AlmostAll
import LeanFormalizations.NumberTheory.Erdos385.Graph

/-!
# Erdős #385: `F(n) ≥ n + (1 − δ)√n` for almost all `n` (phase E3)

Headline `almost_all_F385`: for every `δ ∈ (0, 1/4)`,
`#{n ≤ X : F(n) < n + (1 − δ)√n} = o(X)`, i.e. the graph node `AlmostAllF385`, from four literature
Props (`Literature/Erdos385AlmostAll.lean`).  Since `F(n) < n + √n` always, this gives
`F(n) = n + (1 + o(1))√n` off a density-zero set, sharper than Tao's `n^{1/2+o(1)}` remark (blog,
2024-08-19).  It says nothing about #385(i)/(ii) for every `n`: a variance bound controls measure only.

Route scaffolding (not a deliverable): `PROOF-ERDOS-385-ALMOST-ALL.md` on `main`, with the referee
section and the revision.  Lean parameters follow its §1 "Lean note": `T₀ = exp(κ (log Z)^{1/10})`
because the pinned PNT+ proves only `MediumPNT`; this keeps `o(X)` and weakens the rate to
`exp(−c (log Z)^{1/10})`.

## Frozen statements (do not edit; prove them)

Nodes and edges:
* `ShortIntervalPNT` (node) and `shortIntervalPNT_of_mediumPNT` (edge from `MediumPNTStatement`);
  control `not_shortIntervalPNTUnitWindow` (the lower limit on `H` is load-bearing).
* `SmoothPrimeSumVK` (node, the PROOF file's Lemma VK) and `smoothPrimeSumVK_of_VKZ` (edge from
  `VKZeroFreeLogDeriv`); control `not_smoothPrimeSumVKMRNorm_of_VK` (MR16's main-term normalisation is
  wrong under the standard Mellin transform).

Wiring (PROOF section in brackets):
* W0 `exists_admissible`: a smooth cutoff `g` with the §2 support and plateau exists.
* W1 `witness_margin` [Lemma 1]: a balanced semiprime witness in `[n − h, n − 1]` gives the margin.
* W2 `card_badWindow_le` [Lemma 2 + Chebyshev, §7]: the bad `n` in a window are at most
  `2 X D / μ²` once the long average is `≥ μ`.
* W2′ `longAverage_lower` [Lemma 3]: the long average is `≥ c₁ δ / log² Z`.
* W3 `variance_small` [Lemmas 4, 5, Prop 6]: `D ≤ C exp(−(κ/2)(log Z)^{1/10})`.
* Headline `almost_all_F385` [§7 covering].

## Route

* W1: `a_m ≠ 0` ⇒ `m = pq`, `p ≤ (1 − δ/4)√Z < √Z ≤ q`, so `m` is composite with `minFac m = p ≥
  (1 − δ/2)√Z`; then `F(n) ≥ m + p ≥ n − h + p ≥ n + (1 − 3δ/4)√Z ≥ n + (1 − δ)√n` using
  `√(1 + δ/2) ≤ 1 + δ/4`.
* W2: for bad `n` and `x ∈ [n − h, n − h/2]`, `[x, x + h₁] ⊂ [n − h, n − 1]`, so `S₁(x) = 0` by W1;
  those `x` lie in `[Z, (1 + δ/2)Z] ⊂ [X, 2X]`, where the integrand of `D` is then `≥ μ²`.
* W2′: the `q`-count is `π(x/p + h₂/p) − π(x/p)`; `ShortIntervalPNT` applies because
  `h₂/p ≥ y / (4T₀³)` and `κ` is small against its `c`; Mertens on `p/√Z ∈ [1 − 7δ/16, 1 − 5δ/16]`.
* W3: `A = PQ / log Z` (unique representation).  `MR16Lemma14` with `|a_m| ≤ 1/2`; middle term
  `≤ sup|P|² ∫|Q|²` with `sup_{T₀ ≤ |t| ≤ 8X} |P(1+it)| ≪ 1/T₀ + exp(−(log Z)^{1/3−ε})` from
  `SmoothPrimeSumVK` (P = √Z, T = 16Z) and `∫|Q|² ≪ (U + √Z)/(√Z log Z)` from `MontgomeryVaughanMVT`;
  the tail via the MVT on `A` itself.  The `1/T₀` term dominates.
* Headline: `κ = min(κ₀, 1)`, `μ = c₁ δ / log² Z`; W2 gives `#B_Z ≪ Z log⁴ Z exp(−(κ/2)(log Z)^{1/10})`
  per window; windows `Z_{j+1} = (1 + δ/4) Z_j` cover `[Z₀ + h, ∞)`; sum.
-/

open Real Filter MeasureTheory Complex
open scoped Chebyshev

namespace LeanFormalizations.Erdos385

open LeanFormalizations.Literature

/-! ## Nodes fed by the literature Props -/

/-- **Short-interval PNT** (DOOR Prop 4, Lean form): for some `c > 0`, every `y ≥ y₀` and
`y exp(−c (log y)^{1/10}) ≤ H ≤ y` give `π(y + H) − π(y) ≥ H / (2 log 2y)`. -/
def ShortIntervalPNT : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℝ, ∀ y H : ℝ, y₀ ≤ y →
    y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ H → H ≤ y →
    H / (2 * Real.log (2 * y)) ≤
      (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊

/-- **Control 4 (wrong transcription): any window `H ≥ 1`.**  False: `y = k! + 1`, `H = 1` has
`π(k! + 2) − π(k! + 1) = 0` (`k! + 2` is even), against a positive left side. -/
def ShortIntervalPNTUnitWindow : Prop :=
  ∃ y₀ : ℝ, ∀ y H : ℝ, y₀ ≤ y → 1 ≤ H → H ≤ y →
    H / (2 * Real.log (2 * y)) ≤
      (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊

/-- **Edge: `MediumPNT` ⇒ short-interval PNT.**  Difference `ψ(y + H) − ψ(y)`, discard prime powers
(`O(√y log y)`), partial summation; `c = c'/2`. -/
theorem shortIntervalPNT_of_mediumPNT (h : MediumPNTStatement) : ShortIntervalPNT := by
  sorry

theorem not_shortIntervalPNTUnitWindow : ¬ ShortIntervalPNTUnitWindow := by
  sorry

/-- **Lemma VK (smoothed twisted prime sums).**  For smooth `f` with compact support in `(0, ∞)`
and standard Mellin transform `mellin f s = ∫_0^∞ x^{s−1} f(x) dx`: for every `ε > 0` there is `C` with
`|∑ Λ(n) n^{−it} f(n/P) − mellin f (1 − it) P^{1−it}| ≤ C (P exp(−log P / (log T)^{2/3+ε}) log T + 1)`
for all `P ≥ 2`, `T ≥ 3`, `P ≤ T`, `|t| ≤ T/2`.  No factor `1/(1 − it)` in the main term
(`not_smoothPrimeSumVKMRNorm_of_VK`). -/
def SmoothPrimeSumVK : Prop :=
  ∀ f : ℝ → ℂ, (∀ k : ℕ, ContDiff ℝ k f) → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ P T t : ℝ, 2 ≤ P → 3 ≤ T → P ≤ T → |t| ≤ T / 2 →
      ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) * f (n / P)) -
          mellin f (1 - t * I) * (P : ℂ) ^ (1 - t * I)‖ ≤
        C * (P * Real.exp (-(Real.log P / Real.log T ^ ((2 : ℝ) / 3 + ε))) * Real.log T + 1)

/-- **Control 3d (wrong transcription): MR16's main term `mellin f (1 − it) P^{1−it} / (1 − it)`**,
which belongs to a different normalisation of the transform.  False under the standard one: at
`t = 1`, `T = P`, with a nonnegative bump `f` near `1`, the discrepancy is `≍ P`. -/
def SmoothPrimeSumVKMRNorm : Prop :=
  ∀ f : ℝ → ℂ, (∀ k : ℕ, ContDiff ℝ k f) → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ P T t : ℝ, 2 ≤ P → 3 ≤ T → P ≤ T → |t| ≤ T / 2 →
      ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) * f (n / P)) -
          mellin f (1 - t * I) * (P : ℂ) ^ (1 - t * I) / (1 - t * I)‖ ≤
        C * (P * Real.exp (-(Real.log P / Real.log T ^ ((2 : ℝ) / 3 + ε))) * Real.log T + 1)

/-- **Edge: VK region ⇒ Lemma VK.**  Mellin inversion on `Re s = 1 + 1/log P`, shift to
`σ₁ = 1 − (log T)^{−2/3−ε}` inside the region, residue `mellin f (1 − it) P^{1−it}` at `s = 1 − it`,
truncate at height `T/2` using the decay of `mellin f`.  PNT+'s smoothed-Chebyshev contour code
(`MediumPNT`) is this argument at `t = 0` with the classical region. -/
theorem smoothPrimeSumVK_of_VKZ (h : VKZeroFreeLogDeriv) : SmoothPrimeSumVK := by
  sorry

/-- **Control 3d, as a teeth test against the node:** Lemma VK and MR16's normalisation cannot both
hold.  Their main terms differ by `|mellin f (1 − i)| P / √2` at `t = 1`, `T = P`, which is `≍ P` for
a bump `f` near `1`, while both error terms are `o(P)`.  (Unconditional falsity would need Lemma VK
itself, so the test is stated relative to the node.) -/
theorem not_smoothPrimeSumVKMRNorm_of_VK (h : SmoothPrimeSumVK) : ¬ SmoothPrimeSumVKMRNorm := by
  sorry

/-! ## The construction (PROOF §2) -/

/-- An admissible cutoff: smooth, values in `[0, 1]`, support in `[1 − δ/2, 1 − δ/4]`, and `= 1` on
`J_δ = [1 − 7δ/16, 1 − 5δ/16]`. -/
def Admissible (δ : ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ k : ℕ, ContDiff ℝ k g) ∧ (∀ u, 0 ≤ g u ∧ g u ≤ 1) ∧
    (∀ u, g u ≠ 0 → 1 - δ / 2 ≤ u ∧ u ≤ 1 - δ / 4) ∧
    (∀ u, 1 - 7 * δ / 16 ≤ u → u ≤ 1 - 5 * δ / 16 → g u = 1)

/-- The witness coefficient `a_m = (1/log Z) ∑_{m = pq, √Z ≤ q ≤ (1+2δ)√Z} (log p) g(p/√Z)`, the sum
over primes `p ∣ m` with `m / p` prime. -/
noncomputable def coeffA (δ : ℝ) (g : ℝ → ℝ) (Z : ℝ) (m : ℕ) : ℝ :=
  (∑ p ∈ m.primeFactors,
      if (m / p).Prime ∧ √Z ≤ ((m / p : ℕ) : ℝ) ∧ ((m / p : ℕ) : ℝ) ≤ (1 + 2 * δ) * √Z
      then Real.log p * g (p / √Z) else 0) / Real.log Z

/-- `S(x, h) = ∑_{x ≤ m ≤ x + h} a_m` over integers `m`. -/
noncomputable def shortSum (a : ℕ → ℝ) (x h : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, a m

/-- `X = (1 − δ/2) Z`. -/
noncomputable def paramX (δ Z : ℝ) : ℝ := (1 - δ / 2) * Z

/-- `h = (δ/4) √Z`. -/
noncomputable def paramH (δ Z : ℝ) : ℝ := δ / 4 * √Z

/-- `h₁ = ⌊h/2⌋ − 1`. -/
noncomputable def paramH1 (δ Z : ℝ) : ℝ := (⌊paramH δ Z / 2⌋₊ : ℝ) - 1

/-- `T₀ = exp(κ (log Z)^{1/10})` (the `MediumPNT` choice). -/
noncomputable def paramT0 (κ Z : ℝ) : ℝ := Real.exp (κ * Real.log Z ^ ((1 : ℝ) / 10))

/-- `h₂ = X / T₀³`. -/
noncomputable def paramH2 (δ κ Z : ℝ) : ℝ := paramX δ Z / paramT0 κ Z ^ 3

/-- The variance `D = (1/X) ∫_X^{2X} (S₁(x)/h₁ − S₂(x)/h₂)² dx`. -/
noncomputable def variance (δ κ : ℝ) (g : ℝ → ℝ) (Z : ℝ) : ℝ :=
  (1 / paramX δ Z) * ∫ x in (paramX δ Z)..(2 * paramX δ Z),
    (shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
      shortSum (coeffA δ g Z) x (paramH2 δ κ Z) / paramH2 δ κ Z) ^ 2

/-- The bad `n` in the window `[Z + h, (1 + δ/2) Z]`. -/
def badWindow (δ Z : ℝ) : Set ℕ :=
  {n | Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z ∧ (F n : ℝ) < n + (1 - δ) * √n}

/-! ## Wiring -/

/-- **W0.** An admissible cutoff exists (e.g. from `ContDiffBump`). -/
theorem exists_admissible {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) : ∃ g, Admissible δ g := by
  let f : ContDiffBump (1 - 3 * δ / 8 : ℝ) :=
    ⟨δ / 16, δ / 8, by positivity, by linarith⟩
  refine ⟨f, fun k => f.contDiff, fun u => ⟨f.nonneg, f.le_one⟩, fun u hu => ?_, fun u h1 h2 => ?_⟩
  · have : u ∈ Function.support f := hu
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at this
    have hr : f.rOut = δ / 8 := rfl
    rw [hr] at this
    constructor <;> linarith [this.1, this.2]
  · apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have hr : f.rIn = δ / 16 := rfl
    rw [hr]
    constructor <;> linarith

/-- **W1 (Lemma 1).**  A balanced semiprime witness in `[n − h, n − 1]` gives
`F(n) ≥ n + (1 − δ)√n`. -/
theorem witness_margin {δ Z : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 1 < Z) {g : ℝ → ℝ}
    (hg : Admissible δ g) {n m : ℕ} (hn : Z + paramH δ Z ≤ n) (hn' : (n : ℝ) ≤ (1 + δ / 2) * Z)
    (hm : (n : ℝ) - paramH δ Z ≤ m) (hmn : m < n) (ha : coeffA δ g Z m ≠ 0) :
    (n : ℝ) + (1 - δ) * √n ≤ F n := by
  have hsZ : 0 < √Z := Real.sqrt_pos.2 (by linarith)
  unfold coeffA at ha
  obtain ⟨p, hpm, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (div_ne_zero_iff.1 ha).1
  split_ifs at hp with hq <;> [skip; exact absurd rfl hp]
  obtain ⟨hqp, hq1, hq2⟩ := hq
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
  have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hpm
  have hgp : g (p / √Z) ≠ 0 := right_ne_zero_of_mul hp
  obtain ⟨hp1, hp2⟩ := hg.2.2.1 _ hgp
  rw [le_div_iff₀ hsZ] at hp1
  rw [div_le_iff₀ hsZ] at hp2
  set q := m / p with hqdef
  have hmpq : m = p * q := (Nat.mul_div_cancel' hpd).symm
  have hpq : (p : ℝ) < q := by nlinarith
  have hpq' : p < q := by exact_mod_cast hpq
  have hmin : m.minFac = p := by
    have hm1 : m ≠ 1 := fun h => by
      rw [hmpq] at h; exact hpp.ne_one (Nat.eq_one_of_mul_eq_one_right h)
    have hmp := Nat.minFac_prime hm1
    have hdvd : m.minFac ∣ p * q := hmpq ▸ Nat.minFac_dvd m
    rcases (Nat.Prime.dvd_mul hmp).1 hdvd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hmp hpp).1 h
    · have := (Nat.prime_dvd_prime_iff_eq hmp hqp).1 h
      have := Nat.minFac_le_of_dvd hpp.two_le hpd
      omega
  have hcomp : Composite m := by
    refine ⟨by rw [hmpq]; nlinarith [hpp.two_le, hqp.two_le], fun hmP => ?_⟩
    have := (Nat.prime_mul_iff.1 (hmpq ▸ hmP))
    rcases this with ⟨-, h⟩ | ⟨-, h⟩
    · exact hqp.ne_one h
    · exact hpp.ne_one h
  have hF := add_minFac_le_F hmn hcomp
  rw [hmin] at hF
  have hF' : (m : ℝ) + p ≤ F n := by exact_mod_cast hF
  -- √n ≤ (1 + δ/4) √Z
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsn : √(n : ℝ) ≤ (1 + δ / 4) * √Z := by
    rw [show (1 + δ / 4) * √Z = √((1 + δ / 4) ^ 2 * Z) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ δ ^ 2 * Z := mul_nonneg (sq_nonneg δ) (by linarith)
    nlinarith
  unfold paramH at hm
  have : (1 - δ) * √(n : ℝ) ≤ (1 - δ) * ((1 + δ / 4) * √Z) :=
    mul_le_mul_of_nonneg_left hsn (by linarith)
  have hd2 : 0 ≤ δ ^ 2 * √Z := by positivity
  nlinarith

/-- **W2 (Lemma 2 + Chebyshev).**  If the long average is `≥ μ` on `[Z, (1 + δ/2) Z]`, the bad `n` in
the window number at most `2 X D / μ²`. -/
theorem card_badWindow_le {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∀ᶠ Z : ℝ in atTop, ∀ μ : ℝ, 0 < μ →
      (∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z →
        μ ≤ shortSum (coeffA δ g Z) x (paramH2 δ κ Z) / paramH2 δ κ Z) →
      ((badWindow δ Z).ncard : ℝ) ≤ 2 * paramX δ Z * variance δ κ g Z / μ ^ 2 := by
  sorry

/-- **W2′ (Lemma 3).**  For `κ` small against `MediumPNT`'s constant, the long average is
`≥ c₁ δ / log² Z` on `[Z, (1 + δ/2) Z]`. -/
theorem longAverage_lower (hPNT : MediumPNTStatement) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ g : ℝ → ℝ, Admissible δ g →
      ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ Z : ℝ in atTop, ∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z →
        c₁ * δ / Real.log Z ^ 2 ≤ shortSum (coeffA δ g Z) x (paramH2 δ κ Z) / paramH2 δ κ Z := by
  sorry

/-- **W3 (Lemmas 4, 5, Proposition 6).**  `D ≤ C exp(−(κ/2)(log Z)^{1/10})` for large `Z`. -/
theorem variance_small (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT) (hVK : SmoothPrimeSumVK)
    (hPNT : MediumPNTStatement) {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hκ : 0 < κ)
    (hκ' : κ ≤ 1) {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∃ C : ℝ, ∀ᶠ Z : ℝ in atTop,
      variance δ κ g Z ≤ C * Real.exp (-(κ / 2) * Real.log Z ^ ((1 : ℝ) / 10)) := by
  sorry

/-! ## Headline -/

/-- **Theorem A (Lean form): `F(n) ≥ n + (1 − δ)√n` for almost all `n`**, i.e. the graph node
`AlmostAllF385`, from the four literature Props. -/
theorem almost_all_F385 (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT) (h3 : VKZeroFreeLogDeriv)
    (h4 : MediumPNTStatement) : AlmostAllF385 := by
  sorry

end LeanFormalizations.Erdos385

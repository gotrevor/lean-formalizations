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
  rintro ⟨y₀, hy⟩
  set N : ℕ := ⌈y₀⌉₊ + 1
  have hN : y₀ ≤ (N : ℝ) := by
    have := Nat.le_ceil y₀; simp only [N]; push_cast; linarith
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have h := hy (2 * N + 1) 1 (by linarith) le_rfl (by linarith)
  have e1 : ⌊(2 * N + 1 : ℝ) + 1⌋₊ = 2 * N + 2 := by
    rw [show (2 * N + 1 : ℝ) + 1 = ((2 * N + 2 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have e2 : ⌊(2 * N + 1 : ℝ)⌋₊ = 2 * N + 1 := by
    rw [show (2 * N + 1 : ℝ) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hnp : ¬ (2 * N + 2).Prime := by
    intro hp
    have := hp.eq_one_or_self_of_dvd 2 ⟨N + 1, by ring⟩
    omega
  have e3 : Nat.primeCounting (2 * N + 2) = Nat.primeCounting (2 * N + 1) := by
    simp only [Nat.primeCounting, Nat.primeCounting']
    rw [Nat.count_succ (p := Nat.Prime) (n := 2 * N + 2), if_neg hnp, add_zero]
  rw [e1, e2, e3, sub_self] at h
  have hpos : 0 < Real.log (2 * (2 * N + 1 : ℝ)) := Real.log_pos (by
    have : (0 : ℝ) ≤ N := by positivity
    linarith)
  have : (0 : ℝ) < 1 / (2 * Real.log (2 * (2 * N + 1 : ℝ))) := by positivity
  linarith

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

/-! ## Measure-theoretic helpers for the short sums -/

theorem measurable_shortSum (a : ℕ → ℝ) (h : ℝ) : Measurable fun x => shortSum a x h := by
  have hf : Measurable fun p : ℕ × ℕ => ∑ m ∈ Finset.Icc p.1 p.2, a m := measurable_of_countable _
  exact hf.comp (measurable_id.nat_ceil.prodMk (measurable_id.add_const h).nat_floor)

theorem abs_shortSum_le (a : ℕ → ℝ) {h U x : ℝ} (hx : x ≤ U) (hh : 0 ≤ h) :
    |shortSum a x h| ≤ ∑ m ∈ Finset.range (⌊U + h⌋₊ + 1), |a m| := by
  unfold shortSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_range]
    have := Nat.floor_le_floor (show x + h ≤ U + h by linarith)
    omega
  · intros; exact abs_nonneg _

theorem integrableOn_sq_shortSum (a : ℕ → ℝ) {h₁ h₂ L U : ℝ} (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) :
    IntegrableOn (fun x => (shortSum a x h₁ / h₁ - shortSum a x h₂ / h₂) ^ 2) (Set.Ioc L U) := by
  set B₁ := ∑ m ∈ Finset.range (⌊U + h₁⌋₊ + 1), |a m|
  set B₂ := ∑ m ∈ Finset.range (⌊U + h₂⌋₊ + 1), |a m|
  refine Measure.integrableOn_of_bounded (M := (|B₁ / h₁| + |B₂ / h₂|) ^ 2) measure_Ioc_lt_top.ne
    ((((measurable_shortSum a h₁).div_const _).sub
      ((measurable_shortSum a h₂).div_const _)).pow_const 2).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have e1 := abs_shortSum_le a hx.2 hh₁
  have e2 := abs_shortSum_le a hx.2 hh₂
  rw [Real.norm_eq_abs, abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg _)
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right (e1.trans (le_abs_self _)) (abs_nonneg _)
  · rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right (e2.trans (le_abs_self _)) (abs_nonneg _)

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
  have hsq : Tendsto (fun Z : ℝ => δ / 4 * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
  filter_upwards [eventually_gt_atTop 1, hsq.eventually_ge_atTop 2] with Z hZ hh μ hμ hlong
  set h := paramH δ Z with hhdef
  have hh' : 2 ≤ h := hh
  set X := paramX δ Z with hX
  have hX0 : 0 < X := by rw [hX, paramX]; nlinarith
  set f := fun x => (shortSum (coeffA δ g Z) x (paramH1 δ Z) / paramH1 δ Z -
      shortSum (coeffA δ g Z) x (paramH2 δ κ Z) / paramH2 δ κ Z) ^ 2 with hf
  have hH1 : paramH1 δ Z ≤ h / 2 - 1 := by
    unfold paramH1; have := Nat.floor_le (show 0 ≤ paramH δ Z / 2 by linarith); linarith
  have hH1' : 0 ≤ paramH1 δ Z := by
    unfold paramH1
    have : (1 : ℝ) ≤ ⌊paramH δ Z / 2⌋₊ := by
      have : 1 ≤ ⌊paramH δ Z / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    linarith
  have hH2 : 0 ≤ paramH2 δ κ Z := by unfold paramH2; rw [← hX]; exact div_nonneg hX0.le (by unfold paramT0; positivity)
  -- the bad set is finite
  classical
  set N := ⌊(1 + δ / 2) * Z⌋₊ + 1
  set T := (Finset.range N).filter (· ∈ badWindow δ Z)
  have hBT : badWindow δ Z = ↑T := by
    ext n; simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · intro hn; refine ⟨?_, hn⟩
      have := Nat.le_floor hn.2.1; omega
    · exact fun h => h.2
  rw [hBT, Set.ncard_coe_finset]
  -- unit intervals
  set J : ℕ → Set ℝ := fun n => Set.Ico ((n : ℝ) - h) ((n : ℝ) - h + 1)
  have hJ : ∀ n ∈ T, ∀ x ∈ J n, μ ^ 2 ≤ f x ∧ X < x ∧ x ≤ 2 * X := by
    intro n hn x hx
    obtain ⟨hn1, hn2, hn3⟩ := (Finset.mem_filter.1 hn).2
    obtain ⟨hx1, hx2⟩ := hx
    have hxZ : Z ≤ x := by linarith
    have hxZ' : x ≤ (1 + δ / 2) * Z := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have hS1 : shortSum (coeffA δ g Z) x (paramH1 δ Z) = 0 := by
        unfold shortSum
        refine Finset.sum_eq_zero fun m hm => ?_
        by_contra ha
        rw [Finset.mem_Icc] at hm
        have hm1 : x ≤ m := (Nat.ceil_le).1 hm.1
        have hm2 : (m : ℝ) ≤ x + paramH1 δ Z :=
          (Nat.le_floor_iff (by linarith)).1 hm.2
        have hmn : m < n := by
          have : (m : ℝ) < n := by linarith
          exact_mod_cast this
        have := witness_margin hδ hδ' hZ hg hn1 hn2 (by linarith) hmn ha
        linarith
      have := hlong x hxZ hxZ'
      simp only [hf, hS1, zero_div, zero_sub, neg_sq]
      exact pow_le_pow_left₀ hμ.le this 2
    · have : X < Z := by rw [hX, paramX]; nlinarith
      linarith
    · have : (1 + δ / 2) * Z ≤ 2 * X := by rw [hX, paramX]; nlinarith
      linarith
  have hdisj : Set.Pairwise (↑T) (Function.onFun Disjoint J) := by
    intro n _ m _ hnm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hnm with h | h
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith
    · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith
  have hint := integrableOn_sq_shortSum (coeffA δ g Z) (L := X) (U := 2 * X) hH1' hH2
  have hsub : (⋃ n ∈ T, J n) ⊆ Set.Ioc X (2 * X) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨(hJ n hn x hx).2.1, (hJ n hn x hx).2.2⟩
  have hfnn : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have key : (T.card : ℝ) * μ ^ 2 ≤ ∫ x in X..(2 * X), f x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    calc (T.card : ℝ) * μ ^ 2 = ∑ n ∈ T, μ ^ 2 * volume.real (J n) := by
          rw [Finset.sum_congr rfl fun n _ => by
            rw [show volume.real (J n) = 1 by
              simp only [J, Real.volume_real_Ico]; rw [max_eq_left (by linarith)]; ring, mul_one]]
          simp [mul_comm]
      _ ≤ ∑ n ∈ T, ∫ x in J n, f x := Finset.sum_le_sum fun n hn =>
          setIntegral_ge_of_const_le_real measurableSet_Ico measure_Ico_lt_top.ne
            (fun x hx => (hJ n hn x hx).1) (hint.mono_set fun x hx => hsub (by
              simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩))
      _ = ∫ x in ⋃ n ∈ T, J n, f x := (integral_biUnion_finset T (fun _ _ => measurableSet_Ico)
          hdisj fun n hn => hint.mono_set fun x hx => hsub (by
            simp only [Set.mem_iUnion]; exact ⟨n, hn, hx⟩)).symm
      _ ≤ ∫ x in Set.Ioc X (2 * X), f x :=
          setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => hfnn x)
            (Filter.Eventually.of_forall hsub)
  have hI0 : 0 ≤ ∫ x in X..(2 * X), f x :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => hfnn x
  unfold variance
  change (T.card : ℝ) ≤ 2 * X * (1 / X * ∫ x in X..(2 * X), f x) / μ ^ 2
  rw [show 2 * X * (1 / X * ∫ x in X..(2 * X), f x) = 2 * ∫ x in X..(2 * X), f x by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  linarith

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

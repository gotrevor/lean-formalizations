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

theorem theta_sub_le_primeCounting_sub {a b : ℕ} (hab : a ≤ b) :
    θ b - θ a ≤ ((Nat.primeCounting b : ℝ) - Nat.primeCounting a) * Real.log b := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hab, hp.2⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right, ← Nat.primesLE_card_eq_primeCounting,
    ← Nat.primesLE_card_eq_primeCounting]
  rw [← Nat.cast_sub (Finset.card_le_card hsub), ← Finset.card_sdiff_of_subset hsub]
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := (Finset.mem_sdiff.1 hp).1
  have := Nat.le_of_mem_primesLE hp'
  have := (Nat.prime_of_mem_primesLE hp').pos
  exact Real.log_le_log (by exact_mod_cast this) (by exact_mod_cast ‹p ≤ b›)


/-- The eventual size facts behind `shortIntervalPNT_of_mediumPNT`. -/
theorem shortIntervalPNT_eventually (c K : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, 1 ≤ y ∧ 12 * K ≤ Real.exp (c / 2 * Real.log y ^ ((1 : ℝ) / 10)) ∧
      Real.exp (c / 2 * Real.log y ^ ((1 : ℝ) / 10)) ≤ y ^ ((1 : ℝ) / 8) ∧
      Real.log (2 * y) ≤ 2 * y ^ ((1 : ℝ) / 8) ∧ 32 ≤ y ^ ((1 : ℝ) / 4) := by
  have hL : Tendsto (fun y : ℝ => Real.log y ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hL9 : Tendsto (fun y : ℝ => Real.log y ^ ((9 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hE : Tendsto (fun y : ℝ => Real.exp (c / 2 * Real.log y ^ ((1 : ℝ) / 10))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity))
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have h2y : Tendsto (fun y : ℝ => 2 * y) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop 1, hE.eventually_ge_atTop (12 * K),
    hL9.eventually_ge_atTop (4 * c), h2y.eventually hlog,
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_ge_atTop 32,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with y hy1 hK h9 hl h32 hlpos
  refine ⟨hy1, hK, ?_, ?_, h32⟩
  · have hy0 : 0 < y := by linarith
    rw [Real.rpow_def_of_pos hy0]
    apply Real.exp_le_exp.2
    have hsplit : Real.log y ^ ((1 : ℝ) / 10) * Real.log y ^ ((9 : ℝ) / 10) = Real.log y := by
      rw [← Real.rpow_add hlpos]; norm_num
    have : 0 ≤ Real.log y ^ ((1 : ℝ) / 10) := by positivity
    nlinarith
  · have hy0 : 0 < y := by linarith
    simp only [Real.norm_eq_abs, one_mul] at hl
    rw [abs_of_pos (Real.log_pos (by linarith)), abs_of_pos (by positivity),
      Real.mul_rpow (by norm_num) hy0.le] at hl
    have : (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have : 0 ≤ y ^ ((1 : ℝ) / 8) := by positivity
    nlinarith

/-- **Edge: `MediumPNT` ⇒ short-interval PNT.**  Difference `ψ(y + H) − ψ(y)`, discard prime powers
(`O(√y log y)`), partial summation; `c = c'/2`. -/
theorem shortIntervalPNT_of_mediumPNT (h : MediumPNTStatement) : ShortIntervalPNT := by
  obtain ⟨c, hc, hO⟩ := h
  obtain ⟨K, hK, hKw⟩ := hO.exists_pos
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 hKw.bound
  obtain ⟨y₂, hy₂⟩ := eventually_atTop.1 (shortIntervalPNT_eventually c K hc)
  refine ⟨c / 2, by positivity, max (max x₁ 0) y₂, fun y H hy hH hHy => ?_⟩
  obtain ⟨hy1, hKe, he8, hlog, h32⟩ := hy₂ y (le_of_max_le_right hy)
  have hyx : x₁ ≤ y := (le_max_left _ _).trans (le_of_max_le_left hy)
  have hy0 : 0 < y := by linarith
  set L := Real.log y ^ ((1 : ℝ) / 10) with hLdef
  set e := Real.exp (c / 2 * L) with hedef
  set f := Real.exp (-(c / 2) * L) with hfdef
  have hfe : f * e = 1 := by rw [hfdef, hedef, ← Real.exp_add]; simp
  have hf0 : 0 < f := Real.exp_pos _
  have he0 : 0 < e := Real.exp_pos _
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hyH : 0 < y + H := by linarith
  -- the MediumPNT error at y and y + H
  have hL' : L ≤ Real.log (y + H) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow (Real.log_nonneg hy1) (Real.log_le_log hy0 (by linarith)) (by norm_num)
  have hEE : Real.exp (-c * Real.log (y + H) ^ ((1 : ℝ) / 10)) ≤ f * f := by
    rw [hfdef, ← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have hEy : Real.exp (-c * L) = f * f := by rw [hfdef, ← Real.exp_add]; ring_nf
  have b1 := hx₁ (y + H) (by linarith)
  have b2 := hx₁ y hyx
  simp only [Pi.sub_apply, id, Real.norm_eq_abs] at b1 b2
  rw [abs_of_pos (by positivity : 0 < (y + H) * Real.exp (-c * Real.log (y + H) ^ ((1 : ℝ) / 10)))]
    at b1
  rw [abs_of_pos (by positivity : 0 < y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)))] at b2
  rw [← hLdef, hEy] at b2
  have hψ1 : (y + H) - K * (2 * y) * (f * f) ≤ ψ (y + H) := by
    have := (abs_le.1 b1).1
    have : K * ((y + H) * Real.exp (-c * Real.log (y + H) ^ ((1 : ℝ) / 10))) ≤
        K * (2 * y) * (f * f) := by
      rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hK.le
      exact mul_le_mul (by linarith) hEE (by positivity) (by positivity)
    linarith
  have hψ2 : ψ y ≤ y + K * y * (f * f) := by have := (abs_le.1 b2).2; linarith
  have hθ1 : ψ (y + H) - 2 * √(y + H) * Real.log (y + H) ≤ θ (y + H) := by
    have := Chebyshev.psi_sub_theta_le (show 1 ≤ y + H by linarith); linarith
  have hθ2 := Chebyshev.theta_le_psi y
  -- the prime-power and PNT errors are below H / 2
  have hsq : 2 * √(y + H) * Real.log (y + H) ≤ 2 * (2 * √y) * (2 * y ^ ((1 : ℝ) / 8)) := by
    have h1 : √(y + H) ≤ 2 * √y := by
      rw [show 2 * √y = √(4 * y) by rw [Real.sqrt_mul (by norm_num)]; norm_num]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.log (y + H) ≤ 2 * y ^ ((1 : ℝ) / 8) :=
      (Real.log_le_log hyH (by linarith)).trans hlog
    have : 0 ≤ Real.log (y + H) := Real.log_nonneg (by linarith)
    have : 0 ≤ √(y + H) := Real.sqrt_nonneg _
    nlinarith
  have hr4 : y ^ ((1 : ℝ) / 4) = y ^ ((1 : ℝ) / 8) * y ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hy0]; norm_num
  have hs : √y = y ^ ((1 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy0]; norm_num
  have hyy : y = √y * √y := (Real.mul_self_sqrt hy0.le).symm
  have hA : 2 * (2 * √y) * (2 * y ^ ((1 : ℝ) / 8)) ≤ y * f / 4 := by
    -- multiply through by `e`
    have key : 32 * √y * y ^ ((1 : ℝ) / 8) * e ≤ y := by
      have h8 : 0 ≤ y ^ ((1 : ℝ) / 8) := by positivity
      have hsy : 0 ≤ √y := Real.sqrt_nonneg _
      calc 32 * √y * y ^ ((1 : ℝ) / 8) * e ≤ 32 * √y * y ^ ((1 : ℝ) / 8) * y ^ ((1 : ℝ) / 8) := by
            apply mul_le_mul_of_nonneg_left he8; positivity
        _ = 32 * √y * y ^ ((1 : ℝ) / 4) := by rw [hr4]; ring
        _ ≤ y ^ ((1 : ℝ) / 4) * √y * y ^ ((1 : ℝ) / 4) := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h32 hsy); positivity
        _ = y := by
          rw [show y ^ ((1 : ℝ) / 4) * √y * y ^ ((1 : ℝ) / 4) =
            √y * (y ^ ((1 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) by ring, ← hs, ← hyy]
    have : y * f / 4 = y * f * e / (4 * e) := by field_simp
    rw [this, le_div_iff₀ (by positivity), mul_assoc y f e, hfe]
    nlinarith
  have hB : K * (2 * y) * (f * f) + K * y * (f * f) ≤ y * f / 4 := by
    have h12 : 12 * K * f ≤ 1 := by
      rw [← hfe]; exact (mul_le_mul_of_nonneg_right hKe hf0.le).trans_eq (mul_comm e f)
    have h0 : 0 ≤ y * f := by positivity
    have := mul_le_mul_of_nonneg_right h12 h0
    have h3 : K * (2 * y) * (f * f) + K * y * (f * f) = (12 * K * f) * (y * f) / 4 := by ring
    rw [h3]; linarith
  have hyf : y * f ≤ H := by simpa [hfdef, neg_mul, neg_div] using hH
  have hθd : H / 2 ≤ θ (y + H) - θ y := by linarith
  -- convert to π
  rw [Chebyshev.theta_eq_theta_coe_floor (y + H), Chebyshev.theta_eq_theta_coe_floor y] at hθd
  have hfl : ⌊y⌋₊ ≤ ⌊y + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hπ := theta_sub_le_primeCounting_sub hfl
  have hb1 : (1 : ℝ) ≤ ⌊y + H⌋₊ := by
    have : 1 ≤ ⌊y + H⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hblog : Real.log ⌊y + H⌋₊ ≤ Real.log (2 * y) :=
    Real.log_le_log (by linarith) ((Nat.floor_le hyH.le).trans (by linarith))
  have hπ0 : (0 : ℝ) ≤ (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊ := by
    have := Nat.monotone_primeCounting hfl
    rw [sub_nonneg]; exact_mod_cast this
  have hl2 : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left hblog hπ0
  linarith

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

/-- Counting pairs `(p, q)` from below: a double sum over `m = p q` dominates the pair count. -/
theorem sum_pairs_le_sum_primeFactors (I P : Finset ℕ) (Q : ℕ → Finset ℕ) (T : ℕ → ℕ → ℝ)
    (w : ℕ → ℝ) (hT : ∀ m p, 0 ≤ T m p) (hP : ∀ p ∈ P, 0 < p)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q p, p * q ∈ I ∧ p ∈ (p * q).primeFactors ∧ w p ≤ T (p * q) p) :
    ∑ p ∈ P, ((Q p).card : ℝ) * w p ≤ ∑ m ∈ I, ∑ p ∈ m.primeFactors, T m p := by
  classical
  set T' : ℕ → ℕ → ℝ := fun m p => if p ∈ m.primeFactors then T m p else 0
  have hT' : ∀ m p, 0 ≤ T' m p := fun m p => by simp only [T']; split_ifs <;> simp [hT]
  calc ∑ p ∈ P, ((Q p).card : ℝ) * w p ≤ ∑ p ∈ P, ∑ m ∈ I, T' m p := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hinj : Set.InjOn (fun q => p * q) ↑(Q p) := fun a _ b _ h =>
          Nat.eq_of_mul_eq_mul_left (hP p hp) h
        calc ((Q p).card : ℝ) * w p = ∑ q ∈ Q p, w p := by simp
          _ ≤ ∑ q ∈ Q p, T' (p * q) p := Finset.sum_le_sum fun q hq => by
              simp only [T', if_pos (hPQ p hp q hq).2.1]; exact (hPQ p hp q hq).2.2
          _ = ∑ m ∈ (Q p).image (fun q => p * q), T' m p := (Finset.sum_image (f := fun m => T' m p) hinj).symm
          _ ≤ ∑ m ∈ I, T' m p := Finset.sum_le_sum_of_subset_of_nonneg
              (fun m hm => by
                obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hm; exact (hPQ p hp q hq).1)
              (fun m _ _ => hT' m p)
    _ = ∑ m ∈ I, ∑ p ∈ P, T' m p := Finset.sum_comm
    _ ≤ ∑ m ∈ I, ∑ p ∈ m.primeFactors, T m p := Finset.sum_le_sum fun m _ => by
        simp only [T']
        rw [← Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.1 hp).2)
          (fun p _ _ => hT m p)

/-- The primes in `(⌊y⌋, ⌊y + H⌋]`. -/
noncomputable def primesIn (y H : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊y + H⌋₊ \ Nat.primesLE ⌊y⌋₊

theorem card_primesIn {y H : ℝ} (hH : 0 ≤ H) :
    ((primesIn y H).card : ℝ) = (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊ := by
  have hfl : ⌊y⌋₊ ≤ ⌊y + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊y + H⌋₊ := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hfl, hp.2⟩
  rw [primesIn, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

theorem mem_primesIn {y H : ℝ} {q : ℕ} (hy : 0 ≤ y) (h : q ∈ primesIn y H) :
    q.Prime ∧ y < q ∧ (q : ℝ) ≤ y + H := by
  rw [primesIn, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at h
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := h
  refine ⟨hq2, ?_, ?_⟩
  · have : ⌊y⌋₊ < q := by by_contra hh; exact hq3 ⟨by omega, hq2⟩
    exact (Nat.floor_lt hy).1 this
  · have hyH : 0 ≤ y + H := by
      by_contra hh; push Not at hh
      rw [Nat.floor_of_nonpos hh.le] at hq1; have := hq2.two_le; omega
    exact (Nat.le_floor_iff hyH).1 hq1

/-- `exp(−c (log y)^{1/10}) ≤ ε` for large `y`. -/
theorem eventually_exp_neg_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ ε := by
  have hL : Tendsto (fun y : ℝ => c * Real.log y ^ ((1 : ℝ) / 10)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop).const_mul_atTop hc
  filter_upwards [hL.eventually_ge_atTop (-Real.log ε)] with y hy
  calc Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ Real.exp (Real.log ε) :=
        Real.exp_le_exp.2 (by rw [neg_mul]; linarith)
    _ = ε := Real.exp_log hε

/-- The eventual size facts behind `longAverage_lower`. -/
theorem longAverage_eventually {c δ κ y₀ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hκ : 0 < κ) :
    ∀ᶠ Z : ℝ in atTop, 16 ≤ Z ∧ y₀ ≤ (1 - 7 * δ / 16) * √Z ∧
      Real.exp (-c * Real.log ((1 - 7 * δ / 16) * √Z) ^ ((1 : ℝ) / 10)) ≤ δ / 8 ∧
      2 ≤ Real.exp (c / 4 * Real.log Z ^ ((1 : ℝ) / 10)) ∧ 2 / δ ≤ paramT0 κ Z := by
  have ha : Tendsto (fun Z : ℝ => (1 - 7 * δ / 16) * √Z) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by linarith)
  have hL : Tendsto (fun Z : ℝ => Real.log Z ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hE : Tendsto (fun Z : ℝ => Real.exp (c / 4 * Real.log Z ^ ((1 : ℝ) / 10))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity))
  have hT : Tendsto (fun Z : ℝ => paramT0 κ Z) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hL.const_mul_atTop hκ)
  filter_upwards [eventually_ge_atTop 16, ha.eventually_ge_atTop y₀,
    ha.eventually (eventually_exp_neg_le hc (show 0 < δ / 8 by positivity)),
    hE.eventually_ge_atTop 2, hT.eventually_ge_atTop (2 / δ)] with Z h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

theorem half_rpow_tenth_le {Z y : ℝ} (hlZ : 0 ≤ Real.log Z)
    (hlogy : Real.log Z / 2 ≤ Real.log y) :
    Real.log Z ^ ((1 : ℝ) / 10) / 2 ≤ Real.log y ^ ((1 : ℝ) / 10) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 / 2 : ℝ) ^ ((1 : ℝ) / 10) := ⟨_, rfl⟩
  have hr1 : 1 / 2 ≤ r := hr ▸ Real.self_le_rpow_of_le_one (by norm_num) (by norm_num)
    (by norm_num)
  have hL0 : 0 ≤ Real.log Z ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hlZ _
  calc Real.log Z ^ ((1 : ℝ) / 10) / 2 ≤ r * Real.log Z ^ ((1 : ℝ) / 10) := by
        linarith only [mul_le_mul_of_nonneg_right hr1 hL0]
    _ = (Real.log Z / 2) ^ ((1 : ℝ) / 10) := by
        rw [hr, div_eq_mul_inv (Real.log Z) 2, Real.mul_rpow hlZ (by norm_num), mul_comm]
        congr 1; norm_num
    _ ≤ Real.log y ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow (div_nonneg hlZ (by norm_num)) hlogy (by norm_num)

set_option maxHeartbeats 1600000 in
/-- **The `q`-count for one `p`** in `longAverage_lower`. -/
theorem qcount_lower {c y₀ δ κ Z x : ℝ} {p : ℕ}
    (hS : ∀ y H : ℝ, y₀ ≤ y → y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ H → H ≤ y →
      H / (2 * Real.log (2 * y)) ≤ (Nat.primeCounting ⌊y + H⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊)
    (hc : 0 < c) (hκ : 0 < κ) (hκc : κ ≤ c / 12) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 16 ≤ Z)
    (hy₀ : y₀ ≤ (1 - 7 * δ / 16) * √Z) (hE2 : 2 ≤ Real.exp (c / 4 * Real.log Z ^ ((1 : ℝ) / 10)))
    (hT : 2 / δ ≤ paramT0 κ Z) (hx1 : Z ≤ x) (hx2 : x ≤ (1 + δ / 2) * Z)
    (hp1 : (1 - 7 * δ / 16) * √Z < p) (hp2 : (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z) :
    paramH2 δ κ Z / (2 * p * Real.log Z) ≤ ((primesIn (x / p) (paramH2 δ κ Z / p)).card : ℝ) ∧
      ∀ q ∈ primesIn (x / p) (paramH2 δ κ Z / p), q.Prime ∧ √Z ≤ q ∧
        (q : ℝ) ≤ (1 + 2 * δ) * √Z ∧ ⌈x⌉₊ ≤ p * q ∧ p * q ≤ ⌊x + paramH2 δ κ Z⌋₊ := by
  have hZ0 : 0 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hZ
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by nlinarith) hp1
  have hT3 : paramT0 κ Z ^ 3 = Real.exp (3 * κ * Real.log Z ^ ((1 : ℝ) / 10)) := by
    rw [paramT0, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hT1 : 1 ≤ paramT0 κ Z := by
    rw [paramT0]
    exact Real.one_le_exp (mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _))
  set L := Real.log Z ^ ((1 : ℝ) / 10) with hL
  have hL0 : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  set T0 := paramT0 κ Z with hT0
  set X := paramX δ Z with hX
  have hX0 : 0 < X := by rw [hX, paramX]; nlinarith
  set h2 := paramH2 δ κ Z with hh2
  have hh2' : h2 = X / T0 ^ 3 := rfl
  have hh20 : 0 < h2 := by rw [hh2']; positivity
  have hh2X : h2 ≤ X := by rw [hh2']; exact div_le_self hX0.le (one_le_pow₀ hT1)
  have hXZ : X ≤ Z := by rw [hX, paramX]; nlinarith
  have hh2δ : h2 ≤ δ / 2 * Z := by
    rw [hh2']
    have : X ≤ Z := by rw [hX, paramX]; nlinarith
    have h3 : 2 / δ ≤ T0 ^ 3 := hT.trans (le_self_pow₀ hT1 (by norm_num))
    rw [div_le_iff₀ (by positivity)]
    have : 2 / δ * δ = 2 := by field_simp
    nlinarith
  set y := x / p with hy
  set H := h2 / p with hH
  clear_value y H h2 X T0 L
  have hH0 : 0 < H := by rw [hH]; exact div_pos hh20 hp0
  have hyp : y * p = x := by rw [hy]; field_simp
  have hHp : H * p = h2 := by rw [hH]; field_simp
  have hlZp : 0 < Real.log Z := Real.log_pos (by linarith)
  -- `y ∈ [√Z, 2√Z]`
  have hy1 : √Z ≤ y := by
    rw [hy, le_div_iff₀ hp0]
    have : (p : ℝ) ≤ √Z := hp2.trans (by nlinarith)
    nlinarith
  have hy2 : y ≤ 2 * √Z := by
    rw [hy, div_le_iff₀ hp0]
    have : x ≤ 2 * √Z * ((1 - 7 * δ / 16) * √Z) := by
      have : 2 * √Z * ((1 - 7 * δ / 16) * √Z) = (2 - 7 * δ / 8) * Z := by
        linear_combination (2 - 7 * δ / 8) * hZsq
      rw [this]; nlinarith
    have : 2 * √Z * ((1 - 7 * δ / 16) * √Z) ≤ 2 * √Z * p :=
      mul_le_mul_of_nonneg_left hp1.le (by positivity)
    linarith
  have hy0 : 0 ≤ y := by linarith
  -- apply the short-interval PNT at `y`
  have hHy : H ≤ y := by
    rw [hH, hy]; exact div_le_div_of_nonneg_right (by linarith) hp0.le
  have hlow : y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ H := by
    have hlogy : Real.log Z / 2 ≤ Real.log y := by
      have : Real.log √Z = Real.log Z / 2 := by rw [Real.log_sqrt hZ0.le]
      rw [← this]; exact Real.log_le_log hsZ hy1
    have hlZ : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
    have hLy : L / 2 ≤ Real.log y ^ ((1 : ℝ) / 10) := hL ▸ half_rpow_tenth_le hlZ hlogy
    have hEy : Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ Real.exp (-(c / 2) * L) :=
      Real.exp_le_exp.2 (by linarith only [mul_le_mul_of_nonneg_left hLy hc.le])
    have hkey : 2 * Real.exp (-(c / 2) * L) ≤ Real.exp (-(3 * κ * L)) := by
      have : Real.exp (c / 4 * L) ≤ Real.exp ((c / 2 - 3 * κ) * L) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith only [hκc]) hL0)
      have h' := hE2.trans this
      have heq : Real.exp (-(c / 2) * L) * Real.exp ((c / 2 - 3 * κ) * L) =
          Real.exp (-(3 * κ * L)) := by rw [← Real.exp_add]; ring_nf
      have hm := mul_le_mul_of_nonneg_left h' (Real.exp_pos (-(c / 2) * L)).le
      linarith only [heq, hm]
    have hxX : x ≤ 2 * X := by
      rw [hX, paramX]; nlinarith only [hx2, hδ, hδ', hZ0]
    have hxE : x * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10)) ≤ h2 := by
      rw [hh2', hT3, div_eq_mul_inv X, ← Real.exp_neg]
      calc x * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10))
          ≤ (2 * X) * Real.exp (-(c / 2) * L) :=
            mul_le_mul hxX hEy (Real.exp_pos _).le (by positivity)
        _ = X * (2 * Real.exp (-(c / 2) * L)) := by ring
        _ ≤ X * Real.exp (-(3 * κ * L)) := mul_le_mul_of_nonneg_left hkey hX0.le
    refine le_of_mul_le_mul_right ?_ hp0
    rw [hHp, mul_right_comm, hyp]; exact hxE
  have hcount := hS y H (hy₀.trans ((by nlinarith : (1 - 7 * δ / 16) * √Z ≤ √Z).trans hy1)) hlow hHy
  rw [← card_primesIn hH0.le] at hcount
  refine ⟨?_, fun q hq => ?_⟩
  · refine le_trans ?_ hcount
    have hlog2y : Real.log (2 * y) ≤ Real.log Z :=
      Real.log_le_log (by linarith) (by nlinarith)
    have hlog2y0 : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
    rw [hH, div_div, div_le_div_iff₀ (mul_pos (mul_pos two_pos hp0) hlZp)
      (mul_pos hp0 (mul_pos two_pos hlog2y0))]
    have := mul_le_mul_of_nonneg_left hlog2y (show 0 ≤ h2 * (p * 2) by positivity)
    linarith
  · obtain ⟨hqp, hq1, hq2⟩ := mem_primesIn hy0 hq
    refine ⟨hqp, by linarith, ?_, ?_, ?_⟩
    · have : y + H ≤ (1 + 2 * δ) * √Z := by
        rw [hy, hH, ← add_div, div_le_iff₀ hp0]
        have : x + h2 ≤ (1 + δ) * Z := by nlinarith
        have : (1 + δ) * Z ≤ (1 + 2 * δ) * √Z * ((1 - 7 * δ / 16) * √Z) := by
          have : (1 + 2 * δ) * √Z * ((1 - 7 * δ / 16) * √Z) =
            (1 + 2 * δ) * (1 - 7 * δ / 16) * Z := by
            linear_combination (1 + 2 * δ) * (1 - 7 * δ / 16) * hZsq
          rw [this]; nlinarith
        have : 0 ≤ (1 + 2 * δ) * √Z := by positivity
        nlinarith
      linarith
    · apply Nat.ceil_le.2
      have : x < p * q := by
        have := mul_lt_mul_of_pos_right hq1 hp0
        rw [hyp] at this; linarith
      push_cast; linarith
    · apply Nat.le_floor
      have : (p : ℝ) * q ≤ x + h2 := by
        have := mul_le_mul_of_nonneg_left hq2 hp0.le
        have e : (p : ℝ) * (y + H) = x + h2 := by rw [← hyp, ← hHp]; ring
        rw [e] at this; exact this
      push_cast; linarith

set_option maxHeartbeats 1600000 in
/-- **W2′ (Lemma 3).**  For `κ` small against `MediumPNT`'s constant, the long average is
`≥ c₁ δ / log² Z` on `[Z, (1 + δ/2) Z]`. -/
theorem longAverage_lower (hPNT : MediumPNTStatement) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ g : ℝ → ℝ, Admissible δ g →
      ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ Z : ℝ in atTop, ∀ x, Z ≤ x → x ≤ (1 + δ / 2) * Z →
        c₁ * δ / Real.log Z ^ 2 ≤ shortSum (coeffA δ g Z) x (paramH2 δ κ Z) / paramH2 δ κ Z := by
  obtain ⟨c, hc, y₀, hS⟩ := shortIntervalPNT_of_mediumPNT hPNT
  refine ⟨c / 12, by positivity, fun κ hκ hκc g hg => ⟨1 / 128, by norm_num, ?_⟩⟩
  filter_upwards [longAverage_eventually (y₀ := y₀) hc hδ hδ' hκ] with Z ⟨hZ, hy₀, hEa, hE2, hT⟩
    x hx1 hx2
  have hZ0 : 0 < Z := by linarith
  have hsZ : 0 < √Z := Real.sqrt_pos.2 hZ0
  have hZsq : √Z * √Z = Z := Real.mul_self_sqrt hZ0.le
  have hs4 : 4 ≤ √Z := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hZ
  have hlZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hh20 : 0 < paramH2 δ κ Z := by
    unfold paramH2 paramX; exact div_pos (by nlinarith) (by unfold paramT0; positivity)
  set h2 := paramH2 δ κ Z with hh2
  set a := (1 - 7 * δ / 16) * √Z with ha
  set Ha := δ / 8 * √Z with hHa
  have ha0 : 0 < a := by rw [ha]; nlinarith
  have hHa0 : 0 < Ha := by positivity
  -- the `p`-count
  have hPc : Ha / (2 * Real.log (2 * a)) ≤ ((primesIn a Ha).card : ℝ) := by
    rw [card_primesIn hHa0.le]
    refine hS a Ha hy₀ ?_ (by rw [ha, hHa]; nlinarith)
    calc a * Real.exp (-c * Real.log a ^ ((1 : ℝ) / 10)) ≤ a * (δ / 8) :=
          mul_le_mul_of_nonneg_left hEa ha0.le
      _ ≤ Ha := by rw [ha, hHa]; nlinarith
  have hl2a : Real.log (2 * a) ≤ Real.log Z :=
    Real.log_le_log (by positivity) (by rw [ha]; nlinarith)
  have hl2a0 : 0 < Real.log (2 * a) := Real.log_pos (by rw [ha]; nlinarith)
  have hP' : δ * √Z / (16 * Real.log Z) ≤ ((primesIn a Ha).card : ℝ) := by
    refine le_trans ?_ hPc
    rw [div_le_div_iff₀ (by positivity) (by positivity), hHa]
    have := mul_le_mul_of_nonneg_left hl2a (show 0 ≤ δ * √Z by positivity)
    nlinarith
  -- the `log p` lower bound
  have hlogp : ∀ p ∈ primesIn a Ha, Real.log Z / 4 ≤ Real.log p := by
    intro p hp
    obtain ⟨-, hp1, -⟩ := mem_primesIn ha0.le hp
    have : √Z / 2 ≤ a := by rw [ha]; nlinarith
    have h1 : Real.log (√Z / 2) ≤ Real.log p := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hsZ.ne' (by norm_num), Real.log_sqrt hZ0.le] at h1
    have : 4 * Real.log 2 ≤ Real.log Z := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by positivity) (by norm_num; linarith)
    linarith
  -- the double count
  set T : ℕ → ℕ → ℝ := fun m p =>
    if (m / p).Prime ∧ √Z ≤ ((m / p : ℕ) : ℝ) ∧ ((m / p : ℕ) : ℝ) ≤ (1 + 2 * δ) * √Z
    then Real.log p * g (p / √Z) else 0 with hTdef
  have hT0 : ∀ m p, 0 ≤ T m p := fun m p => by
    simp only [hTdef]; split_ifs
    · exact mul_nonneg (Real.log_natCast_nonneg p) (hg.2.1 _).1
    · exact le_rfl
  have hpair := sum_pairs_le_sum_primeFactors (Finset.Icc ⌈x⌉₊ ⌊x + h2⌋₊) (primesIn a Ha)
    (fun p => primesIn (x / p) (h2 / p)) T (fun p => Real.log p) hT0
    (fun p hp => by exact_mod_cast (mem_primesIn ha0.le hp).1.pos) (fun p hp q hq => by
      obtain ⟨hpp, hp1, hp2⟩ := mem_primesIn ha0.le hp
      have hp2' : (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z := by
        have : a + Ha = (1 - 5 * δ / 16) * √Z := by rw [ha, hHa]; ring
        linarith
      obtain ⟨-, hQ⟩ := qcount_lower hS hc hκ hκc hδ hδ' hZ hy₀ hE2 hT hx1 hx2 hp1 hp2'
      obtain ⟨hqp, hq1, hq2, hq3, hq4⟩ := hQ q hq
      refine ⟨Finset.mem_Icc.2 ⟨hq3, hq4⟩, Nat.mem_primeFactors.2 ⟨hpp, dvd_mul_right p q,
        mul_ne_zero hpp.ne_zero hqp.ne_zero⟩, ?_⟩
      simp only [hTdef]
      rw [Nat.mul_div_cancel_left q hpp.pos, if_pos ⟨hqp, hq1, hq2⟩]
      have : g (p / √Z) = 1 := hg.2.2.2 _ (by rw [le_div_iff₀ hsZ]; linarith)
        (by rw [div_le_iff₀ hsZ]; linarith)
      rw [this, mul_one])
  have hsum : ∑ m ∈ Finset.Icc ⌈x⌉₊ ⌊x + h2⌋₊, ∑ p ∈ m.primeFactors, T m p =
      shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    unfold shortSum coeffA
    rw [← Finset.sum_div, div_mul_cancel₀ _ hlZ.ne']
  rw [hsum] at hpair
  -- each `p` contributes at least `h2 / (8 √Z)`
  have hper : ∀ p ∈ primesIn a Ha, h2 / (8 * √Z) ≤
      ((primesIn (x / p) (h2 / p)).card : ℝ) * Real.log p := by
    intro p hp
    obtain ⟨hpp, hp1, hp2⟩ := mem_primesIn ha0.le hp
    have hp2' : (p : ℝ) ≤ (1 - 5 * δ / 16) * √Z := by
      have : a + Ha = (1 - 5 * δ / 16) * √Z := by rw [ha, hHa]; ring
      linarith
    have hp0 : (0 : ℝ) < p := by linarith
    have hpZ : (p : ℝ) ≤ √Z := hp2'.trans (by nlinarith)
    have hQc := (qcount_lower hS hc hκ hκc hδ hδ' hZ hy₀ hE2 hT hx1 hx2 hp1 hp2').1
    have hlp := hlogp p hp
    have h1 : h2 / (2 * √Z * Real.log Z) ≤ h2 / (2 * p * Real.log Z) :=
      div_le_div_of_nonneg_left hh20.le (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith) hlZ.le)
    have h2' := le_trans h1 hQc
    calc h2 / (8 * √Z) = h2 / (2 * √Z * Real.log Z) * (Real.log Z / 4) := by
          field_simp; ring
      _ ≤ ((primesIn (x / p) (h2 / p)).card : ℝ) * Real.log p :=
          mul_le_mul h2' hlp (by positivity) (by positivity)
  have hsumlow : ((primesIn a Ha).card : ℝ) * (h2 / (8 * √Z)) ≤
      shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    refine le_trans ?_ hpair
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hper
  have hfin : δ * h2 / (128 * Real.log Z) ≤ shortSum (coeffA δ g Z) x h2 * Real.log Z := by
    refine le_trans ?_ hsumlow
    calc δ * h2 / (128 * Real.log Z) = δ * √Z / (16 * Real.log Z) * (h2 / (8 * √Z)) := by
          field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hP' (by positivity)
  rw [le_div_iff₀ hh20]
  have : 1 / 128 * δ / Real.log Z ^ 2 * h2 = δ * h2 / (128 * Real.log Z) / Real.log Z := by
    field_simp
  rw [this, div_le_iff₀ hlZ]
  exact hfin

/-- **W3 (Lemmas 4, 5, Proposition 6).**  `D ≤ C exp(−(κ/2)(log Z)^{1/10})` for large `Z`. -/
theorem variance_small (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT) (hVK : SmoothPrimeSumVK)
    (hPNT : MediumPNTStatement) {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hκ : 0 < κ)
    (hκ' : κ ≤ 1) {g : ℝ → ℝ} (hg : Admissible δ g) :
    ∃ C : ℝ, ∀ᶠ Z : ℝ in atTop,
      variance δ κ g Z ≤ C * Real.exp (-(κ / 2) * Real.log Z ^ ((1 : ℝ) / 10)) := by
  sorry

/-! ## Headline -/

/-- One geometric step of the window covering: `rZ + h(rZ) ≤ (1 + δ/2) Z` for `r = 1 + δ/4`. -/
theorem window_step {δ Z : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hZ : 2 ≤ Z) :
    (1 + δ / 4) * Z + paramH δ ((1 + δ / 4) * Z) ≤ (1 + δ / 2) * Z := by
  unfold paramH
  have : √((1 + δ / 4) * Z) ≤ Z := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  nlinarith

/-- **Covering by geometric windows.**  If every window `[Z + h, (1 + δ/2) Z]` carries at most `η Z`
elements of `E` for large `Z`, for every `η > 0`, then `E` has density zero. -/
theorem tendsto_density_zero_of_windows {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (E : Set ℕ)
    (hW : ∀ η : ℝ, 0 < η → ∀ᶠ Z : ℝ in atTop,
      ({n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}.ncard : ℝ) ≤ η * Z) :
    Tendsto (fun X : ℕ => ({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℝ) / X) atTop (nhds 0) := by
  classical
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (by positivity),
    fun η hη => ?_⟩
  set r : ℝ := 1 + δ / 4 with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  set η' : ℝ := η * (r - 1) / (4 * r) with hη'
  have hη'0 : 0 < η' := by rw [hη']; apply div_pos (mul_pos hη (by linarith)) (by linarith)
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.1 (hW η' hη'0)
  set Z₀ : ℝ := max Z₁ (max 16 (4 / δ)) with hZ₀
  have hZ₀16 : 16 ≤ Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hZ₀δ : 1 ≤ Z₀ * (δ / 4) := by
    have : 4 / δ ≤ Z₀ := (le_max_right _ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hδ] at this; linarith
  set Zs : ℕ → ℝ := fun j => Z₀ * r ^ j with hZs
  have hZs_ge : ∀ j, Z₀ ≤ Zs j := fun j => le_mul_of_one_le_right (by linarith)
    (one_le_pow₀ hr1.le)
  have hZs_succ : ∀ j, Zs (j + 1) = r * Zs j := fun j => by simp only [hZs, pow_succ]; ring
  have hZs_big : ∀ j : ℕ, (j : ℝ) ≤ Zs j := fun j => by
    have h1 : 1 + (j : ℝ) * (δ / 4) ≤ r ^ j := by
      rw [hr]; exact one_add_mul_le_pow (by linarith) j
    have : (j : ℝ) ≤ Z₀ * (1 + j * (δ / 4)) := by nlinarith
    exact this.trans (mul_le_mul_of_nonneg_left h1 (by linarith))
  have hH0 : ∀ Z : ℝ, 0 ≤ paramH δ Z := fun Z => by unfold paramH; positivity
  set W : ℝ → Set ℕ := fun Z => {n : ℕ | n ∈ E ∧ Z + paramH δ Z ≤ n ∧ (n : ℝ) ≤ (1 + δ / 2) * Z}
  have hWfin : ∀ Z, (W Z).Finite := fun Z =>
    (Set.finite_Iic ⌊(1 + δ / 2) * Z⌋₊).subset fun n hn => by
      simp only [Set.mem_Iic]; exact Nat.le_floor hn.2.2
  set N₀ : ℕ := ⌈Z₀ + paramH δ Z₀⌉₊ with hN₀
  set P : ℕ → ℕ → Prop := fun X j => Zs j + paramH δ (Zs j) ≤ X with hP
  -- the covering
  have hcover : ∀ X n : ℕ, n ∈ E → N₀ ≤ n → n ≤ X →
      ∃ j ≤ Nat.findGreatest (P X) X, n ∈ W (Zs j) := by
    intro X n hnE hn hnX
    set j := Nat.findGreatest (P n) n with hj
    have hP0 : P n 0 := by
      simp only [hP, hZs, pow_zero, mul_one]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hPj : P n j := Nat.findGreatest_spec (Nat.zero_le n) hP0
    have hjn : j ≤ n := Nat.findGreatest_le n
    refine ⟨j, Nat.le_findGreatest (hjn.trans hnX) ((show (P n j) from hPj).trans
      (by exact_mod_cast hnX)), hnE, hPj, ?_⟩
    by_contra hcon
    push Not at hcon
    have hstep := window_step hδ hδ' ((show (2 : ℝ) ≤ 16 by norm_num).trans
      (hZ₀16.trans (hZs_ge j)))
    rw [← hZs_succ] at hstep
    have hPj1 : P n (j + 1) := by simp only [hP]; linarith
    by_cases hj1 : j + 1 ≤ n
    · exact Nat.findGreatest_is_greatest (by omega) hj1 hPj1
    · have := hZs_big (j + 1)
      have : Zs (j + 1) ≤ n := le_trans (le_add_of_nonneg_right (hH0 _)) hPj1
      have : (n : ℝ) < (j + 1 : ℕ) := by exact_mod_cast (by omega : n < j + 1)
      linarith
  -- the count
  have hcount : ∀ X : ℕ, N₀ ≤ X →
      ({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℝ) ≤ N₀ + η * X / 4 := by
    intro X hX
    set J := Nat.findGreatest (P X) X
    have hsub : {n : ℕ | n ≤ X ∧ n ∈ E} ⊆ Set.Iio N₀ ∪ ⋃ j ∈ Finset.range (J + 1), W (Zs j) := by
      intro n ⟨hnX, hnE⟩
      by_cases hn : n < N₀
      · exact Or.inl hn
      · obtain ⟨j, hj, hW'⟩ := hcover X n hnE (by omega) hnX
        exact Or.inr (Set.mem_biUnion (Finset.mem_range.2 (by omega)) hW')
    have hfin : (Set.Iio N₀ ∪ ⋃ j ∈ Finset.range (J + 1), W (Zs j)).Finite :=
      (Set.finite_Iio N₀).union (Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => hWfin _)
    have h1 := Set.ncard_le_ncard hsub hfin
    have h2 := Set.ncard_union_le (Set.Iio N₀) (⋃ j ∈ Finset.range (J + 1), W (Zs j))
    have h3 := Finset.set_ncard_biUnion_le (Finset.range (J + 1)) (fun j => W (Zs j))
    have hN : (Set.Iio N₀).ncard = N₀ := by
      rw [show Set.Iio N₀ = ↑(Finset.range N₀) by ext; simp, Set.ncard_coe_finset,
        Finset.card_range]
    have hsumW : (∑ j ∈ Finset.range (J + 1), ((W (Zs j)).ncard : ℝ)) ≤
        ∑ j ∈ Finset.range (J + 1), η' * Zs j :=
      Finset.sum_le_sum fun j _ => hZ₁ (Zs j) ((le_max_left _ _).trans (hZs_ge j))
    have hgeom : ∑ j ∈ Finset.range (J + 1), Zs j ≤ r * Zs J / (r - 1) := by
      simp only [hZs]
      rw [← Finset.mul_sum, geom_sum_eq hr1.ne', ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : 0 ≤ Z₀ := by linarith
      rw [pow_succ]
      nlinarith [pow_pos (show 0 < r by linarith) J]
    have hJX : Zs J ≤ X := by
      have hP0 : P X 0 := by
        simp only [hP, hZs, pow_zero, mul_one]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hX)
      have := Nat.findGreatest_spec (Nat.zero_le X) hP0
      exact le_trans (le_add_of_nonneg_right (hH0 _)) this
    have hcast : ((⋃ j ∈ Finset.range (J + 1), W (Zs j)).ncard : ℝ) ≤
        ∑ j ∈ Finset.range (J + 1), ((W (Zs j)).ncard : ℝ) := by exact_mod_cast h3
    have : η' * (r * Zs J / (r - 1)) ≤ η * X / 4 := by
      rw [hη']
      have hr0 : r - 1 ≠ 0 := ne_of_gt (by linarith)
      have hr0' : r ≠ 0 := ne_of_gt (by linarith)
      have : η * (r - 1) / (4 * r) * (r * Zs J / (r - 1)) = η * Zs J / 4 := by
        field_simp
      rw [this]; nlinarith
    calc ({n : ℕ | n ≤ X ∧ n ∈ E}.ncard : ℝ)
        ≤ ((Set.Iio N₀ ∪ ⋃ j ∈ Finset.range (J + 1), W (Zs j)).ncard : ℝ) := by exact_mod_cast h1
      _ ≤ (Set.Iio N₀).ncard + ((⋃ j ∈ Finset.range (J + 1), W (Zs j)).ncard : ℝ) := by
          exact_mod_cast h2
      _ ≤ N₀ + η' * (r * Zs J / (r - 1)) := by
          rw [hN]
          have := hsumW.trans_eq (Finset.mul_sum _ _ _).symm
          have := mul_le_mul_of_nonneg_left hgeom hη'0.le
          linarith
      _ ≤ N₀ + η * X / 4 := by linarith
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop ⌈4 * N₀ / η⌉₊] with X hX hX'
  have hX0 : (0 : ℝ) < X := by
    have : 0 < X := lt_of_le_of_lt (Nat.zero_le _) hX'
    exact_mod_cast this
  have hXb : 4 * N₀ / η < X := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hX')
  rw [div_lt_iff₀ hX0]
  have := hcount X hX
  rw [div_lt_iff₀ hη] at hXb
  nlinarith

/-- `(log Z)^4 exp(−a (log Z)^{1/10}) → 0`. -/
theorem tendsto_log_pow_four_mul_exp {a : ℝ} (ha : 0 < a) :
    Tendsto (fun Z : ℝ => Real.log Z ^ 4 * Real.exp (-a * Real.log Z ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
  have hu : Tendsto (fun Z : ℝ => Real.log Z ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hv : Tendsto (fun v : ℝ => v ^ 40 * Real.exp (-a * v)) atTop (nhds 0) := by
    have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 40).comp (tendsto_id.const_mul_atTop ha)
    have h' := h.const_mul (1 / a ^ 40)
    rw [mul_zero] at h'
    refine h'.congr fun v => ?_
    simp only [Function.comp, id]
    field_simp
  refine (hv.comp hu).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Z hZ
  simp only [Function.comp]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_nonneg hZ)]
  norm_num

/-- **Theorem A (Lean form): `F(n) ≥ n + (1 − δ)√n` for almost all `n`**, i.e. the graph node
`AlmostAllF385`, from the four literature Props. -/
theorem almost_all_F385 (h1 : MR16Lemma14) (h2 : MontgomeryVaughanMVT) (h3 : VKZeroFreeLogDeriv)
    (h4 : MediumPNTStatement) : AlmostAllF385 := by
  intro δ hδ hδ'
  obtain ⟨g, hg⟩ := exists_admissible hδ hδ'
  obtain ⟨κ₀, hκ₀, hW2'⟩ := longAverage_lower h4 hδ hδ'
  have hκ : 0 < min κ₀ 1 := lt_min hκ₀ one_pos
  obtain ⟨c₁, hc₁, hlong⟩ := hW2' (min κ₀ 1) hκ (min_le_left _ _) g hg
  obtain ⟨C, hvar⟩ := variance_small h1 h2 (smoothPrimeSumVK_of_VKZ h3) h4 hδ hδ' hκ
    (min_le_right _ _) hg
  have hbad := card_badWindow_le hδ hδ' hκ (min_le_right _ _) hg
  set κ := min κ₀ 1
  refine tendsto_density_zero_of_windows hδ hδ' {n | (F n : ℝ) < n + (1 - δ) * √n} ?_
  intro η hη
  have hε := (tendsto_log_pow_four_mul_exp (show 0 < κ / 2 by positivity)).const_mul
    (2 * C / (c₁ * δ) ^ 2)
  rw [mul_zero] at hε
  filter_upwards [hbad, hlong, hvar, hε.eventually (eventually_lt_nhds hη),
    eventually_gt_atTop 1] with Z hb hl hv hε' hZ
  have hset : {n : ℕ | (F n : ℝ) < n + (1 - δ) * √n ∧ Z + paramH δ Z ≤ n ∧
      (n : ℝ) ≤ (1 + δ / 2) * Z} = badWindow δ Z := by
    ext n; simp only [badWindow, Set.mem_setOf_eq]; tauto
  rw [hset]
  have hlZ : 0 < Real.log Z := Real.log_pos hZ
  set μ := c₁ * δ / Real.log Z ^ 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hb' := hb μ hμ0 hl
  have hD0 : 0 ≤ variance δ κ g Z := by
    unfold variance
    have : 0 < paramX δ Z := by unfold paramX; nlinarith
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hX : paramX δ Z ≤ Z := by unfold paramX; nlinarith
  have hX0 : 0 ≤ paramX δ Z := by unfold paramX; nlinarith
  set e := Real.exp (-(κ / 2) * Real.log Z ^ ((1 : ℝ) / 10))
  have hCe : 0 ≤ C * e := hD0.trans hv
  calc ((badWindow δ Z).ncard : ℝ) ≤ 2 * paramX δ Z * variance δ κ g Z / μ ^ 2 := hb'
    _ ≤ 2 * Z * (C * e) / μ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := mul_le_mul hX hv hD0 (by linarith)
        linarith
    _ = Z * (2 * C / (c₁ * δ) ^ 2 * (Real.log Z ^ 4 * e)) := by
        rw [hμ]; field_simp
    _ ≤ η * Z := by rw [mul_comm η]; exact mul_le_mul_of_nonneg_left hε'.le (by linarith)

end LeanFormalizations.Erdos385

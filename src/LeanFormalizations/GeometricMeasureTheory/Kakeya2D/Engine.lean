/-
# Davies' theorem — proof engine (planar Kakeya dimension)

The headline `dimH S = 2` splits into the two inequalities:

* `dimH_le_two` — the **trivial** half: any subset of `ℝ²` has Hausdorff dimension `≤ 2`,
  by monotonicity into `univ`, whose dimension is `finrank ℝ (ℝ²) = 2`. **Proven.**
* `two_le_dimH` — **Davies 1971**, the genuine content: a planar Kakeya set has Hausdorff
  dimension `≥ 2`. Now fully machine-checked *modulo the single crisp axiom*
  `kakeya_dominant_scale_count` (the cross-scale orchestration / net-thinning). Strategy: Córdoba's
  dual / "bush" `L²` argument — see `PLAN.md`.

Only `two_le_dimH` uses `IsKakeya`; the upper bound holds for every set in the plane.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Defs
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Cover
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open Set MeasureTheory
open scoped NNReal ENNReal

namespace LeanFormalizations.Kakeya2D

/-- The trivial upper bound: every subset of the plane has Hausdorff dimension at most `2`.
(Holds for any set, Kakeya or not — `dimH` is monotone and `dimH (univ : Set ℝ²) = 2`.) -/
theorem dimH_le_two (S : Set (EuclideanSpace ℝ (Fin 2))) : dimH S ≤ 2 := by
  have huniv : dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) = 2 := by
    simp [Real.dimH_univ_eq_finrank]
  calc dimH S ≤ dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) := dimH_mono (subset_univ S)
    _ = 2 := huniv

/-! ### Exponential-beats-polynomial constant (the content-bound constant)

The cross-scale assembly produces, at the cover's dominant scale `j*`, a content contribution
`≳ b^{j*}/(1+j*)^m` with `b = 2^{2-d} > 1` (since `d < 2`) and a fixed polynomial denominator from
the Córdoba/pigeonhole losses. Since `j*` is the *output* of the pigeonhole (not under our control),
the Hausdorff-content constant `c` must be a uniform lower bound valid for *every* `j*`. As `b^j/(1+j)^m
→ ∞`, the infimum over `j` is attained and positive: this is exactly the `c > 0` the content bound
needs. The lemma is proven root-free (Bernoulli + a `√b` induction), so it carries no extra axioms. -/

/-- Bernoulli base case: for `b > 1`, `min(1,b-1)·(1+j) ≤ b^j` for all `j`. -/
theorem exists_const_mul_succ_le {b : ℝ} (hb : 1 < b) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, c * (1 + (j : ℝ)) ≤ b ^ j := by
  refine ⟨min 1 (b - 1), lt_min one_pos (by linarith), fun j => ?_⟩
  have hbern : 1 + (j : ℝ) * (b - 1) ≤ b ^ j := by
    have h := one_add_mul_le_pow (a := b - 1) (by linarith) j
    have he : (1 : ℝ) + (b - 1) = b := by ring
    rwa [he] at h
  have hm1 : min 1 (b - 1) ≤ 1 := min_le_left _ _
  have hmb : min 1 (b - 1) ≤ b - 1 := min_le_right _ _
  have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
  calc min 1 (b - 1) * (1 + (j : ℝ)) = min 1 (b - 1) + min 1 (b - 1) * j := by ring
    _ ≤ 1 + (b - 1) * j := add_le_add hm1 (mul_le_mul_of_nonneg_right hmb hj)
    _ = 1 + (j : ℝ) * (b - 1) := by ring
    _ ≤ b ^ j := hbern

/-- **Exponential beats any fixed polynomial (multiplicative form).** For `b > 1` and any `m`, there
is `c > 0` with `c·(1+j)^m ≤ b^j` for all `j`. Proven by induction on `m` using a `√b` split:
`c₁(1+j)^m ≤ (√b)^j` and `c₂(1+j) ≤ (√b)^j` multiply to `c₁c₂(1+j)^{m+1} ≤ b^j`. -/
theorem exists_const_mul_pow_le : ∀ (m : ℕ) {b : ℝ}, 1 < b →
    ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, c * (1 + (j : ℝ)) ^ m ≤ b ^ j := by
  intro m
  induction m with
  | zero => intro b hb; exact ⟨1, one_pos, fun j => by simpa using one_le_pow₀ hb.le⟩
  | succ m ih =>
    intro b hb
    have hb0 : (0 : ℝ) ≤ b := by linarith
    set s := Real.sqrt b with hs
    have hs1 : 1 < s := by
      rw [hs]; exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using hb)
    have hss : s * s = b := Real.mul_self_sqrt hb0
    obtain ⟨c1, hc1, h1⟩ := ih hs1
    obtain ⟨c2, hc2, h2⟩ := exists_const_mul_succ_le hs1
    refine ⟨c1 * c2, by positivity, fun j => ?_⟩
    have hsj : (0 : ℝ) ≤ s ^ j := by positivity
    calc c1 * c2 * (1 + (j : ℝ)) ^ (m + 1)
        = (c1 * (1 + (j : ℝ)) ^ m) * (c2 * (1 + (j : ℝ))) := by ring
      _ ≤ s ^ j * s ^ j := by
          refine mul_le_mul (h1 j) (h2 j) ?_ hsj
          have : (0 : ℝ) ≤ c2 * (1 + (j : ℝ)) := by positivity
          exact this
      _ = b ^ j := by rw [← mul_pow, hss]

/-- **The content-bound constant.** For `b > 1` and any `m`, there is `c > 0` with `c ≤ b^j/(1+j)^m`
for *all* `j` — the uniform positive lower bound on the dominant-scale content contribution. -/
theorem exists_pos_le_pow_div {b : ℝ} (hb : 1 < b) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, c ≤ b ^ j / (1 + (j : ℝ)) ^ m := by
  obtain ⟨c, hc, h⟩ := exists_const_mul_pow_le m hb
  refine ⟨c, hc, fun j => ?_⟩
  have hden : (0 : ℝ) < (1 + (j : ℝ)) ^ m := by positivity
  rw [le_div_iff₀ hden]
  exact h j

/-- **Exponential-beats-polynomial ratio (the localized-Córdoba content constant).** For `0 < d < 2`
there is a fixed `cR > 0` with, for every dyadic scale `j`,

  `cR · (4·(1/4)^j) · (12π·(1 + j·log 2))  ≤  (1/((j+1)(j+2)))² · ((1/2)^(j+1))^d`.

This is exactly the inequality the cross-scale assembly needs after `cover_content_per_scale`: the
left coefficient is the Córdoba per-piece coefficient `(ρ+δ)²·6πδ·2N(1+log N)` at `δ = ρ = (1/2)^j`,
`N = 2^j`; the right is the squared covered-length numerator `(1/((j+1)(j+2)))²` times `η^d` with
`η = (1/2)^(j+1)`. Setting `q = (1/2)^d` and `b = 4q = 2^{2-d} > 1`, the right side is `q^{j+1}/poly`
and the ratio is `≳ b^j/poly(j)`, whose infimum over `j` is positive since `b > 1`
(`exists_const_mul_pow_le`). Pure real analysis — no measure theory. -/
theorem content_ratio_lower {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ j : ℕ,
      cR * (4 * (1 / 4 : ℝ) ^ j) * (12 * Real.pi * (1 + (j : ℝ) * Real.log 2))
        ≤ (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) ^ 2 * ((1 / 2 : ℝ) ^ (j + 1)) ^ d := by
  set q : ℝ := (1 / 2 : ℝ) ^ d with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos (by norm_num) d
  have hb1 : (1 : ℝ) < 4 * q := by
    have hlt : (1 / 2 : ℝ) ^ (2 : ℝ) < (1 / 2 : ℝ) ^ d :=
      Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) hd2
    have h2 : (1 / 2 : ℝ) ^ (2 : ℝ) = 1 / 4 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h2] at hlt; rw [hq]; linarith
  obtain ⟨c0, hc0, hc0le⟩ := exists_const_mul_pow_le 5 hb1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hπ : 0 < Real.pi := Real.pi_pos
  refine ⟨c0 * q / (192 * Real.pi * (1 + Real.log 2)), by positivity, ?_⟩
  intro j
  set P : ℝ := ((j : ℝ) + 1) * ((j : ℝ) + 2) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  -- the squared-power identity `((1/2)^(j+1))^d = q^(j+1)`
  have hE : ((1 / 2 : ℝ) ^ (j + 1)) ^ d = q ^ (j + 1) := by
    rw [hq, ← Real.rpow_natCast (1 / 2 : ℝ) (j + 1),
      ← Real.rpow_natCast ((1 / 2 : ℝ) ^ d) (j + 1),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm]
  -- `q^(j+1) = q · (1/4)^j · (4q)^j`
  have hqpow : q ^ j = (1 / 4 : ℝ) ^ j * (4 * q) ^ j := by
    rw [← mul_pow, show (1 / 4 : ℝ) * (4 * q) = q from by ring]
  have hqj1 : q ^ (j + 1) = q * ((1 / 4 : ℝ) ^ j * (4 * q) ^ j) := by
    rw [pow_succ, hqpow]; ring
  -- degree-5 polynomial bound
  have hpoly : (1 + (j : ℝ) * Real.log 2) * P ^ 2 ≤ 4 * (1 + Real.log 2) * ((j : ℝ) + 1) ^ 5 := by
    have hx : (0 : ℝ) ≤ (j : ℝ) := j.cast_nonneg
    have h1 : (1 + (j : ℝ) * Real.log 2) ≤ (1 + Real.log 2) * (1 + (j : ℝ)) := by
      have he : (1 + Real.log 2) * (1 + (j : ℝ))
          = 1 + (j : ℝ) + Real.log 2 + (j : ℝ) * Real.log 2 := by ring
      rw [he]; linarith [hx, hlog2.le]
    have hstep : ((j : ℝ) + 2) ^ 2 ≤ 4 * ((j : ℝ) + 1) ^ 2 := by nlinarith [hx, mul_nonneg hx hx]
    have h2 : P ^ 2 ≤ 4 * ((j : ℝ) + 1) ^ 4 := by
      rw [hP]
      calc (((j : ℝ) + 1) * ((j : ℝ) + 2)) ^ 2 = ((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 2) ^ 2 := by ring
        _ ≤ ((j : ℝ) + 1) ^ 2 * (4 * ((j : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = 4 * ((j : ℝ) + 1) ^ 4 := by ring
    calc (1 + (j : ℝ) * Real.log 2) * P ^ 2
        ≤ ((1 + Real.log 2) * (1 + (j : ℝ))) * (4 * ((j : ℝ) + 1) ^ 4) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 * (1 + Real.log 2) * ((j : ℝ) + 1) ^ 5 := by ring
  -- core: `c0·G·P² ≤ 4(1+log2)·(4q)^j`
  have hc5 : c0 * ((j : ℝ) + 1) ^ 5 ≤ (4 * q) ^ j := by
    have h := hc0le j
    rwa [show (1 + (j : ℝ)) = ((j : ℝ) + 1) from by ring] at h
  have hcore : c0 * ((1 + (j : ℝ) * Real.log 2) * P ^ 2) ≤ 4 * (1 + Real.log 2) * (4 * q) ^ j := by
    calc c0 * ((1 + (j : ℝ) * Real.log 2) * P ^ 2)
        ≤ c0 * (4 * (1 + Real.log 2) * ((j : ℝ) + 1) ^ 5) := mul_le_mul_of_nonneg_left hpoly hc0.le
      _ = 4 * (1 + Real.log 2) * (c0 * ((j : ℝ) + 1) ^ 5) := by ring
      _ ≤ 4 * (1 + Real.log 2) * (4 * q) ^ j := mul_le_mul_of_nonneg_left hc5 (by positivity)
  -- assemble the main inequality
  set cR : ℝ := c0 * q / (192 * Real.pi * (1 + Real.log 2)) with hcR
  have hmain : cR * (48 * Real.pi) * (1 + (j : ℝ) * Real.log 2) * P ^ 2 ≤ q * (4 * q) ^ j := by
    have hK : (0 : ℝ) < 192 * Real.pi * (1 + Real.log 2) := by positivity
    rw [hcR]
    rw [show c0 * q / (192 * Real.pi * (1 + Real.log 2)) * (48 * Real.pi)
          * (1 + (j : ℝ) * Real.log 2) * P ^ 2
        = (c0 * q * (48 * Real.pi) * (1 + (j : ℝ) * Real.log 2) * P ^ 2)
          / (192 * Real.pi * (1 + Real.log 2)) from by ring, div_le_iff₀ hK]
    calc c0 * q * (48 * Real.pi) * (1 + (j : ℝ) * Real.log 2) * P ^ 2
        = (q * (48 * Real.pi)) * (c0 * ((1 + (j : ℝ) * Real.log 2) * P ^ 2)) := by ring
      _ ≤ (q * (48 * Real.pi)) * (4 * (1 + Real.log 2) * (4 * q) ^ j) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = q * (4 * q) ^ j * (192 * Real.pi * (1 + Real.log 2)) := by ring
  -- convert main inequality into the goal
  have hRHS : (1 / P) ^ 2 * q ^ (j + 1) = q ^ (j + 1) / P ^ 2 := by
    rw [div_pow, one_pow]; ring
  rw [hE, hRHS, le_div_iff₀ (by positivity : (0 : ℝ) < P ^ 2), hqj1]
  calc cR * (4 * (1 / 4 : ℝ) ^ j) * (12 * Real.pi * (1 + (j : ℝ) * Real.log 2)) * P ^ 2
      = (cR * (48 * Real.pi) * (1 + (j : ℝ) * Real.log 2) * P ^ 2) * (1 / 4 : ℝ) ^ j := by ring
    _ ≤ (q * (4 * q) ^ j) * (1 / 4 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = q * ((1 / 4 : ℝ) ^ j * (4 * q) ^ j) := by ring

/-- **The narrowed deep crux (cross-scale orchestration / dominant-scale extraction).** This is the
one genuinely reference-gated combinatorial obligation of the planar Kakeya lower bound, isolated as a
crisp `axiom`. Given a planar Kakeya set `S`, a cover `{tₙ}` (`ediam ≤ 1`), and `0 < d < 2`, it asserts
the existence of a **dominant dyadic scale** `j` together with:

* base points `a k` and covered sets `A k ⊆ [0,1]` (one per net direction `θ_k = k·2⁻ʲ`);
* a finite set `s` of cover pieces, each of diameter `∈ (2⁻⁽ʲ⁺¹⁾, 2⁻ʲ]` (genuinely *at* scale `j`);
* the geometric containment `φ_k(A k) ⊆ ⋃_{n∈s} tₙ` (the covered segments lie in the scale-`j` pieces);
* the **covered-length numerator bound** `∑ₖ 2δ·vol(A k) ≥ 1/((j+1)(j+2))` (`δ = 2⁻ʲ`) — a
  `1/poly(j)` fraction of the `N = 2ʲ` net directions is covered at the dominant scale.

This bundles the two dyadic pigeonholes (`Cover.exists_dominant_scale`, `exists_global_dominant_scale`)
with the net-thinning + covered-length-retention step that breaks the net-scale circularity — the lone
piece still open (see `ON-LINE-REQUEST.md`). **Everything downstream of it is now machine-checked**:
`cover_content_per_scale` (Córdoba count ⟹ content), `content_ratio_lower` (the exponential-beats-poly
constant), and the assembly below. Discharging this axiom into a proof is the remaining work. -/
axiom kakeya_dominant_scale_count
    {S : Set Plane} (h : IsKakeya S) {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2)
    (t : ℕ → Set Plane) (hcov : S ⊆ ⋃ n, t n) (hr : ∀ n, Metric.ediam (t n) ≤ 1) :
    ∃ j : ℕ, ∃ (a : ℕ → Plane) (A : ℕ → Set ℝ),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, A k ⊆ Set.Icc (0 : ℝ) 1) ∧
      ∃ s : Finset ℕ,
        (∀ n ∈ s, Metric.ediam (t n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j)) ∧
        (∀ n ∈ s, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ≤ Metric.ediam (t n)) ∧
        (∀ k, (fun u => a k + u • dir ((k : ℝ) * (1 / 2 : ℝ) ^ j)) '' (A k) ⊆ ⋃ n ∈ s, t n) ∧
        ENNReal.ofReal (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
          ≤ ∑ k ∈ Finset.range (2 ^ j), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * volume (A k)

theorem kakeya_hausdorffContentBound
    {S : Set (EuclideanSpace ℝ (Fin 2))} (h : IsKakeya S) {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2) :
    HausdorffContentBound S d := by
  obtain ⟨cR, hcRpos, hcR⟩ := content_ratio_lower hd0 hd2
  set D : ℝ≥0∞ := volume (Metric.closedBall (0 : Plane) 1) with hD
  have hDpos : 0 < D := volume_closedBall_one_pos
  have hDtop : D ≠ ⊤ := volume_closedBall_one_ne_top
  refine ⟨1, zero_lt_one, D⁻¹ * ENNReal.ofReal cR, ?_, ?_⟩
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hDtop) (ENNReal.ofReal_pos.mpr hcRpos).ne'
  · intro t hcov hdiam
    obtain ⟨j, a, A, hAmeas, hA01, s, hediam_hi, hediam_lo, hscov, hnum⟩ :=
      kakeya_dominant_scale_count h hd0 hd2 t hcov hdiam
    -- the single-scale content brick at the dominant scale `δ = ρ = (1/2)^j`, `N = 2^j`
    have hps := cover_content_per_scale (δ := (1 / 2 : ℝ) ^ j) (ρ := (1 / 2 : ℝ) ^ j) (N := 2 ^ j)
      (η := ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)))
      (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
      (by rw [Nat.cast_pow, ← mul_pow]; norm_num) a A hAmeas hA01 (0 : ℝ) s t hediam_hi
      (by simpa only [zero_add] using hscov) hd0.le hediam_lo
    rw [← hD] at hps
    set C0 : ℝ≥0∞ := ENNReal.ofReal (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2) * D
        * ENNReal.ofReal (6 * Real.pi * (1 / 2 : ℝ) ^ j
          * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ)))) with hC0def
    -- real simplifications connecting the Córdoba coefficient to `content_ratio_lower`'s form
    have hsq : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 from by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    have hW1 : ((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2 = 4 * (1 / 4 : ℝ) ^ j := by
      rw [show (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j = 2 * (1 / 2 : ℝ) ^ j from by ring, mul_pow, hsq]
      norm_num
    have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by rw [Nat.cast_pow, Nat.cast_ofNat]
    have hW2 : 6 * Real.pi * (1 / 2 : ℝ) ^ j
        * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ)))
        = 12 * Real.pi * (1 + (j : ℝ) * Real.log 2) := by
      rw [hcast, Real.log_pow,
        show 6 * Real.pi * (1 / 2 : ℝ) ^ j * (2 * (2 : ℝ) ^ j * (1 + (j : ℝ) * Real.log 2))
          = 12 * Real.pi * ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) * (1 + (j : ℝ) * Real.log 2) from by ring,
        show (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 from by rw [← mul_pow]; norm_num]
      ring
    have hKEYreal : cR * (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2)
          * (6 * Real.pi * (1 / 2 : ℝ) ^ j
            * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))
        ≤ (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) ^ 2 * ((1 / 2 : ℝ) ^ (j + 1)) ^ d := by
      rw [hW1, hW2]; exact hcR j
    -- `C0 ≠ 0`, `C0 ≠ ⊤` for the cancellation
    have hW2pos : 0 < 6 * Real.pi * (1 / 2 : ℝ) ^ j
        * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))) := by
      rw [hW2]
      have hp : (0 : ℝ) < 1 + (j : ℝ) * Real.log 2 := by
        have h := mul_nonneg (Nat.cast_nonneg j) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
        linarith
      exact mul_pos (by positivity) hp
    have hC0pos : C0 ≠ 0 := by
      rw [hC0def]
      exact mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hDpos.ne')
        (ENNReal.ofReal_pos.mpr hW2pos).ne'
    have hC0top : C0 ≠ ⊤ := by
      rw [hC0def]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDtop) ENNReal.ofReal_ne_top
    -- `(D⁻¹·ofReal cR)·C0 = ofReal(cR·W1·W2)` (the `D⁻¹·D` cancels)
    have hLHS : (D⁻¹ * ENNReal.ofReal cR) * C0
        = ENNReal.ofReal (cR * ((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2
          * (6 * Real.pi * (1 / 2 : ℝ) ^ j
            * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))) := by
      rw [hC0def,
        show (D⁻¹ * ENNReal.ofReal cR) * (ENNReal.ofReal (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2) * D
            * ENNReal.ofReal (6 * Real.pi * (1 / 2 : ℝ) ^ j
              * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ)))))
          = (D⁻¹ * D) * (ENNReal.ofReal cR
              * ENNReal.ofReal (((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2)
              * ENNReal.ofReal (6 * Real.pi * (1 / 2 : ℝ) ^ j
                * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))) from by ring,
        ENNReal.inv_mul_cancel hDpos.ne' hDtop, one_mul,
        ← ENNReal.ofReal_mul hcRpos.le, ← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.mul_le_mul_iff_left hC0pos hC0top]
    calc (D⁻¹ * ENNReal.ofReal cR) * C0
        = ENNReal.ofReal (cR * ((1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j) ^ 2
            * (6 * Real.pi * (1 / 2 : ℝ) ^ j
              * (2 * ((2 ^ j : ℕ) : ℝ) * (1 + Real.log ((2 ^ j : ℕ) : ℝ))))) := hLHS
      _ ≤ ENNReal.ofReal ((1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) ^ 2 * ((1 / 2 : ℝ) ^ (j + 1)) ^ d) :=
          ENNReal.ofReal_le_ofReal hKEYreal
      _ = (ENNReal.ofReal (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) ^ 2
          * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1))) ^ d := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1))]
      _ ≤ (∑ k ∈ Finset.range (2 ^ j), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * volume (A k)) ^ 2
            * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1))) ^ d := by gcongr
      _ ≤ (∑ n ∈ s, Metric.ediam (t n) ^ d) * C0 := hps
      _ ≤ (∑' n, Metric.ediam (t n) ^ d) * C0 := mul_le_mul_right' (ENNReal.sum_le_tsum s) C0

/-- **The concrete crux (Davies 1971, measure form).** For a Kakeya set `S ⊆ ℝ²`, every
`d`-dimensional Hausdorff measure with `d < 2` is *positive*: `μH[d] S ≠ 0`.

This is the genuine analytic content; `two_le_dimH` is a free `ℝ≥0∞`-density wrapper around it.
The route to discharge it is the Córdoba `L²`/bush argument (`PLAN.md`, ladder K2–K5):
δ-tube overlap bound ⟹ Minkowski-content lower bound `vol(Sδ) ≳ 1/log(1/δ)` ⟹ a Hausdorff content
lower bound witnessing `μH[d] S > 0` for every `d < 2`.

**Status (this run).** K2–K4 are **proven, axiom-clean**: the content bound `vol(Sδ) ≳ 1/log(1/δ)`
is `volume_thickening_log_ge`. K5's measure-free reduction (`Cover.lean`,
`hausdorffMeasure_ne_zero_of_contentBound`) turns the crux into the **Hausdorff content bound**
`kakeya_hausdorffContentBound`, now machine-checked modulo the lone axiom
`kakeya_dominant_scale_count`. The `d = 0` endpoint is free from monotonicity of `μH` in `d`
against the `d = 1` content bound. -/
theorem hausdorffMeasure_pos_of_isKakeya
    (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    ∀ d : ℝ≥0, (d : ℝ≥0∞) < 2 → μH[(d : ℝ)] S ≠ 0 := by
  -- For every real exponent `0 < e < 2`, content bound ⟹ positive Hausdorff measure.
  have key : ∀ e : ℝ, 0 < e → e < 2 → μH[e] S ≠ 0 := fun e he0 he2 =>
    hausdorffMeasure_ne_zero_of_contentBound he0 (kakeya_hausdorffContentBound h he0 he2)
  intro d hd
  rcases eq_or_lt_of_le (zero_le d) with hd0 | hd0
  · -- `d = 0`: `μH[0] S ≥ μH[1] S ≠ 0` by monotonicity of `μH` in the exponent.
    have hd0R : (d : ℝ) = 0 := by exact_mod_cast hd0.symm
    have hmono : μH[(1 : ℝ)] S ≤ μH[(d : ℝ)] S := by
      rw [hd0R]; exact Measure.hausdorffMeasure_mono (by norm_num) S
    exact fun hz => key 1 one_pos (by norm_num) (le_antisymm (hz ▸ hmono) (zero_le _))
  · -- `0 < d < 2`.
    have hd2R : (d : ℝ) < 2 := by exact_mod_cast hd
    exact key d (by exact_mod_cast hd0) hd2R

/-- **Davies 1971.** A Kakeya set in `ℝ²` has Hausdorff dimension at least `2`.

This is the genuine content of the planar Kakeya set conjecture (the upper bound is free).
Reduced (K1, axiom-clean) to the measure-positivity crux `hausdorffMeasure_pos_of_isKakeya`:
Frostman's lemma `le_dimH_of_hausdorffMeasure_ne_zero` lifts each `μH[d] S ≠ 0` (with `d < 2`)
to `↑d ≤ dimH S`, and `ENNReal.le_of_forall_nnreal_lt` pushes the supremum over `d < 2` up to `2`. -/
theorem two_le_dimH (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    2 ≤ dimH S := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  exact le_dimH_of_hausdorffMeasure_ne_zero (hausdorffMeasure_pos_of_isKakeya S h r hr)

end LeanFormalizations.Kakeya2D

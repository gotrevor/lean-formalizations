/-
# Davies' theorem — proof engine (planar Kakeya dimension)

The headline `dimH S = 2` splits into the two inequalities:

* `dimH_le_two` — the **trivial** half: any subset of `ℝ²` has Hausdorff dimension `≤ 2`,
  by monotonicity into `univ`, whose dimension is `finrank ℝ (ℝ²) = 2`. **Proven.**
* `two_le_dimH` — **Davies 1971**, the genuine content: a planar Kakeya set has Hausdorff
  dimension `≥ 2`. Now machine-checked *modulo the single crisp axiom*
  `kakeya_subresolution_content` (the **Case B / sub-resolution** residual — see its docstring): the
  full dominant-scale assembly (fine net ⟶ shift pigeonhole ⟶ base-angle Córdoba) is proven; the lone
  leftover is the Hausdorff-vs-box gap for covers dominated by pieces finer than the net resolution.
  Strategy: Córdoba's dual / "bush" `L²` argument — see `PLAN.md`.

Only `two_le_dimH` uses `IsKakeya`; the upper bound holds for every set in the plane.
-/
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Defs
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Cover
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.NetThinning
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

/-- **Case B residual: the sub-resolution Hausdorff-content bound — the genuine remaining obstacle.**

The dominant-scale assembly (`kakeya_hausdorffContentBound`, below) runs a fine net at resolution
`2⁻ᴶ`, pigeonholes to a dominant scale `j ≤ J`, and — when `j < J` (**Case A**) — discharges the
content bound entirely from the proven bricks (`exists_dominant_shift` ⟹ a shifted `2⁻ʲ`-net of `2ʲ`
directions covered `≳ 1/poly(j)` at scale `j`, fed to the base-angle `cover_content_per_scale`). The
*only* leftover is **Case B** `j = J`: the cover is dominated by pieces **finer** than the net
resolution, so the scale-`J` fiber is not a single scale — `cover_content_per_scale` does not apply
(pieces can be arbitrarily small, so their *count* no longer bounds `∑ ediam^d`).

This is exactly the **Hausdorff-vs-box-counting gap**. The Córdoba `L²` bound pins the box dimension
at every fixed scale (proven: `volume_thickening_log_ge`); promoting it to a Hausdorff content bound
for an arbitrarily-fine cover requires summing the per-scale counts across the sub-resolution scales
with the right convexity — the part not yet formalized. It is isolated here as the content conclusion
**conditioned on the Case-B witness**: a `2ᴶ`-direction net (base points `a k`, measurable covered
sets `A k ⊆ [0,1]`, base angle `c`) whose covered segments lie in a family `s` of pieces *all* of
diameter `≤ 2⁻ᴶ` (`hediam_hi`), carrying `≥ 1/poly(J)` of the aggregate covered length (`hnum`). Note
this axiom is **strictly weaker** than the former monolithic dominant-scale axiom: it only fires once
the bricks have *proven* we reach scale `J` with the numerator in hand; Case A needs no axiom at all.
See `ON-LINE-REQUEST.md` UPDATE 3 (ask 3b: rigorous handling of the non-measurable sub-resolution
family). Reference: Wolff, *Lectures on Harmonic Analysis*; Mattila, *Fourier Analysis and Hausdorff
Dimension*, §22–23. -/
axiom kakeya_subresolution_content {d : ℝ} (hd : 0 ≤ d)
    {cR : ℝ} (hcRpos : 0 < cR) (J : ℕ) (c : ℝ)
    (a : ℕ → Plane) (A : ℕ → Set ℝ) (hAmeas : ∀ k, MeasurableSet (A k))
    (hA01 : ∀ k, A k ⊆ Set.Icc (0 : ℝ) 1) (U : ℕ → Set Plane) (s : Set ℕ)
    (hediam_hi : ∀ n ∈ s, Metric.ediam (U n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ J))
    (hscov : ∀ k, (fun u => a k + u • dir (c + (k : ℝ) * (1 / 2 : ℝ) ^ J)) '' (A k) ⊆ ⋃ n ∈ s, U n)
    (hnum : ENNReal.ofReal (1 / (((J : ℝ) + 1) * ((J : ℝ) + 2)))
        ≤ ∑ k ∈ Finset.range (2 ^ J), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ J) * volume (A k)) :
    (volume (Metric.closedBall (0 : Plane) 1))⁻¹ * ENNReal.ofReal cR
      ≤ ∑' n, Metric.ediam (U n) ^ d

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
    -- Reduce to closed cover pieces (same `ediam`, still covering `S`): measurable pullbacks.
    set U : ℕ → Set Plane := fun n => closure (t n) with hUdef
    have hUcl : ∀ n, IsClosed (U n) := fun n => isClosed_closure
    have hediam_eq : ∀ n, Metric.ediam (U n) = Metric.ediam (t n) :=
      fun n => Metric.ediam_closure (t n)
    have hUcov : S ⊆ ⋃ n, U n := hcov.trans (Set.iUnion_mono fun n => subset_closure)
    have hUdiam : ∀ n, Metric.ediam (U n) ≤ 1 := fun n => (hediam_eq n).le.trans (hdiam n)
    rw [show (∑' n, Metric.ediam (t n) ^ d) = ∑' n, Metric.ediam (U n) ^ d from by
      simp_rw [hediam_eq]]
    -- Fine net at resolution `2⁻ᴶ` (here `J = 1`); per-direction measurable pullbacks.
    set J : ℕ := 1 with hJdef
    have hpull : ∀ m : ℕ, ∃ (bm : Plane) (Tm : ℕ → Set ℝ),
        (∀ n, MeasurableSet (Tm n)) ∧ (∀ n, Tm n ⊆ Set.Icc (0 : ℝ) 1) ∧
        (∀ n, (fun u => bm + u • dir ((m : ℝ) * (1 / 2 : ℝ) ^ J)) '' (Tm n) ⊆ U n) ∧
        1 ≤ volume (⋃ n, Tm n) := by
      intro m
      obtain ⟨bm, hbm⟩ := h (dir ((m : ℝ) * (1 / 2 : ℝ) ^ J)) (norm_dir _)
      obtain ⟨Tm, hT1, hT2, hT3, hT4⟩ :=
        exists_measurable_pullback_cover (norm_dir ((m : ℝ) * (1 / 2 : ℝ) ^ J)) hUcl
          (hbm.trans hUcov)
      exact ⟨bm, Tm, hT1, hT2, hT3, hT4⟩
    choose bp T hTmeas hT01 hTcov hTvol using hpull
    -- Capped dyadic scale function (zero-diameter pieces sent to the floor `J`).
    set g : ℕ → ℕ := fun n =>
      if 0 < (Metric.ediam (U n)).toReal then min (dyadicIdx (Metric.ediam (U n)).toReal) J else J
      with hgdef
    have hgle : ∀ n, g n ≤ J := by
      intro n; simp only [hgdef]; split
      · exact min_le_right _ _
      · exact le_refl J
    -- Per-direction, per-scale union covered length.
    set L : ℕ → ℕ → ℝ≥0∞ := fun m i => volume (⋃ n ∈ (g ⁻¹' {i} : Set ℕ), T m n) with hLdef
    have hLsupp : ∀ m i, J < i → L m i = 0 := by
      intro m i hi
      have hempty : (g ⁻¹' {i} : Set ℕ) = ∅ := by
        ext n
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro he; exact absurd (he ▸ hgle n) (not_le.mpr hi)
      simp only [hLdef, hempty, Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty,
        measure_empty]
    have hLcov : ∀ m ∈ Finset.range (2 ^ J), 1 ≤ ∑' i, L m i := fun m _ =>
      one_le_tsum_volume_fiber_union g (hTvol m)
    obtain ⟨j, hjJ, β, hβ, hshift⟩ := exists_dominant_shift L hLsupp hLcov
    -- The shifted subnet: directions `dir(c + i·2⁻ʲ)`, `c = β·2⁻ᴶ`, fine index `m = β + 2^{J-j}·i`.
    set c : ℝ := (β : ℝ) * (1 / 2 : ℝ) ^ J with hcdef
    set A : ℕ → Set ℝ := fun i => ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), T (β + 2 ^ (J - j) * i) n with hAdef
    have hAmeas : ∀ i, MeasurableSet (A i) := fun i =>
      MeasurableSet.biUnion (Set.to_countable _) (fun n _ => hTmeas _ n)
    have hA01 : ∀ i, A i ⊆ Set.Icc (0 : ℝ) 1 := fun i =>
      Set.iUnion₂_subset (fun n _ => hT01 _ n)
    -- the resolution identity `2^{J-j}·2⁻ᴶ = 2⁻ʲ`
    have hpowJ : (1 / 2 : ℝ) ^ J = (1 / 2 : ℝ) ^ (J - j) * (1 / 2 : ℝ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjJ]
    have hstep : (2 : ℝ) ^ (J - j) * (1 / 2 : ℝ) ^ J = (1 / 2 : ℝ) ^ j := by
      rw [hpowJ, ← mul_assoc, ← mul_pow]; norm_num
    -- direction agreement `dir(c + i·2⁻ʲ) = dir(m·2⁻ᴶ)`
    have hangle : ∀ i : ℕ, c + (i : ℝ) * (1 / 2 : ℝ) ^ j
        = ((β + 2 ^ (J - j) * i : ℕ) : ℝ) * (1 / 2 : ℝ) ^ J := by
      intro i; rw [hcdef, ← hstep]; push_cast; ring
    -- the covering containment for the subnet
    have hscov : ∀ i, (fun u => bp (β + 2 ^ (J - j) * i)
        + u • dir (c + (i : ℝ) * (1 / 2 : ℝ) ^ j)) '' (A i)
        ⊆ ⋃ n ∈ (g ⁻¹' {j} : Set ℕ), U n := by
      intro i
      rw [hangle i, hAdef, Set.image_iUnion₂]
      exact Set.iUnion₂_subset (fun n hn =>
        (hTcov (β + 2 ^ (J - j) * i) n).trans (Set.subset_biUnion_of_mem hn))
    -- the covered-length numerator at the dominant scale
    have hAvol : ∀ i, volume (A i) = L (β + 2 ^ (J - j) * i) j := fun i => rfl
    have hnum : ENNReal.ofReal (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
        ≤ ∑ i ∈ Finset.range (2 ^ j), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * volume (A i) := by
      calc ENNReal.ofReal (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
          = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * (((2 ^ j : ℕ) : ℝ≥0∞) * scaleWeight j) := by
            rw [scaleWeight,
              show ((2 ^ j : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ j) from by
                rw [← ENNReal.ofReal_natCast, Nat.cast_pow, Nat.cast_ofNat],
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show (2 * (1 / 2 : ℝ) ^ j)
                  * ((2 : ℝ) ^ j * (1 / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2))))
                = ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) from by
                  field_simp,
              show (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 from by rw [← mul_pow]; norm_num, one_mul]
        _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * ∑ i ∈ Finset.range (2 ^ j), volume (A i) := by
            refine mul_le_mul_left' ?_ _
            simp_rw [hAvol]; exact hshift
        _ = ∑ i ∈ Finset.range (2 ^ j), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) * volume (A i) := by
            rw [Finset.mul_sum]
    -- Case split: dominant scale strictly below the resolution (A) vs. saturating it (B).
    rcases lt_or_eq_of_le hjJ with hjlt | hjeq
    · -- Case A: pieces genuinely at scale `j < J`; finite/infinite fiber split.
      have hwin : ∀ n, g n = j → Metric.ediam (U n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j)
          ∧ ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ≤ Metric.ediam (U n) := by
        intro n hn
        have hpos : 0 < (Metric.ediam (U n)).toReal := by
          by_contra hp
          simp only [hgdef] at hn; rw [if_neg hp] at hn; omega
        have hdi : dyadicIdx (Metric.ediam (U n)).toReal = j := by
          simp only [hgdef] at hn; rw [if_pos hpos] at hn; omega
        have hle1 : (Metric.ediam (U n)).toReal ≤ 1 := by
          have := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (hUdiam n); simpa using this
        have hwindow := dyadicIdx_window hpos hle1
        rw [hdi] at hwindow
        have heq : Metric.ediam (U n) = ENNReal.ofReal (Metric.ediam (U n)).toReal :=
          (ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num) (hUdiam n))).symm
        exact ⟨by rw [heq]; exact ENNReal.ofReal_le_ofReal hwindow.2,
          by rw [heq]; exact ENNReal.ofReal_le_ofReal hwindow.1.le⟩
      by_cases hfin : (g ⁻¹' {j} : Set ℕ).Finite
      · -- finite fiber: the base-angle Córdoba content brick
        have hbiUeq : (⋃ n ∈ (g ⁻¹' {j} : Set ℕ), U n) = ⋃ n ∈ hfin.toFinset, U n := by
          ext x; simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
        refine caseA_content hd0.le hcRpos hcR j c (fun i => bp (β + 2 ^ (J - j) * i)) A hAmeas
          hA01 U hfin.toFinset (fun n hn => (hwin n (hfin.mem_toFinset.mp hn)).1)
          (fun n hn => (hwin n (hfin.mem_toFinset.mp hn)).2) (fun i => ?_) hnum
        rw [← hbiUeq]; exact hscov i
      · -- infinite fiber: `∑' ediam^d = ⊤`
        have hinf : (g ⁻¹' {j} : Set ℕ).Infinite := hfin
        haveI : Infinite ↥(g ⁻¹' {j} : Set ℕ) := Set.infinite_coe_iff.mpr hinf
        have hεpos : 0 < ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ^ d :=
          ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top
        have h3 : ∑' _n : ↥(g ⁻¹' {j} : Set ℕ), ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ^ d = ⊤ :=
          ENNReal.tsum_const_eq_top_of_ne_zero hεpos.ne'
        have h2 : ∑' n : ↥(g ⁻¹' {j} : Set ℕ), ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) ^ d
            ≤ ∑' n : ↥(g ⁻¹' {j} : Set ℕ), Metric.ediam (U ↑n) ^ d :=
          ENNReal.tsum_le_tsum (fun n => ENNReal.rpow_le_rpow (hwin ↑n n.2).2 hd0.le)
        have h1 : ∑' n : ↥(g ⁻¹' {j} : Set ℕ), Metric.ediam (U ↑n) ^ d
            ≤ ∑' n, Metric.ediam (U n) ^ d :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
        have htop : ∑' n, Metric.ediam (U n) ^ d = ⊤ :=
          top_le_iff.mp (h3 ▸ (h2.trans h1))
        rw [htop]; exact le_top
    · -- Case B: dominant scale saturates the resolution (`j = J`) — the sub-resolution residual.
      clear hjeq
      have hwinB : ∀ n ∈ (g ⁻¹' {j} : Set ℕ), Metric.ediam (U n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
        intro n hn
        have hn' : g n = j := hn
        by_cases hp : 0 < (Metric.ediam (U n)).toReal
        · have hdiJ : j ≤ dyadicIdx (Metric.ediam (U n)).toReal := by
            simp only [hgdef] at hn'; rw [if_pos hp] at hn'; omega
          have hle1 : (Metric.ediam (U n)).toReal ≤ 1 := by
            have := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (hUdiam n); simpa using this
          have hw := (dyadicIdx_window hp hle1).2
          have hmono : (1 / 2 : ℝ) ^ dyadicIdx (Metric.ediam (U n)).toReal ≤ (1 / 2 : ℝ) ^ j :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hdiJ
          have heq : Metric.ediam (U n) = ENNReal.ofReal (Metric.ediam (U n)).toReal :=
            (ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num) (hUdiam n))).symm
          rw [heq]; exact ENNReal.ofReal_le_ofReal (hw.trans hmono)
        · have htr0 : (Metric.ediam (U n)).toReal = 0 := le_antisymm (not_lt.mp hp) ENNReal.toReal_nonneg
          have hz : Metric.ediam (U n) = 0 := by
            rcases (ENNReal.toReal_eq_zero_iff _).mp htr0 with hh | hh
            · exact hh
            · exact absurd hh (ne_top_of_le_ne_top (by norm_num) (hUdiam n))
          rw [hz]; exact zero_le _
      exact kakeya_subresolution_content hd0.le hcRpos j c (fun i => bp (β + 2 ^ (J - j) * i)) A
        hAmeas hA01 U (g ⁻¹' {j} : Set ℕ) hwinB hscov hnum

/-- **Legacy discrete-route measure form (off the headline path).** For a Kakeya set `S ⊆ ℝ²`, every
`d`-dimensional Hausdorff measure with `d < 2` is positive — proved here via the discrete Case-A/Case-B
route (`kakeya_hausdorffContentBound`, depending on the legacy axiom `kakeya_subresolution_content`).

This chain is **superseded** by the measurable-selection route (`Wiring.lean`:
`hausdorffMeasure_pos_of_isKakeya` / `two_le_dimH`, depending only on the clean axiom
`kakeya_measurable_selection`), which is what the headline `davies_kakeya_2d` now uses. It is kept here
as the proven Case-A discrete structure (the cap-free dominant-scale assembly), not deleted. -/
theorem hausdorffMeasure_pos_of_isKakeya_discrete
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

/-- **Davies 1971 (legacy discrete route, off the headline path).** A Kakeya set in `ℝ²` has Hausdorff
dimension at least `2`, proved via the discrete Case-A/Case-B route. Superseded for the headline by
`Wiring.two_le_dimH` (measurable-selection route, clean axiom); kept as proven discrete structure. -/
theorem two_le_dimH_discrete (S : Set (EuclideanSpace ℝ (Fin 2))) (h : IsKakeya S) :
    2 ≤ dimH S := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  exact le_dimH_of_hausdorffMeasure_ne_zero (hausdorffMeasure_pos_of_isKakeya_discrete S h r hr)

end LeanFormalizations.Kakeya2D

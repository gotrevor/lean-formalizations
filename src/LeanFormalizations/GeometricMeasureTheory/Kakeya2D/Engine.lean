/-
# Davies' theorem — proof engine (planar Kakeya dimension)

The headline `dimH S = 2` splits into the two inequalities:

* `dimH_le_two` — the **trivial** half: any subset of `ℝ²` has Hausdorff dimension `≤ 2`,
  by monotonicity into `univ`, whose dimension is `finrank ℝ (ℝ²) = 2`. **Proven.**
* `two_le_dimH` — **Davies 1971**, the genuine content: a planar Kakeya set has Hausdorff
  dimension `≥ 2`. The SOUND, axiom-clean proof of this is the *elementary / measurable-selection*
  route in `Selection.lean` (`kakeya_hausdorffContentBound_elementary` ⟶ `two_le_dimH`), which the
  headline `davies_kakeya_2d` uses.

  This file (Engine) now holds only the reusable analytic bricks of that route — the trivial upper
  bound `dimH_le_two`, the exponential-beats-polynomial content constant `content_ratio_lower` (with
  its helpers), and a kernel-checked **guard** `kakeya_subresolution_content_is_unsound`.

  ⚠️ **Soundness note (2026-06-19).** Earlier laps papered over the discrete route's "Case B"
  (sub-resolution) gap with an `axiom kakeya_subresolution_content`. That axiom is **FALSE** — it
  omitted the exponential-beats-polynomial link between its constant `cR` and `d` (the `hcR`
  hypothesis that `caseA_content` carries), so its conclusion `D⁻¹·cR ≤ ∑' ediam^d` had to hold for
  *arbitrary* `cR > 0` against a *fixed finite* `∑' ediam^d`. The false axiom was REMOVED; the
  kernel-checked refutation `kakeya_subresolution_content_is_unsound` below is kept as a guard so it
  cannot return. The legacy discrete assembly that carried the corresponding disclosed `sorry` has
  itself been **deleted** (it was fully superseded by `Selection.lean`); see the removal note at the
  end of this file.

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

/-- **The discrete-route Case-B "sub-resolution content" statement is UNSOUND (FALSE).**

Earlier laps cited the universally-quantified statement below as `axiom kakeya_subresolution_content`,
believing it a "true but deep" Hausdorff-vs-box-counting residual. It is in fact **false**, for two
independent reasons:

1. **It dropped the `hcR` hypothesis.** The sound single-scale brick `caseA_content` links its
   constant `cR` to the exponent `d` via the exponential-beats-polynomial inequality `hcR`. The
   abstract statement here omits it (only `0 < cR`), so its conclusion `D⁻¹·cR ≤ ∑' ediam^d` had to
   hold for *every* `cR > 0` against a *fixed* configuration with *finite* `∑' ediam^d` — impossible.
   The refutation below exploits exactly this: it fixes a one-piece cover of a single unit segment
   (so `∑' ediam^d` is finite, ≤ 1) and picks `cR = vol(disc).toReal + 1`, forcing
   `D⁻¹·cR > 1 ≥ ∑' ediam^d`.

2. **Even with `hcR` restored it is false for `d > 1`.** The hypotheses fix only `2ᴶ` *directions*
   but leave the base points `a k` arbitrary, so the `2ᴶ` segments may be placed pairwise far apart;
   covering them by *unshared* pieces of size `2⁻ⁱ` (`i ≥ J`) uses `≈ 2^{J+i}` pieces with
   `∑ ediam^d ≈ 2^{J+i(1-d)} → 0`. The Córdoba overlap that makes the real theorem work needs the
   segments forced into a common bounded set (a Kakeya set) — structure the abstract statement drops.

This is why the discrete route genuinely cannot close Case B, and why the SOUND headline proof routes
through the *measurable-selection / elementary open-cover* argument (`Selection.lean`) instead. The
former false axiom has been removed; this kernel-checked refutation is kept as a permanent guard so the
unsound statement is never reintroduced. Headline is unaffected:
`#print axioms davies_kakeya_2d = [propext, Classical.choice, Quot.sound]`. -/
theorem kakeya_subresolution_content_is_unsound :
    ¬ (∀ (d : ℝ), 0 ≤ d → ∀ (cR : ℝ), 0 < cR → ∀ (J : ℕ) (c : ℝ)
        (a : ℕ → Plane) (A : ℕ → Set ℝ), (∀ k, MeasurableSet (A k)) →
        (∀ k, A k ⊆ Set.Icc (0 : ℝ) 1) → ∀ (U : ℕ → Set Plane) (s : Set ℕ),
        (∀ n ∈ s, Metric.ediam (U n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ J)) →
        (∀ k, (fun u => a k + u • dir (c + (k : ℝ) * (1 / 2 : ℝ) ^ J)) '' (A k) ⊆ ⋃ n ∈ s, U n) →
        (ENNReal.ofReal (1 / (((J : ℝ) + 1) * ((J : ℝ) + 2)))
          ≤ ∑ k ∈ Finset.range (2 ^ J), ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ J) * volume (A k)) →
        (volume (Metric.closedBall (0 : Plane) 1))⁻¹ * ENNReal.ofReal cR
          ≤ ∑' n, Metric.ediam (U n) ^ d) := by
  intro H
  set D : ℝ≥0∞ := volume (Metric.closedBall (0 : Plane) 1) with hD
  have hDpos : 0 < D := volume_closedBall_one_pos
  have hDtop : D ≠ ⊤ := volume_closedBall_one_ne_top
  set SEG : Set Plane := (fun u => (0 : Plane) + u • dir 0) '' (Set.Icc (0 : ℝ) 1) with hSEG
  classical
  set U : ℕ → Set Plane := fun n => if n = 0 then SEG else ∅ with hUdef
  set A : ℕ → Set ℝ := fun k => if k = 0 then Set.Icc (0 : ℝ) 1 else ∅ with hAdef
  have hU0 : U 0 = SEG := by rw [hUdef]; simp
  have hUk : ∀ n, n ≠ 0 → U n = ∅ := fun n hn => by rw [hUdef]; simp [hn]
  have hA0 : A 0 = Set.Icc (0 : ℝ) 1 := by rw [hAdef]; simp
  have hAk : ∀ k, k ≠ 0 → A k = ∅ := fun k hk => by rw [hAdef]; simp [hk]
  set cR : ℝ := D.toReal + 1 with hcRdef
  have hcRpos : 0 < cR := by have := ENNReal.toReal_nonneg (a := D); rw [hcRdef]; linarith
  have hediam_seg : Metric.ediam SEG ≤ 1 := by
    apply Metric.ediam_le
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    rw [Set.mem_Icc] at hs ht
    show edist ((0 : Plane) + s • dir 0) ((0 : Plane) + t • dir 0) ≤ 1
    rw [edist_dist]
    refine (ENNReal.ofReal_le_ofReal ?_).trans_eq ENNReal.ofReal_one
    rw [zero_add, zero_add, dist_eq_norm, ← sub_smul, norm_smul, norm_dir, mul_one,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hmeas : ∀ k, MeasurableSet (A k) := fun k => by
    by_cases hk : k = 0
    · rw [hk, hA0]; exact measurableSet_Icc
    · rw [hAk k hk]; exact MeasurableSet.empty
  have h01 : ∀ k, A k ⊆ Set.Icc (0 : ℝ) 1 := fun k => by
    by_cases hk : k = 0
    · rw [hk, hA0]
    · rw [hAk k hk]; exact Set.empty_subset _
  have hax := H 1 (le_of_lt one_pos) cR hcRpos 0 0 (fun _ => (0 : Plane)) A hmeas h01 U {0}
    (fun n hn => by
      simp only [Set.mem_singleton_iff] at hn; subst hn
      rw [hU0]; simpa using hediam_seg)
    (fun k => by
      by_cases hk : k = 0
      · subst hk
        rw [hA0]
        intro y hy
        rw [Set.mem_iUnion₂]
        refine ⟨0, rfl, ?_⟩
        rw [hU0, hSEG]
        obtain ⟨u, hu, rfl⟩ := hy
        exact ⟨u, hu, by norm_num⟩
      · rw [hAk k hk]; simp)
    (by
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton, hA0]
      rw [Real.volume_Icc]
      norm_num)
  have htsum : (∑' n, Metric.ediam (U n) ^ (1 : ℝ)) ≤ 1 := by
    rw [tsum_eq_single 0]
    · rw [hU0, ENNReal.rpow_one]; exact hediam_seg
    · intro n hn
      rw [hUk n hn]; simp [Metric.ediam]
  have hfin : D⁻¹ * ENNReal.ofReal cR ≤ 1 := hax.trans htsum
  have hle : ENNReal.ofReal cR ≤ D := by
    have h2 := mul_le_mul_left' hfin D
    rwa [← mul_assoc, ENNReal.mul_inv_cancel hDpos.ne' hDtop, one_mul, mul_one] at h2
  have hgt : D < ENNReal.ofReal cR := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hDtop]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr (by rw [hcRdef]; linarith)
  exact absurd hgt (not_lt.mpr hle)

/-! ### Legacy discrete route — removed (2026-06-19)

The legacy *discrete* Córdoba assembly (`kakeya_hausdorffContentBound` and its measure/dimension
wrappers `hausdorffMeasure_pos_of_isKakeya_discrete`, `two_le_dimH_discrete`) has been **deleted**.
Its Case-B branch was an unclosable disclosed `sorry`: the discrete finite-net route provably cannot
close the sub-resolution case (the abstract statement it would need is
`kakeya_subresolution_content`, which is **FALSE** — see the kernel-checked refutation
`kakeya_subresolution_content_is_unsound` above, kept as a guard so the false axiom cannot return).
The whole discrete route is fully **superseded** by the SOUND, axiom-clean elementary / open-cover
measurable-selection route in `Selection.lean` (`kakeya_hausdorffContentBound_elementary` ⟶
`two_le_dimH` ⟶ the headline `davies_kakeya_2d`). The reusable analytic bricks of this file
(`content_ratio_lower`, `exists_pos_le_pow_div`, …) remain in use by that route. -/

end LeanFormalizations.Kakeya2D

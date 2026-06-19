/-
# Davies' theorem — proof engine (planar Kakeya dimension)

The headline `dimH S = 2` splits into the two inequalities:

* `dimH_le_two` — the **trivial** half: any subset of `ℝ²` has Hausdorff dimension `≤ 2`,
  by monotonicity into `univ`, whose dimension is `finrank ℝ (ℝ²) = 2`. **Proven.**
* `two_le_dimH` — **Davies 1971**, the genuine content: a planar Kakeya set has Hausdorff
  dimension `≥ 2`. This is the run's open crux (`sorry`). Strategy: Córdoba's dual / "bush"
  `L²` argument — see `PLAN.md`.

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

/-- **The deep crux (Davies 1971, Hausdorff content form), as one named obligation.** For a planar
Kakeya set `S` and every exponent `0 < d < 2`, the `d`-dimensional **Hausdorff content** of `S` is
bounded below: there is a scale `r > 0` and a constant `c > 0` such that every fine countable cover
of `S` has `∑ₙ ediam(tₙ)^d ≥ c`.

This is the genuine remaining content of the planar Kakeya theorem and the lone `sorry` of the run.
The proof (multi-lap) is Córdoba's argument run on an arbitrary cover: a dyadic pigeonhole reduces
the cover to a dominant scale `δ`, where the K4 single-scale tube count `volume_thickening_log_ge`
(`vol(Sδ) ≳ 1/log(1/δ)`) forces enough cover pieces that `∑ ediam^d ≳ δ^{d-2}/log ≥ c`. The reduction
machinery (`Cover.lean`) turns this content bound into `μH[d] S ≠ 0`. See `PLAN.md` / `PENDING_WORK.md`. -/
theorem kakeya_hausdorffContentBound
    {S : Set (EuclideanSpace ℝ (Fin 2))} (h : IsKakeya S) {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2) :
    HausdorffContentBound S d := by
  -- **The remaining deep obligation (K5 core):** the multi-scale Córdoba cover-content estimate.
  sorry

/-- **The concrete crux (Davies 1971, measure form).** For a Kakeya set `S ⊆ ℝ²`, every
`d`-dimensional Hausdorff measure with `d < 2` is *positive*: `μH[d] S ≠ 0`.

This is the genuine analytic content; `two_le_dimH` is a free `ℝ≥0∞`-density wrapper around it.
The route to discharge it is the Córdoba `L²`/bush argument (`PLAN.md`, ladder K2–K5):
δ-tube overlap bound ⟹ Minkowski-content lower bound `vol(Sδ) ≳ 1/log(1/δ)` ⟹ a Hausdorff content
lower bound witnessing `μH[d] S > 0` for every `d < 2`.

**Status (this run).** K2–K4 are **proven, axiom-clean**: the content bound `vol(Sδ) ≳ 1/log(1/δ)`
is `volume_thickening_log_ge`. K5's measure-free reduction (`Cover.lean`,
`hausdorffMeasure_ne_zero_of_contentBound`) turns the crux into the **Hausdorff content bound**
`kakeya_hausdorffContentBound` — the lone remaining `sorry`. The `d = 0` endpoint is free from
monotonicity of `μH` in `d` against the `d = 1` content bound. -/
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
